"""
Bayesian Proof Solver
=====================
A complete standalone propositional + first-order logic prover.

The solver uses Naive Bayes to score candidate inference steps and drives
an A*-style best-first search over proof states.  It is entirely independent
of the CSP solver — it does its own candidate generation, its own search
loop, and returns its own proof-step objects.

Supported inference rules
-------------------------
  Propositional
    modus_ponens   : A, (A -> B)   ⊢  B
    and_elim_left  : (A & B)       ⊢  A
    and_elim_right : (A & B)       ⊢  B
    and_intro      : A, B          ⊢  (A & B)

  First-order (quantifier rules)
    universal_instantiation : (∀x.φ(x)), term t  ⊢  φ(t)
    existential_intro        : φ(t)               ⊢  (∃x.φ(x))

Search strategy
---------------
State    = frozenset of formulas currently known.
Priority = cumulative Σ log P(success | step_features) along the path,
           maximised via a min-heap over negated scores (best-first).

Automatic And-elimination is applied whenever the known set grows, so the
solver never needs explicit and_elim_left / and_elim_right steps for facts
that can be derived immediately from the initial knowledge.
"""

from __future__ import annotations

import heapq
import math
from dataclasses import dataclass
from itertools import count
from typing import Optional

from parser.ast import Formula, Atom, And, Imp, Not, Predicate, ForAll, Exists
from logic.matcher import expand_context
from logic.substitution import substitute, collect_terms
from bayes.features import extract_step_features
from bayes.scorer import default_step_scorer

_STEP_SCORER = default_step_scorer()


# ──────────────────────────────────────────────────────────────────────────────
# Public data structures
# ──────────────────────────────────────────────────────────────────────────────

@dataclass
class BayesProofStep:
    """
    One step in a Bayesian proof.

    Attributes
    ----------
    formula   : formula derived at this step
    rule      : inference rule applied
    support1  : first premise (or the ForAll formula for UI)
    support2  : second premise, or the term string wrapped in Atom for UI,
                or None for single-premise rules
    score     : P(success | features) for this individual step
    """
    formula:  Formula
    rule:     str
    support1: Optional[Formula] = None
    support2: Optional[Formula] = None
    score:    float = 0.0

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, BayesProofStep):
            return NotImplemented
        return (self.formula  == other.formula  and
                self.rule     == other.rule     and
                self.support1 == other.support1 and
                self.support2 == other.support2)

    def __hash__(self) -> int:
        return hash((self.formula, self.rule, self.support1, self.support2))


@dataclass
class BayesSolverStats:
    """
    Diagnostic counters emitted by solve_bayes.

      nodes_expanded    : proof states popped from the priority queue
      candidates_scored : (step, state) pairs evaluated by the scorer
      steps_in_proof    : length of the final proof (0 = trivially known)
    """
    nodes_expanded:    int = 0
    candidates_scored: int = 0
    steps_in_proof:    int = 0


# ──────────────────────────────────────────────────────────────────────────────
# Internal helpers
# ──────────────────────────────────────────────────────────────────────────────

def _collect_subformulas(formula: Formula, out: set[Formula]) -> None:
    """Recursively collect formula and all its syntactic subformulas."""
    if formula in out:
        return
    out.add(formula)
    if isinstance(formula, (And, Imp)):
        _collect_subformulas(formula.left, out)
        _collect_subformulas(formula.right, out)
    elif isinstance(formula, Not):
        _collect_subformulas(formula.child, out)
    elif isinstance(formula, (ForAll, Exists)):
        _collect_subformulas(formula.body, out)
    # Atom, Predicate are leaves


def _formula_sort_key(f: Formula) -> tuple[int, str]:
    if isinstance(f, Atom):      return (0, str(f))
    if isinstance(f, Predicate): return (1, str(f))
    if isinstance(f, Not):       return (2, str(f))
    if isinstance(f, And):       return (3, str(f))
    if isinstance(f, Imp):       return (4, str(f))
    if isinstance(f, (ForAll, Exists)): return (5, str(f))
    return (6, str(f))


def _gather_available_terms(formulas: set[Formula]) -> set[str]:
    """
    Collect all names that can serve as concrete instantiation terms for UI.
    """
    terms: set[str] = set()
    for f in formulas:
        collect_terms(f, terms)
    if not terms:
        terms.add("a")  # default Skolem constant when no terms exist
    return terms


def _build_formula_domain(
    assumptions: list[Formula], goal: Formula
) -> list[Formula]:
    """
    Build the finite universe of formulas the solver may derive.

    Contains:
    1. All syntactic subformulas of assumptions and goal.
    2. All universal-instantiation results reachable from ForAll formulas
       in the assumptions, using the terms that appear in the problem.
    """
    base: set[Formula] = set()
    for a in assumptions:
        _collect_subformulas(a, base)
    _collect_subformulas(goal, base)

    terms = _gather_available_terms(base)

    # Add UI instantiations and their subformulas.
    additions: set[Formula] = set()
    for f in list(base):
        if isinstance(f, ForAll):
            for t in terms:
                instance = substitute(f.body, f.var, t)
                _collect_subformulas(instance, additions)

    base |= additions
    return sorted(base, key=_formula_sort_key)


def _score_step(
    step: BayesProofStep,
    *,
    goal: Formula,
    known: frozenset[Formula],
    depth: int,
) -> float:
    """Score a candidate step using the Naive Bayes step model."""
    features = extract_step_features(
        step,
        goal=goal,
        available_count=len(known),
        depth=depth,
        available=list(known),
    )
    return _STEP_SCORER.score(features, positive_label="success")


def _generate_candidates(
    known: frozenset[Formula],
    formula_domain: list[Formula],
    available_terms: set[str],
    goal: Formula,
    depth: int,
) -> list[BayesProofStep]:
    """
    Generate every valid inference step given the current knowledge.

    A step is valid when all its premises are in `known`, its conclusion
    is not already known, and it satisfies its rule's structural constraint.
    """
    candidates: list[BayesProofStep] = []

    for result in formula_domain:
        if result in known:
            continue

        # ── modus_ponens ─────────────────────────────────────────────────
        # Find every (A -> result) where A is also known.
        for f in known:
            if isinstance(f, Imp) and f.right == result and f.left in known:
                step = BayesProofStep(
                    formula=result,
                    rule="modus_ponens",
                    support1=f,       # the implication
                    support2=f.left,  # the antecedent
                )
                step.score = _score_step(step, goal=goal, known=known, depth=depth)
                candidates.append(step)

        # ── and_elim_left ────────────────────────────────────────────────
        for f in known:
            if isinstance(f, And) and f.left == result:
                step = BayesProofStep(
                    formula=result, rule="and_elim_left",
                    support1=f, support2=None,
                )
                step.score = _score_step(step, goal=goal, known=known, depth=depth)
                candidates.append(step)
                break

        # ── and_elim_right ───────────────────────────────────────────────
        for f in known:
            if isinstance(f, And) and f.right == result:
                step = BayesProofStep(
                    formula=result, rule="and_elim_right",
                    support1=f, support2=None,
                )
                step.score = _score_step(step, goal=goal, known=known, depth=depth)
                candidates.append(step)
                break

        # ── and_intro ────────────────────────────────────────────────────
        if isinstance(result, And):
            if result.left in known and result.right in known:
                step = BayesProofStep(
                    formula=result, rule="and_intro",
                    support1=result.left, support2=result.right,
                )
                step.score = _score_step(step, goal=goal, known=known, depth=depth)
                candidates.append(step)

    # ── universal_instantiation ──────────────────────────────────────────
    # For every ∀x.φ(x) in known and every available term t, derive φ(t).
    for f in known:
        if isinstance(f, ForAll):
            for t in available_terms:
                instance = substitute(f.body, f.var, t)
                if instance in known:
                    continue
                if instance not in set(formula_domain):
                    continue  # outside the bounded domain
                step = BayesProofStep(
                    formula=instance,
                    rule="universal_instantiation",
                    support1=f,         # the universal formula
                    support2=Atom(t),   # the term used (wrapped as Atom for display)
                )
                step.score = _score_step(step, goal=goal, known=known, depth=depth)
                candidates.append(step)

    # ── existential_intro ────────────────────────────────────────────────
    # For every ∃x.φ(x) in the domain and a witness t such that φ(t) is
    # already known, derive ∃x.φ(x).
    for result in formula_domain:
        if result in known:
            continue
        if not isinstance(result, Exists):
            continue
        # Find a witness: some term t such that substitute(body, var, t) ∈ known.
        for t in available_terms:
            witness_formula = substitute(result.body, result.var, t)
            if witness_formula in known:
                step = BayesProofStep(
                    formula=result,
                    rule="existential_intro",
                    support1=witness_formula,  # the witness instance
                    support2=None,
                )
                step.score = _score_step(step, goal=goal, known=known, depth=depth)
                candidates.append(step)
                break  # one witness is enough

    return candidates


# ──────────────────────────────────────────────────────────────────────────────
# Main solver
# ──────────────────────────────────────────────────────────────────────────────

def solve_bayes(
    assumptions: list[Formula],
    goal:        Formula,
    max_steps:   int = 10,
    *,
    stats: Optional[BayesSolverStats] = None,
) -> Optional[list[BayesProofStep]]:
    """
    Find a proof of `goal` from `assumptions` using Bayesian best-first search.

    Parameters
    ----------
    assumptions : known premises
    goal        : formula to prove
    max_steps   : maximum number of derived inference steps allowed
    stats       : optional stats collector, mutated in-place

    Returns
    -------
    list[BayesProofStep] on success (empty list = goal follows directly),
    or None if no proof is found within `max_steps`.
    """
    if stats is None:
        stats = BayesSolverStats()

    # Seed knowledge with And-elimination pre-applied.
    initial_known: frozenset[Formula] = frozenset(
        expand_context(set(assumptions))
    )

    if goal in initial_known:
        stats.steps_in_proof = 0
        return []

    formula_domain   = _build_formula_domain(assumptions, goal)
    available_terms  = _gather_available_terms(set(formula_domain))

    # ── Priority queue ────────────────────────────────────────────────────
    # Entry: (neg_cumulative_log_prob, tie_break_seq, known, steps)
    _seq = count()
    heap: list[tuple[float, int, frozenset[Formula], tuple[BayesProofStep, ...]]] = []
    heapq.heappush(heap, (0.0, next(_seq), initial_known, ()))

    # best_score[known] — prunes dominated paths.
    best_score: dict[frozenset[Formula], float] = {initial_known: 0.0}

    while heap:
        neg_score, _, known, steps = heapq.heappop(heap)
        cumulative = -neg_score

        stats.nodes_expanded += 1

        if goal in known:
            stats.steps_in_proof = len(steps)
            return list(steps)

        if len(steps) >= max_steps:
            continue

        candidates = _generate_candidates(
            known, formula_domain, available_terms, goal, len(steps)
        )
        stats.candidates_scored += len(candidates)

        for step in candidates:
            if step.formula in known:
                continue

            new_known = frozenset(
                expand_context(set(known) | {step.formula})
            )
            new_log_prob = cumulative + math.log(max(step.score, 1e-12))

            prev = best_score.get(new_known, float("-inf"))
            if new_log_prob <= prev:
                continue

            best_score[new_known] = new_log_prob
            heapq.heappush(
                heap,
                (-new_log_prob, next(_seq), new_known, steps + (step,)),
            )

    return None


# ──────────────────────────────────────────────────────────────────────────────
# Pretty printer
# ──────────────────────────────────────────────────────────────────────────────

def print_bayes_proof(
    steps: list[BayesProofStep],
    assumptions: list[Formula],
    goal: Formula,
) -> None:
    """Print a Bayesian proof in a readable format."""
    print(f"  Assumptions : {[str(a) for a in assumptions]}")
    print(f"  Goal        : {goal}")
    print()
    if not steps:
        print("  (goal follows immediately from assumptions — 0 derived steps)")
        return
    for i, step in enumerate(steps):
        sups = []
        if step.support1 is not None:
            sups.append(str(step.support1))
        if step.support2 is not None:
            sups.append(str(step.support2))
        print(
            f"  Step {i + 1}: {step.formula}"
            f"  by  {step.rule}"
            f"  (supports: {', '.join(sups) or '—'})"
            f"  [p={step.score:.3f}]"
        )
