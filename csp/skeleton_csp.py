"""
CSP Proof Solver
================
Encodes propositional proof search as a bounded CSP:
  - each proof step is a variable
  - each variable's domain is the candidate formula set
  - local rule checks (MP, and-intro, and-elim) are the constraints
  - max_steps bounds the depth

This solver is a pure CSP — Bayesian scoring lives in bayes/solver.py.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Optional

from parser.ast import Formula, Atom, And, Imp, Not


RULES = (
    "modus_ponens",
    "and_intro",
    "and_elim_left",
    "and_elim_right",
)


@dataclass(frozen=True)
class CSPStep:
    """
    One proof step in the CSP model.

      formula  : the formula derived at this step
      rule     : inference rule applied
      support1 : first premise
      support2 : second premise (None for single-premise rules)
    """
    formula:  Formula
    rule:     str
    support1: Optional[Formula] = None
    support2: Optional[Formula] = None


@dataclass
class CSPStats:
    nodes_expanded:      int = 0
    candidates_generated: int = 0
    candidates_considered: int = 0


def formula_complexity(formula: Formula) -> int:
    """Structural complexity — used as a sort key, not a semantic measure."""
    if isinstance(formula, Atom):
        return 1
    if isinstance(formula, Not):
        return 1 + formula_complexity(formula.child)
    if isinstance(formula, And):
        return 1 + formula_complexity(formula.left) + formula_complexity(formula.right)
    if isinstance(formula, Imp):
        return 1 + formula_complexity(formula.left) + formula_complexity(formula.right)
    return 1


def collect_formulas(formula: Formula, out: set[Formula]) -> None:
    """Recursively collect a formula and all of its syntactic subformulas."""
    if formula in out:
        return
    out.add(formula)
    if isinstance(formula, (And, Imp)):
        collect_formulas(formula.left, out)
        collect_formulas(formula.right, out)
    elif isinstance(formula, Not):
        collect_formulas(formula.child, out)


def candidate_formula_domain(
    assumptions: list[Formula],
    goal: Formula,
) -> list[Formula]:
    """
    Build the finite formula domain: all subformulas of assumptions + goal,
    sorted by structural complexity (simpler first).
    """
    formulas: set[Formula] = set()
    for assumption in assumptions:
        collect_formulas(assumption, formulas)
    collect_formulas(goal, formulas)

    return sorted(formulas, key=lambda f: (formula_complexity(f), str(f)))


def available_formulas(
    assumptions: list[Formula], steps: list[CSPStep]
) -> list[Formula]:
    """Return assumptions plus every formula derived so far, in order."""
    seen: list[Formula] = []
    for formula in assumptions:
        if formula not in seen:
            seen.append(formula)
    for step in steps:
        if step.formula not in seen:
            seen.append(step.formula)
    return seen


def can_apply_modus_ponens(
    result: Formula, support1: Formula, support2: Formula
) -> bool:
    if isinstance(support1, Imp) and support1.left == support2 and support1.right == result:
        return True
    if isinstance(support2, Imp) and support2.left == support1 and support2.right == result:
        return True
    return False


def can_apply_and_intro(
    result: Formula, support1: Formula, support2: Formula
) -> bool:
    if not isinstance(result, And):
        return False
    return result.left == support1 and result.right == support2


def can_apply_and_elim_left(result: Formula, support1: Formula) -> bool:
    return isinstance(support1, And) and support1.left == result


def can_apply_and_elim_right(result: Formula, support1: Formula) -> bool:
    return isinstance(support1, And) and support1.right == result


def step_is_locally_valid(
    step: CSPStep,
    assumptions: list[Formula],
    prior_steps: list[CSPStep],
) -> bool:
    available = available_formulas(assumptions, prior_steps)

    if step.formula in available:
        return False

    if step.rule == "modus_ponens":
        if step.support1 is None or step.support2 is None:
            return False
        if step.support1 not in available or step.support2 not in available:
            return False
        return can_apply_modus_ponens(step.formula, step.support1, step.support2)

    if step.rule == "and_intro":
        if step.support1 is None or step.support2 is None:
            return False
        if step.support1 not in available or step.support2 not in available:
            return False
        return can_apply_and_intro(step.formula, step.support1, step.support2)

    if step.rule == "and_elim_left":
        if step.support1 is None:
            return False
        if step.support1 not in available:
            return False
        return can_apply_and_elim_left(step.formula, step.support1)

    if step.rule == "and_elim_right":
        if step.support1 is None:
            return False
        if step.support1 not in available:
            return False
        return can_apply_and_elim_right(step.formula, step.support1)

    return False


def generate_candidate_steps(
    assumptions: list[Formula],
    goal: Formula,
    prior_steps: list[CSPStep],
    formula_domain: list[Formula],
    *,
    stats: Optional[CSPStats] = None,
) -> list[CSPStep]:
    """Generate all locally-valid next proof steps, sorted goal-first then by complexity."""
    available = available_formulas(assumptions, prior_steps)
    candidates: list[CSPStep] = []

    two_support_rules = ["modus_ponens", "and_intro"]
    one_support_rules = ["and_elim_left", "and_elim_right"]

    for result in formula_domain:
        for support1 in available:
            for support2 in available:
                for rule in two_support_rules:
                    step = CSPStep(formula=result, rule=rule,
                                   support1=support1, support2=support2)
                    if step_is_locally_valid(step, assumptions, prior_steps):
                        candidates.append(step)

    for result in formula_domain:
        for support1 in available:
            for rule in one_support_rules:
                step = CSPStep(formula=result, rule=rule, support1=support1)
                if step_is_locally_valid(step, assumptions, prior_steps):
                    candidates.append(step)

    candidates.sort(
        key=lambda s: (
            s.formula != goal,
            formula_complexity(s.formula),
            str(s.formula),
            s.rule,
        )
    )

    # Dedup while preserving order.
    unique: list[CSPStep] = []
    seen: set[CSPStep] = set()
    for step in candidates:
        if step not in seen:
            seen.add(step)
            unique.append(step)

    if stats is not None:
        stats.candidates_generated += len(unique)

    return unique


def solve_bounded_csp(
    assumptions: list[Formula],
    goal: Formula,
    max_steps: int = 4,
    *,
    stats: Optional[CSPStats] = None,
) -> Optional[list[CSPStep]]:
    """
    Solve a proof task by bounded backtracking CSP search.

    Returns a list of CSPStep objects on success, or None if no proof
    is found within `max_steps` derived steps.
    """
    if goal in assumptions:
        return []

    formula_domain = candidate_formula_domain(assumptions, goal)

    def backtrack(partial_steps: list[CSPStep]) -> Optional[list[CSPStep]]:
        if stats is not None:
            stats.nodes_expanded += 1

        current_available = available_formulas(assumptions, partial_steps)

        if goal in current_available:
            return partial_steps

        if len(partial_steps) >= max_steps:
            return None

        candidates = generate_candidate_steps(
            assumptions=assumptions,
            goal=goal,
            prior_steps=partial_steps,
            formula_domain=formula_domain,
            stats=stats,
        )

        for candidate in candidates:
            if candidate.formula in current_available:
                continue
            if stats is not None:
                stats.candidates_considered += 1

            result = backtrack(partial_steps + [candidate])
            if result is not None:
                return result

        return None

    return backtrack([])
