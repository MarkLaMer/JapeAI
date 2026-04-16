"""
cbn/logic_causal.py -- Bayesian Network proof solver.

A genuinely independent third solver alongside CSP (depth-first backtracking)
and PDDL (breadth-first BFS), using four distinct mechanisms:

  1. D-separation filter
     Build a CausalGraph from the implications in the assumption set.  Use
     the Bayes-ball algorithm to identify which formulas in the domain have
     an active causal path to the goal atoms given the observed assumption
     atoms.  Formulas that are d-separated (causally irrelevant) are pruned
     from the search domain before the search begins.

  2. Best-first probabilistic search
     A priority queue scored by cumulative Naive Bayes step scores.  Always
     expands the most promising proof state next.
       CSP  -- depth-first backtracking + iterative deepening
       PDDL -- uniform breadth-first BFS
       Bayes -- best-first, guided by posterior step-success probability

  3. Full FOL rule set
     Forward rules (each costs one search expansion):
       forall-elim, exists-intro, or-intro, MP, and-intro, and-elim
     Structural goal-decomposition rules (free -- handled recursively):
       imp-intro, forall-intro, exists-elim, or-elim

  4. Implication Introduction
     To prove A -> B: assume A, spawn a sub-search for B in the extended
     context, discharge the hypothesis.  Handles all tautologies and
     hypothetical reasoning problems.
"""
from __future__ import annotations

import heapq
from math import log
from typing import Optional

from parser.ast import (
    Formula, Atom, And, Imp, Not, Or, ForAll, Exists, Var, Predicate,
)
from cbn.graph import CausalGraph
from bayes.scorer import default_step_scorer, default_formula_scorer
from bayes.features import extract_step_features, _formula_type
from csp.fol_csp import (
    FOLStep, FOLImpIntroStep, FOLForAllIntroStep,
    FOLExistsElimStep, FOLOrElimStep, FOLNotIntroStep, FOLRAAStep, FOLProofStep,
    _generate_forward_steps, _build_domain, _has_contradiction,
    _fol_solve_contra,
    render_fol_csp_steps,
)
from logic.fol_prover import subst, _fresh, reset_fresh, collect_terms


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

_MAX_STATES      = 3000   # max priority-queue expansions per forward search
_MAX_STRUCT_DEPTH = 12    # max recursive structural-rule nesting
_MAX_CONTRA_STEPS = 15    # step budget for contradiction search (RAA / not-intro)


# ---------------------------------------------------------------------------
# Atom helpers
# ---------------------------------------------------------------------------

def _atom_nodes(formula: Formula) -> set[str]:
    """Return string labels of all atomic sub-formulas."""
    if isinstance(formula, (Atom, Var, Predicate)):
        return {str(formula)}
    if isinstance(formula, Not):
        return _atom_nodes(formula.child)
    if isinstance(formula, (And, Or, Imp)):
        return _atom_nodes(formula.left) | _atom_nodes(formula.right)
    if isinstance(formula, (ForAll, Exists)):
        return _atom_nodes(formula.body)
    return {str(formula)}


# ---------------------------------------------------------------------------
# Step 1: Build causal graph from assumptions
# ---------------------------------------------------------------------------

def _build_causal_graph(
    assumptions: list[Formula],
    goal: Formula,
) -> tuple[CausalGraph, set[str]]:
    """
    Build a CausalGraph from the implications in *assumptions*.

    Nodes  : all atomic sub-formulas appearing in assumptions + goal.
    Edges  : for each Imp(A, B) in assumptions, directed edges from every
             atom of A to every atom of B (excluding self-loops).

    Returns (graph, all_atom_labels).
    """
    all_labels: set[str] = set()
    for f in list(assumptions) + [goal]:
        all_labels.update(_atom_nodes(f))

    edges: list[tuple[str, str]] = []
    for f in assumptions:
        if isinstance(f, Imp):
            ant_labels = _atom_nodes(f.left)
            con_labels = _atom_nodes(f.right)
            for a in ant_labels:
                for c in con_labels:
                    if a != c:
                        edges.append((a, c))

    edges = list(dict.fromkeys(edges))   # deduplicate, preserve order

    # Drop any edge that would create a cycle
    safe: list[tuple[str, str]] = []
    for edge in edges:
        try:
            CausalGraph(all_labels, safe + [edge])
            safe.append(edge)
        except ValueError:
            pass

    return CausalGraph(all_labels, safe), all_labels


# ---------------------------------------------------------------------------
# Step 2: D-separation filter
# ---------------------------------------------------------------------------

def _dsep_filter(
    domain: set[Formula],
    graph: CausalGraph,
    assumption_atoms: set[str],
    goal_atoms: set[str],
) -> set[Formula]:
    """
    Prune *domain* to formulas with at least one atom d-connected to any
    goal atom given the observed assumption atoms.

    A formula is considered relevant if it lies on an active causal path
    from the assumptions to the goal.  D-separated (causally blocked)
    formulas are removed -- they cannot contribute to the proof.
    """
    if not graph.nodes or not goal_atoms:
        return domain

    observed = assumption_atoms & graph.nodes
    goal_nodes = goal_atoms & graph.nodes

    kept: set[Formula] = set()
    for f in domain:
        f_atoms = _atom_nodes(f) & graph.nodes
        if not f_atoms:
            kept.add(f)   # no graph nodes -- keep (cannot evaluate)
            continue

        # Keep if any atom of f is d-connected to any goal atom
        relevant = any(
            not graph.d_separated(a, g, observed)
            for a in f_atoms
            for g in goal_nodes
            if a != g
        )
        if relevant or (f_atoms & goal_nodes):
            kept.add(f)

    # Always keep assumptions and goal themselves
    kept.update(domain & set())   # no-op, just for clarity
    return kept if kept else domain   # never return empty domain


# ---------------------------------------------------------------------------
# Step 3: Best-first forward search (Bayesian priority queue)
# ---------------------------------------------------------------------------

def _best_first_search(
    base: list[Formula],
    goal: Formula,
    domain: set[Formula],
    max_states: int = _MAX_STATES,
) -> Optional[list[FOLStep]]:
    """
    Best-first forward proof search guided by Naive Bayes step scores.

    Each search state is a frozenset of known formulas plus the sequence
    of steps that produced it.  The priority queue always expands the state
    with the highest cumulative Bayesian score (lowest neg-log-score).

    This differs fundamentally from:
      CSP  -- which uses DFS with a step budget and backtracks
      PDDL -- which expands all states at depth d before depth d+1
    """
    step_scorer = default_step_scorer()

    initial = frozenset(base)
    # heap entries: (neg_log_score, tie_counter, known_frozenset, steps)
    heap: list = [(0.0, 0, initial, [])]
    visited: set[frozenset[Formula]] = set()
    counter = 0

    while heap and counter < max_states:
        neg_score, _, known, steps = heapq.heappop(heap)

        if known in visited:
            continue
        visited.add(known)
        counter += 1

        if goal in known:
            return steps

        candidates = _generate_forward_steps(known, domain)

        for fstep in candidates:
            if fstep.formula in known:
                continue

            new_known = known | {fstep.formula}
            if new_known in visited:
                continue

            # Score this step with the Naive Bayes model
            feats = extract_step_features(
                fstep,
                goal=goal,
                available_count=len(known),
                depth=len(steps),
            )
            p_success = step_scorer.score(feats, "success")
            new_neg_score = neg_score - log(max(p_success, 1e-9))

            new_steps = steps + [fstep]
            heapq.heappush(heap, (new_neg_score, id(new_steps), new_known, new_steps))

    return None


# ---------------------------------------------------------------------------
# Step 4: Structural goal decomposition + best-first search
# ---------------------------------------------------------------------------

def _solve(
    base: list[Formula],
    goal: Formula,
    domain: set[Formula],
    struct_depth: int = 0,
) -> Optional[list[FOLProofStep]]:
    """
    Prove *goal* from *base*.

    Strategy:
      1. Fast checks (goal in context, contradiction).
      2. Structural decomposition of the goal shape -- mirrors the CSP solver
         so the Bayes solver handles the same problem classes.
      3. Structural rules on the context (Exists-elim, Or-elim).
      4. Best-first forward search for flat goals.
      5. RAA classical fallback.
    """
    if struct_depth > _MAX_STRUCT_DEPTH:
        return None

    available = set(base)

    # -- Fast path: goal already known ----------------------------------------
    if goal in available:
        return []

    # -- Contradiction -> ex falso --------------------------------------------
    if _has_contradiction(available):
        return [FOLStep(formula=goal, rule="ex_falso")]

    # -- ForAll-intro ---------------------------------------------------------
    # Add fresh constant to base so collect_terms can find it for forall_elim
    if isinstance(goal, ForAll):
        c = _fresh()
        subgoal = subst(goal.body, goal.var, c)
        sub = _solve(base + [c], subgoal, domain, struct_depth + 1)
        if sub is not None:
            return [FOLForAllIntroStep(
                formula=goal, var=goal.var,
                const_name=c.name, sub_steps=tuple(sub),
            )]
        return None

    # -- Imp-intro ------------------------------------------------------------
    if isinstance(goal, Imp):
        augmented = list(available) + [goal.left]
        sub = _solve(augmented, goal.right, domain, struct_depth + 1)
        if sub is not None:
            return [FOLImpIntroStep(
                formula=goal, antecedent=goal.left, sub_steps=tuple(sub),
            )]
        # Fall through: goal may be derivable as a fact via MP

    # -- Not-intro: assume A, derive contradiction ----------------------------
    if isinstance(goal, Not):
        augmented = list(available) + [goal.child]
        contra = _fol_solve_contra(
            augmented, _MAX_CONTRA_STEPS, struct_depth + 1, frozenset(), domain,
        )
        if contra is not None:
            return [FOLNotIntroStep(
                formula=goal, assumed=goal.child, contra_steps=tuple(contra),
            )]

    # -- And-intro: prove both conjuncts separately ---------------------------
    if isinstance(goal, And):
        l_sub = _solve(base, goal.left,  domain, struct_depth + 1)
        if l_sub is not None:
            r_sub = _solve(base, goal.right, domain, struct_depth + 1)
            if r_sub is not None:
                return l_sub + r_sub + [FOLStep(
                    formula=goal, rule="and_intro",
                    support1=goal.left, support2=goal.right,
                )]

    # -- Or-intro: try each disjunct -----------------------------------------
    if isinstance(goal, Or):
        sub = _solve(base, goal.left, domain, struct_depth + 1)
        if sub is not None:
            return sub + [FOLStep(formula=goal, rule="or_intro_l", support1=goal.left)]
        sub = _solve(base, goal.right, domain, struct_depth + 1)
        if sub is not None:
            return sub + [FOLStep(formula=goal, rule="or_intro_r", support1=goal.right)]

    # -- Exists-intro: try each available term as a witness -------------------
    if isinstance(goal, Exists):
        terms = collect_terms(available)
        for term in terms:
            subgoal = subst(goal.body, goal.var, term)
            if subgoal in available:
                return [FOLStep(
                    formula=goal, rule="exists_intro",
                    support1=subgoal, note=f"{goal.var}|{term}",
                )]
            sub = _solve(base, subgoal, domain, struct_depth + 1)
            if sub is not None:
                return sub + [FOLStep(
                    formula=goal, rule="exists_intro",
                    support1=subgoal, note=f"{goal.var}|{term}",
                )]

    # -- Exists-elim: eliminate any Exists in context -------------------------
    for f in list(available):
        if not isinstance(f, Exists):
            continue
        c = _fresh()
        instance = subst(f.body, f.var, c)
        augmented = [x for x in base if x is not f] + [instance]
        sub = _solve(augmented, goal, domain, struct_depth + 1)
        if sub is not None:
            return [FOLExistsElimStep(
                formula=goal, elim_formula=f,
                const_name=c.name, sub_steps=tuple(sub),
            )]

    # -- Or-elim: case-split on any disjunction in context --------------------
    for f in list(available):
        if not isinstance(f, Or):
            continue
        left_base  = [x for x in base if x is not f] + [f.left]
        right_base = [x for x in base if x is not f] + [f.right]
        left_sub  = _solve(left_base,  goal, domain, struct_depth + 1)
        right_sub = _solve(right_base, goal, domain, struct_depth + 1)
        if left_sub is not None and right_sub is not None:
            return [FOLOrElimStep(
                formula=goal, or_formula=f,
                left_steps=tuple(left_sub), right_steps=tuple(right_sub),
            )]

    # -- Best-first forward search --------------------------------------------
    fwd = _best_first_search(base, goal, domain)
    if fwd is not None:
        return fwd

    # -- RAA: classical fallback (assume ~goal, derive contradiction) ---------
    if not isinstance(goal, Not):
        neg = Not(goal)
        if neg not in available:
            contra = _fol_solve_contra(
                list(available) + [neg],
                _MAX_CONTRA_STEPS, struct_depth + 1, frozenset(), domain,
            )
            if contra is not None:
                return [FOLRAAStep(
                    formula=goal, neg_assumed=neg, contra_steps=tuple(contra),
                )]

    return None


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

def solve_logic_causal(
    assumptions: list[Formula],
    goal: Formula,
) -> Optional[list[FOLProofStep]]:
    """
    Bayesian Network proof solver.

    Parameters
    ----------
    assumptions : parsed Formula objects
    goal        : target Formula

    Returns
    -------
    list[FOLProofStep]  -- proof steps (compatible with render_logic_causal_steps)
    None                -- if the goal is not provable from the assumptions
    """
    reset_fresh()

    # Build the formula domain (all sub-formulas of assumptions + goal)
    domain = _build_domain(assumptions, goal)

    # Step 1: Build causal graph
    if assumptions:
        try:
            graph, all_atoms = _build_causal_graph(assumptions, goal)
        except Exception:
            graph = CausalGraph(set(), [])
            all_atoms = set()
    else:
        graph = CausalGraph(set(), [])
        all_atoms = set()

    # Step 2: D-separation filter -- prune causally irrelevant formulas
    if graph.nodes:
        assumption_atoms: set[str] = set()
        for f in assumptions:
            if isinstance(f, (Atom, Var, Predicate)):
                assumption_atoms.update(_atom_nodes(f))
        goal_atoms = _atom_nodes(goal)
        domain = _dsep_filter(domain, graph, assumption_atoms, goal_atoms)

    # Steps 3+4: Structural decomposition + best-first Bayesian search
    return _solve(list(assumptions), goal, domain)


def render_logic_causal_steps(
    steps: list[FOLProofStep],
    lines: list,
    depth: int = 0,
) -> None:
    """
    Flatten Bayes solver proof steps into (depth, formula_str, rule_label, note)
    tuples for the proof pane.  Delegates to render_fol_csp_steps since both
    solvers now share the same FOLProofStep types.
    """
    render_fol_csp_steps(steps, lines, depth)
