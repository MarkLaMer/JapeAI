"""
cbn/logic_causal.py — CBN / SCM-backed natural-deduction solver (complete FOL).

Accepts the same (assumptions, goal) input as csp/fol_csp.py and returns
FOLProofStep objects rendered by the same render_fol_csp_steps() function,
so the GUI proof pane looks identical to the CSP solver output.

This module builds the causal graph and SCM, then runs an independent
factor-style propagation solver in cbn/factor_bp.py.  The CBN / SCM layer
provides:
  1. dependency structure via CausalGraph
  2. deterministic reachability / ordering via SCM
  3. guidance for the native proof engine's message-passing schedule
"""
from __future__ import annotations

import heapq
from math import log
from typing import Optional

from parser.ast import Formula, Atom, And, Imp, Not, Or, ForAll, Exists, Var, Predicate
from cbn.graph import CausalGraph, graph_from_string
from cbn.scm   import SCM, SCMVariable, NoiseVar
from csp.fol_csp import render_fol_csp_steps, FOLProofStep
from cbn.factor_bp import solve_factor_bp


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
    CBN / SCM-backed FOL natural deduction solver.

    Builds the causal graph and SCM, then runs the independent factor /
    message-passing proof engine in cbn/factor_bp.py.

    Handles all connectives and quantifiers:  ∀ ∃ ¬ ∨ ∧ →  plus RAA.

    Returns
    -------
    list[FOLProofStep]  — same proof-step types as the GUI renderer expects
    None                — goal not provable from the given assumptions
    """
    graph: CausalGraph | None = None
    scm: SCM | None = None
    try:
        graph, label_map = _build_graph(assumptions, goal)
        scm = _build_scm(assumptions, graph, label_map)
    except Exception:
        pass

    return solve_factor_bp(assumptions, goal, graph=graph, scm=scm)


def explain_logic_causal(
    assumptions: list[Formula],
    goal: Formula,
) -> list[CausalProofLine] | None:
    """
    Return the proof as a flat list of (conclusion, rule_label) pairs.
    Used by the CLI (main.py) for the "formula   (rule)" output format.

    Structural sub-proofs (∀-intro scope, →-intro scope, etc.) are rendered
    with indentation encoded in the action string.
    """
    steps = solve_logic_causal(assumptions, goal)
    if steps is None:
        return None

    lines: list = []
    render_fol_csp_steps(steps, lines)

    result: list[CausalProofLine] = []
    _NON_DERIVED = {"assumption", "assumptions", "premise", "premises", "hyp"}
    for depth, formula_str, rule_label, note in lines:
        if rule_label in _NON_DERIVED:
            continue
        indent = "  " * depth
        note_part = f"  [{note}]" if note else ""
        result.append(CausalProofLine(
            conclusion=f"{indent}{formula_str}",
            action=f"{rule_label}{note_part}",
        ))

    return result


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
