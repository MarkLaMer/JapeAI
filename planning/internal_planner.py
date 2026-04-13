from __future__ import annotations

"""
internal_planner.py — Forward BFS planner for the theorem-proving PDDL domain.

Treats the PDDL encoding as a state-space problem and searches it directly,
without needing an external planner binary.

State  : frozenset of currently-known Formula objects
Actions: the four PDDL domain actions (MP, AND-ELIM-LEFT, AND-ELIM-RIGHT, AND-INTRO)
         plus ImpIntro (scoped hypothesis, proves Imp formulas)
Goal   : goal formula is in the known set

This is complementary to the backward-chaining logic/rules.py prover:
- logic/rules.py is goal-directed (backward chaining)
- This planner is data-directed (forward chaining, PDDL-style)

Returns a list of action strings matching the PDDL domain action names.
"""

from collections import deque
from typing import Optional

from parser.ast import Formula, And, Imp
from planning.encoder import collect_formulas


# --------------------------------------------------------------------------- #
# Action application
# --------------------------------------------------------------------------- #

def _apply_actions(
    known: frozenset[Formula],
    implications: list[tuple[Formula, Formula, Formula]],
    conjunctions: list[tuple[Formula, Formula, Formula]],
) -> list[tuple[frozenset[Formula], str]]:
    """
    Return (new_known_set, action_description) for every applicable action.

    implications : list of (A, B, Imp(A,B)) triples
    conjunctions : list of (A, B, And(A,B)) triples
    """
    results: list[tuple[frozenset[Formula], str]] = []

    for a, b, imp in implications:
        # modus-ponens: known(A) ∧ known(A→B) → known(B)
        if a in known and imp in known and b not in known:
            results.append((
                known | {b},
                f"modus-ponens({a}, {b}, {imp})",
            ))

    for a, b, conj in conjunctions:
        # and-elim-left: known(A∧B) → known(A)
        if conj in known and a not in known:
            results.append((
                known | {a},
                f"and-elim-left({a}, {b}, {conj})",
            ))
        # and-elim-right: known(A∧B) → known(B)
        if conj in known and b not in known:
            results.append((
                known | {b},
                f"and-elim-right({a}, {b}, {conj})",
            ))
        # and-intro: known(A) ∧ known(B) → known(A∧B)
        if a in known and b in known and conj not in known:
            results.append((
                known | {conj},
                f"and-intro({a}, {b}, {conj})",
            ))

    return results


# --------------------------------------------------------------------------- #
# Core planner
# --------------------------------------------------------------------------- #

def plan_forward(
    assumptions: list[Formula],
    goal: Formula,
    max_depth: int = 20,
) -> Optional[list[str]]:
    """
    Forward BFS planner over the PDDL domain state space.

    Supports:
    - modus-ponens
    - and-elim-left / and-elim-right
    - and-intro
    - imp-intro  (hypothetical scoped proof, inline recursive call)

    Returns a list of action-description strings on success, or None if
    no proof is found within max_depth forward steps.

    The action strings mirror the PDDL domain action names so the output
    can be cross-checked against a PDDL planner's plan.
    """
    # Collect every formula and subformula referenced in the problem.
    all_formulas: set[Formula] = set()
    for a in assumptions:
        collect_formulas(a, all_formulas)
    collect_formulas(goal, all_formulas)

    implications = [
        (f.left, f.right, f)
        for f in all_formulas
        if isinstance(f, Imp)
    ]
    conjunctions = [
        (f.left, f.right, f)
        for f in all_formulas
        if isinstance(f, And)
    ]

    initial: frozenset[Formula] = frozenset(assumptions)

    # Quick check: can we prove via ImpIntro at the top level?
    # If goal is Imp(A,B), try proving B from assumptions+{A} and wrap result.
    if isinstance(goal, Imp) and max_depth > 0:
        intro_result = plan_forward(
            list(assumptions) + ([goal.left] if goal.left not in assumptions else []),
            goal.right,
            max_depth - 1,
        )
        if intro_result is not None:
            return intro_result + [f"imp-intro({goal.left}, {goal.right}, {goal})"]

    # BFS: each entry is (known_set, action_list_so_far, depth)
    queue: deque[tuple[frozenset[Formula], list[str], int]] = deque()
    queue.append((initial, [], 0))
    visited: set[frozenset[Formula]] = {initial}

    while queue:
        known, actions, depth = queue.popleft()

        if goal in known:
            return actions

        if depth >= max_depth:
            continue

        for new_known, action_str in _apply_actions(known, implications, conjunctions):
            if new_known not in visited:
                visited.add(new_known)
                queue.append((new_known, actions + [action_str], depth + 1))

            # Also try ImpIntro from the new state for any Imp formula in domain.
            for imp_formula in all_formulas:
                if not isinstance(imp_formula, Imp):
                    continue
                if imp_formula in new_known:
                    continue
                a_hyp = imp_formula.left
                b_cons = imp_formula.right
                hyp_assumptions = list(new_known)
                if a_hyp not in new_known:
                    hyp_assumptions.append(a_hyp)
                if b_cons in new_known or b_cons in frozenset(hyp_assumptions):
                    # Consequent is already reachable without sub-proof steps
                    with_imp = new_known | {imp_formula}
                    if with_imp not in visited:
                        visited.add(with_imp)
                        intro_action = (
                            f"imp-intro({a_hyp}, {b_cons}, {imp_formula})"
                        )
                        queue.append((
                            with_imp,
                            actions + [action_str, intro_action],
                            depth + 1,
                        ))

    return None


def plan_and_print(
    assumptions: list[Formula],
    goal: Formula,
    max_depth: int = 20,
) -> None:
    """
    Convenience wrapper: plan and print the resulting action sequence.
    """
    result = plan_forward(assumptions, goal, max_depth=max_depth)
    print(f"Assumptions: {[str(a) for a in assumptions]}")
    print(f"Goal:        {goal}")
    if result is None:
        print("No plan found within depth limit.")
    else:
        print(f"Plan ({len(result)} steps):")
        for i, action in enumerate(result):
            print(f"  {i + 1}. {action}")
