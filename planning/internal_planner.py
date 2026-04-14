from __future__ import annotations

"""
internal_planner.py — Forward BFS planner for FOL natural deduction.

Algorithm
---------
Structural rules (∀-intro, →-intro, ¬-intro, ∃-elim, ∨-elim, RAA) are handled
by goal-directed recursive decomposition — the same approach as the CSP solver.

Forward rules (∀-elim, ∧-elim, MP, ∃-intro, ∨-intro, ∧-intro) are explored
via *breadth-first search* over the known-formula state, which is the key
algorithmic distinction from the CSP solver's depth-first iterative deepening.

Two-pass strategy: direct proofs first (allow_raa=False), then classical RAA.
"""

from collections import deque
from typing import Optional, FrozenSet

from parser.ast import (
    Formula, Atom, And, Imp, Or, Not, Var, ForAll, Exists,
)
from logic.fol_prover import (
    subst, collect_terms,
    _fresh, reset_fresh,
    _contradiction, _expand_with_witnesses,
)


# --------------------------------------------------------------------------- #
# Constants
# --------------------------------------------------------------------------- #

MAX_FORWARD = 15   # BFS forward-step budget
MAX_STRUCT  = 20   # max recursive structural depth

_Keys = FrozenSet[tuple]


# --------------------------------------------------------------------------- #
# Domain / subformula helpers
# --------------------------------------------------------------------------- #

def _collect_subformulas(f: Formula, out: set) -> None:
    if f in out:
        return
    out.add(f)
    if isinstance(f, (And, Or, Imp)):
        _collect_subformulas(f.left,  out)
        _collect_subformulas(f.right, out)
    elif isinstance(f, Not):
        _collect_subformulas(f.child, out)
    elif isinstance(f, (ForAll, Exists)):
        _collect_subformulas(f.body, out)


def _build_domain(assumptions: list[Formula], goal: Formula) -> set[Formula]:
    domain: set[Formula] = set()
    for a in assumptions:
        _collect_subformulas(a, domain)
    _collect_subformulas(goal, domain)
    return domain


# --------------------------------------------------------------------------- #
# Forward rule generation (BFS actions)
# --------------------------------------------------------------------------- #

def _forward_steps(
    known:  frozenset[Formula],
    domain: set[Formula],
    terms:  list[Var],
) -> list[tuple[frozenset[Formula], str]]:
    """
    Return all valid one-step forward derivations from *known*,
    each as (new_known, action_string).
    """
    results: list[tuple[frozenset[Formula], str]] = []

    for f in known:
        # ∀-elim
        if isinstance(f, ForAll):
            for term in terms:
                inst = subst(f.body, f.var, term)
                if inst not in known:
                    results.append((known | {inst},
                                    f"forall-elim({f}, {term})"))
        # ∧-elim L / R
        if isinstance(f, And):
            if f.left not in known:
                results.append((known | {f.left},  f"and-elim-left({f})"))
            if f.right not in known:
                results.append((known | {f.right}, f"and-elim-right({f})"))

    # MP
    for f in known:
        if isinstance(f, Imp) and f.left in known and f.right not in known:
            results.append((known | {f.right}, f"mp({f.left}, {f})"))

    # ∃-intro
    for target in domain:
        if isinstance(target, Exists) and target not in known:
            for term in terms:
                witness = subst(target.body, target.var, term)
                if witness in known:
                    results.append((known | {target},
                                    f"exists-intro({witness}, {target})"))
                    break

    # ∨-intro L / R
    for target in domain:
        if isinstance(target, Or) and target not in known:
            if target.left in known:
                results.append((known | {target},
                                f"or-intro-left({target.left}, {target})"))
            elif target.right in known:
                results.append((known | {target},
                                f"or-intro-right({target.right}, {target})"))

    # ∧-intro
    for target in domain:
        if isinstance(target, And) and target not in known:
            if target.left in known and target.right in known:
                results.append((known | {target},
                                f"and-intro({target.left}, {target.right})"))

    return results


# --------------------------------------------------------------------------- #
# Structural solver (recursive) + BFS forward search
# --------------------------------------------------------------------------- #

def _solve(
    base:        list[Formula],
    goal:        Formula,
    max_forward: int,
    depth:       int,
    domain:      set[Formula],
    keys:        _Keys,
    allow_raa:   bool,
) -> Optional[list[str]]:
    """
    Prove *goal* from *base*.  Returns action list or None.
    Structural rules are handled recursively; forward rules via BFS.
    """
    if depth > MAX_STRUCT:
        return None

    available = set(base)

    # ── Trivial ──────────────────────────────────────────────────────────────
    if goal in available:
        return []
    if _contradiction(available):
        return [f"ex-falso → {goal}"]

    # ── Structural decomposition of goal ─────────────────────────────────────

    # ∀-intro
    if isinstance(goal, ForAll):
        c = _fresh()
        subgoal = subst(goal.body, goal.var, c)
        sub = _solve(list(available), subgoal,
                     max_forward, depth + 1, domain, keys, allow_raa)
        if sub is not None:
            return sub + [f"forall-intro({goal.var}↦{c.name}) → {goal}"]

    # →-intro
    if isinstance(goal, Imp):
        augmented = list(available) + [goal.left]
        sub = _solve(augmented, goal.right,
                     max_forward, depth + 1, domain, keys, allow_raa)
        if sub is not None:
            return sub + [f"imp-intro({goal.left}) → {goal}"]

    # ¬-intro
    if isinstance(goal, Not):
        augmented = list(available) + [goal.child]
        sub = _solve_contra(augmented, max_forward, depth + 1, domain, keys)
        if sub is not None:
            return sub + [f"not-intro({goal.child}) → {goal}"]

    # ∃-intro
    if isinstance(goal, Exists):
        key = ("∃I", str(goal))
        if key not in keys:
            terms = collect_terms(available)
            for term in terms:
                subgoal = subst(goal.body, goal.var, term)
                if subgoal in available:
                    return [f"exists-intro({goal.var}↦{term}) → {goal}"]
                sub = _solve(list(available), subgoal,
                             max_forward, depth + 1, domain,
                             keys | {key}, allow_raa)
                if sub is not None:
                    return sub + [f"exists-intro({goal.var}↦{term}) → {goal}"]

    # ∨-intro
    if isinstance(goal, Or):
        for side, label in [(goal.left, "left"), (goal.right, "right")]:
            key = ("∨I" + label, str(goal))
            if key not in keys:
                sub = _solve(list(available), side,
                             max_forward, depth + 1, domain,
                             keys | {key}, allow_raa)
                if sub is not None:
                    return sub + [f"or-intro-{label} → {goal}"]

    # ∧-intro
    if isinstance(goal, And):
        key = ("∧I", str(goal))
        if key not in keys:
            l = _solve(list(available), goal.left,
                       max_forward, depth + 1, domain, keys | {key}, allow_raa)
            if l is not None:
                r = _solve(list(available), goal.right,
                           max_forward, depth + 1, domain, keys | {key}, allow_raa)
                if r is not None:
                    return l + r + [f"and-intro({goal.left}, {goal.right}) → {goal}"]

    # ── Structural rules on context ───────────────────────────────────────────

    # ∃-elim
    for f in list(available):
        if not isinstance(f, Exists):
            continue
        key = ("∃E", str(f))
        if key in keys:
            continue
        c = _fresh()
        inst = subst(f.body, f.var, c)
        sub = _solve(list(available) + [inst], goal,
                     max_forward, depth + 1, domain, keys | {key}, allow_raa)
        if sub is not None:
            return ([f"exists-elim({f}↦{c.name})"]
                    + sub
                    + [f"exists-elim-close({f}) → {goal}"])

    # ∨-elim
    for f in list(available):
        if not isinstance(f, Or):
            continue
        key = ("∨E", str(f))
        if key in keys:
            continue
        nk = keys | {key}
        l = _solve(list(available) + [f.left],  goal,
                   max_forward, depth + 1, domain, nk, allow_raa)
        if l is not None:
            r = _solve(list(available) + [f.right], goal,
                       max_forward, depth + 1, domain, nk, allow_raa)
            if r is not None:
                return ([f"or-elim({f})"]
                        + l + r
                        + [f"or-elim-close → {goal}"])

    # ── BFS over forward rules ────────────────────────────────────────────────
    if max_forward > 0:
        terms   = collect_terms(available)
        initial = frozenset(available)
        queue: deque = deque([(initial, terms, [], 0)])
        visited: set = {initial}

        while queue:
            known, cur_terms, actions, fwd_depth = queue.popleft()
            if fwd_depth >= max_forward:
                continue

            for new_known, action in _forward_steps(known, domain, cur_terms):
                if new_known in visited:
                    continue
                visited.add(new_known)
                new_actions = actions + [action]

                if goal in new_known:
                    return new_actions

                # After each forward step try structural decomposition
                sub = _solve(list(new_known), goal,
                             0, depth + 1, domain, keys, allow_raa)
                if sub is not None:
                    return new_actions + sub

                queue.append((new_known, collect_terms(new_known),
                              new_actions, fwd_depth + 1))

    # ── RAA (classical fallback) ──────────────────────────────────────────────
    if allow_raa and not isinstance(goal, Not):
        neg = Not(goal)
        if neg not in available:
            key = ("RAA", str(goal))
            if key not in keys:
                sub = _solve_contra(list(available) + [neg],
                                    max_forward, depth + 1, domain, keys | {key})
                if sub is not None:
                    return ([f"assume({neg})"]
                            + sub
                            + [f"raa → {goal}"])

    return None


def _solve_contra(
    base:        list[Formula],
    max_forward: int,
    depth:       int,
    domain:      set[Formula],
    keys:        _Keys,
) -> Optional[list[str]]:
    """Derive a contradiction (⊥) from *base*."""
    if depth > MAX_STRUCT:
        return None

    available = _expand_with_witnesses(set(base))

    contra = _contradiction(available)
    if contra:
        pos, neg = contra
        return [f"contradiction({pos}, {neg})"]

    terms = collect_terms(available)

    # ∀-elim into context
    for f in list(available):
        if not isinstance(f, ForAll):
            continue
        for term in terms:
            key = ("∀E⊥", str(f), str(term))
            if key in keys:
                continue
            inst = subst(f.body, f.var, term)
            if inst in available:
                continue
            result = _solve_contra(list(available) + [inst],
                                   max_forward, depth + 1, domain, keys | {key})
            if result is not None:
                return [f"forall-elim({f}, {term})"] + result

    # ∃-elim into context
    for f in list(available):
        if not isinstance(f, Exists):
            continue
        key = ("∃E⊥", str(f))
        if key in keys:
            continue
        c = _fresh()
        inst = subst(f.body, f.var, c)
        result = _solve_contra(list(available) + [inst],
                               max_forward, depth + 1, domain, keys | {key})
        if result is not None:
            return [f"exists-elim({f}↦{c.name})"] + result

    # ∨-elim into context
    for f in list(available):
        if not isinstance(f, Or):
            continue
        key = ("∨E⊥", str(f))
        if key in keys:
            continue
        nk = keys | {key}
        l = _solve_contra(list(available) + [f.left],
                          max_forward, depth + 1, domain, nk)
        if l is not None:
            r = _solve_contra(list(available) + [f.right],
                              max_forward, depth + 1, domain, nk)
            if r is not None:
                return [f"or-elim-contra({f})"] + l + r

    # Prove the positive of each negation
    for f in list(available):
        if not isinstance(f, Not):
            continue
        key = ("prove+", str(f.child))
        if key in keys:
            continue
        proof = _solve(list(available - {f}), f.child,
                       max_forward, depth + 1, domain,
                       keys | {key}, allow_raa=True)
        if proof is not None:
            return proof + [f"contradiction({f.child}, {f})"]

    return None


# --------------------------------------------------------------------------- #
# Public API
# --------------------------------------------------------------------------- #

def plan_forward(
    assumptions: list[Formula],
    goal:        Formula,
    max_depth:   int = MAX_FORWARD,
) -> Optional[list[str]]:
    """
    FOL BFS planner.  Two-pass: direct proofs first, then classical RAA.
    Returns a list of action strings, or None if no proof found.
    """
    domain = _build_domain(assumptions, goal)

    # Pass 1: no RAA
    reset_fresh()
    result = _solve(list(assumptions), goal,
                    max_depth, 0, domain, frozenset(), allow_raa=False)
    if result is not None:
        return result

    # Pass 2: RAA allowed
    reset_fresh()
    return _solve(list(assumptions), goal,
                  max_depth, 0, domain, frozenset(), allow_raa=True)


def plan_and_print(
    assumptions: list[Formula],
    goal:        Formula,
    max_depth:   int = MAX_FORWARD,
) -> None:
    result = plan_forward(assumptions, goal, max_depth=max_depth)
    print(f"Assumptions: {[str(a) for a in assumptions]}")
    print(f"Goal:        {goal}")
    if result is None:
        print("No plan found within depth limit.")
    else:
        print(f"Plan ({len(result)} steps):")
        for i, action in enumerate(result, 1):
            print(f"  {i}. {action}")
