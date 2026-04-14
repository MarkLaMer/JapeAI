"""
Feature extraction for the Bayesian proof solver.

Only extract_step_features is exposed — it scores individual candidate
inference steps during best-first search.  The formula-domain, rule-level,
and partial-state feature extractors that used to live here were only needed
by the CSP's Bayes reordering layer, which has been removed.
"""

from __future__ import annotations

from typing import Any

from parser.ast import Formula, Atom, And, Imp, Not, Predicate, ForAll, Exists


# ──────────────────────────────────────────────────────────────────────────────
# Internal helpers
# ──────────────────────────────────────────────────────────────────────────────

def _formula_type(formula: Formula | None) -> str:
    if formula is None:    return "None"
    if isinstance(formula, Atom):      return "Atom"
    if isinstance(formula, And):       return "And"
    if isinstance(formula, Imp):       return "Imp"
    if isinstance(formula, Not):       return "Not"
    if isinstance(formula, Predicate): return "Predicate"
    if isinstance(formula, ForAll):    return "ForAll"
    if isinstance(formula, Exists):    return "Exists"
    return "Other"


def _formula_complexity(formula: Formula | None) -> int:
    if formula is None:
        return 0
    if isinstance(formula, Atom):
        return 1
    if isinstance(formula, Predicate):
        return 1 + len(formula.args)
    if isinstance(formula, Not):
        return 1 + _formula_complexity(formula.child)
    if isinstance(formula, (And, Imp)):
        return 1 + _formula_complexity(formula.left) + _formula_complexity(formula.right)
    if isinstance(formula, (ForAll, Exists)):
        return 2 + _formula_complexity(formula.body)
    return 1


def _bucket_complexity(value: int) -> str:
    if value <= 1: return "simple"
    if value <= 3: return "medium"
    return "complex"


def _bucket_count(value: int) -> str:
    if value <= 3:  return "small"
    if value <= 7:  return "medium"
    return "large"


def _bucket_depth(value: int) -> str:
    if value <= 1: return "shallow"
    if value <= 3: return "mid"
    return "deep"


def _collect_subformulas(formula: Formula, out: set[Formula]) -> None:
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
    # Atom, Predicate — leaves, nothing to recurse into


def _subformula_overlap_bucket(result: Formula, goal: Formula) -> str:
    """
    How many structural subformulas does `result` share with `goal`?

    full    — result IS the goal
    partial — they share at least one compound subformula
    none    — no meaningful structural overlap
    """
    if result == goal:
        return "full"

    result_subs: set[Formula] = set()
    _collect_subformulas(result, result_subs)

    goal_subs: set[Formula] = set()
    _collect_subformulas(goal, goal_subs)

    shared = result_subs & goal_subs
    meaningful = {f for f in shared if not isinstance(f, (Atom, Predicate))}

    if meaningful:
        return "partial"
    if result_subs & goal_subs:
        overlap_ratio = len(result_subs & goal_subs) / max(len(result_subs), 1)
        return "partial" if overlap_ratio >= 0.5 else "none"
    return "none"


def _is_subformula_of_goal(result: Formula, goal: Formula) -> str:
    """Is `result` a strict syntactic subformula of `goal`?"""
    if result == goal:
        return "False"
    goal_subs: set[Formula] = set()
    _collect_subformulas(goal, goal_subs)
    return str(result in goal_subs)


def _result_leads_to_goal(
    result: Formula,
    goal: Formula,
    available: list[Formula] | None,
) -> str:
    """
    Does `result` sit on a short implication path to `goal`?

    direct  — there is an available A → goal where A == result
    one_hop — there is an available result → X and X → goal
    False   — no such path found
    """
    if available is None:
        return "False"
    for f in available:
        if isinstance(f, Imp) and f.left == result and f.right == goal:
            return "direct"
    intermediates = {f.right for f in available
                     if isinstance(f, Imp) and f.left == result}
    for mid in intermediates:
        for f in available:
            if isinstance(f, Imp) and f.left == mid and f.right == goal:
                return "one_hop"
    return "False"


def _involves_quantifier(formula: Formula | None) -> str:
    """Does this formula involve a quantifier (ForAll or Exists)?"""
    if formula is None:
        return "False"
    if isinstance(formula, (ForAll, Exists)):
        return "True"
    if isinstance(formula, (And, Imp)):
        return str(
            _involves_quantifier(formula.left) == "True"
            or _involves_quantifier(formula.right) == "True"
        )
    if isinstance(formula, Not):
        return _involves_quantifier(formula.child)
    return "False"


# ──────────────────────────────────────────────────────────────────────────────
# Public API
# ──────────────────────────────────────────────────────────────────────────────

def extract_step_features(
    step: Any,
    *,
    goal: Formula,
    available_count: int,
    depth: int,
    available: list[Formula] | None = None,
) -> dict[str, str]:
    """
    Extract a feature dictionary for one candidate inference step.

    Parameters
    ----------
    step           : object with .formula, .rule, .support1, .support2
    goal           : the overall proof goal
    available_count: number of formulas currently known
    depth          : how many steps have been taken so far
    available      : list of currently-known formulas (for path features)
    """
    result_complexity = _formula_complexity(step.formula)
    return {
        "rule":               str(step.rule),
        "result_is_goal":     str(step.formula == goal),
        "result_type":        _formula_type(step.formula),
        "result_complexity":  _bucket_complexity(result_complexity),
        "support1_type":      _formula_type(step.support1),
        "support2_type":      _formula_type(step.support2),
        "available_count":    _bucket_count(available_count),
        "depth":              _bucket_depth(depth),
        # goal-directed features
        "subformula_overlap":   _subformula_overlap_bucket(step.formula, goal),
        "is_subformula_of_goal": _is_subformula_of_goal(step.formula, goal),
        "leads_to_goal":        _result_leads_to_goal(step.formula, goal, available),
        # quantifier-awareness features
        "result_has_quantifier": _involves_quantifier(step.formula),
        "goal_has_quantifier":   _involves_quantifier(goal),
    }
