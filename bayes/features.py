from __future__ import annotations

from typing import Any, Mapping

from parser.ast import Formula, Atom, And, Imp, Not


def _formula_type(formula: Formula | None) -> str:
    if formula is None:
        return "None"
    if isinstance(formula, Atom):
        return "Atom"
    if isinstance(formula, And):
        return "And"
    if isinstance(formula, Imp):
        return "Imp"
    if isinstance(formula, Not):
        return "Not"
    return "Other"


def _formula_complexity(formula: Formula | None) -> int:
    if formula is None:
        return 0
    if isinstance(formula, Atom):
        return 1
    if isinstance(formula, Not):
        return 1 + _formula_complexity(formula.child)
    if isinstance(formula, And):
        return 1 + _formula_complexity(formula.left) + _formula_complexity(formula.right)
    if isinstance(formula, Imp):
        return 1 + _formula_complexity(formula.left) + _formula_complexity(formula.right)
    return 1


def _bucket_complexity(value: int) -> str:
    if value <= 1:
        return "simple"
    if value <= 3:
        return "medium"
    return "complex"


def _bucket_count(value: int) -> str:
    if value <= 3:
        return "small"
    if value <= 7:
        return "medium"
    return "large"


def _bucket_depth(value: int) -> str:
    if value <= 1:
        return "shallow"
    if value <= 3:
        return "mid"
    return "deep"


def _bucket_remaining_steps(value: int) -> str:
    if value <= 1:
        return "low"
    if value <= 3:
        return "medium"
    return "high"


def extract_formula_features(
    formula: Formula,
    *,
    is_goal: bool,
    is_assumption: bool,
) -> dict[str, str]:
    return {
        "formula_type": _formula_type(formula),
        "complexity_bucket": _bucket_complexity(_formula_complexity(formula)),
        "is_goal": str(bool(is_goal)),
        "is_assumption": str(bool(is_assumption)),
    }


def extract_step_features(
    step: Any,
    *,
    goal: Formula,
    available_count: int,
    depth: int,
) -> dict[str, str]:
    result_complexity = _formula_complexity(step.formula)
    return {
        "rule": str(step.rule),
        "result_is_goal": str(step.formula == goal),
        "result_type": _formula_type(step.formula),
        "result_complexity": _bucket_complexity(result_complexity),
        "support1_type": _formula_type(step.support1),
        "support2_type": _formula_type(step.support2),
        "available_count": _bucket_count(available_count),
        "depth": _bucket_depth(depth),
    }


def extract_rule_features(
    *,
    rule: str,
    goal: Formula,
    available_count: int,
    depth: int,
) -> dict[str, str]:
    return {
        "rule": str(rule),
        "goal_type": _formula_type(goal),
        "available_count": _bucket_count(available_count),
        "depth": _bucket_depth(depth),
    }


def extract_partial_features(
    *,
    goal: Formula,
    available_count: int,
    depth: int,
    remaining_steps: int,
    goal_in_available: bool,
) -> dict[str, str]:
    return {
        "goal_type": _formula_type(goal),
        "available_count": _bucket_count(available_count),
        "depth": _bucket_depth(depth),
        "remaining_steps": _bucket_remaining_steps(remaining_steps),
        "goal_in_available": str(bool(goal_in_available)),
    }
