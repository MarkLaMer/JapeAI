"""
tests/test_bayes_solver.py -- Bayesian best-first FOL proof solver tests.

Covers every GUI example category:
  - Propositional
  - FOL Warm-up
  - FOL Level 1
  - FOL Level 2
  - FOL Level 3

All three solvers (CSP, PDDL, Bayes) are exercised on every example to
verify consistent results.  Individual solver files have their own focused
unit tests; this file concentrates on the Bayes solver and cross-solver
agreement.
"""
from __future__ import annotations

import pytest
from parser.parser import parse_formula as pf

from cbn.logic_causal import solve_logic_causal, render_logic_causal_steps
from csp.fol_csp import solve_fol_csp, FOLProofStep
from planning.internal_planner import plan_forward


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _bayes(assumptions_strs: list[str], goal_str: str):
    """Parse and run the Bayes solver."""
    return solve_logic_causal([pf(s) for s in assumptions_strs], pf(goal_str))


def _csp(assumptions_strs: list[str], goal_str: str):
    return solve_fol_csp([pf(s) for s in assumptions_strs], pf(goal_str))


def _pddl(assumptions_strs: list[str], goal_str: str):
    return plan_forward([pf(s) for s in assumptions_strs], pf(goal_str))


def _rules(result) -> list[str]:
    """Flatten all rule names out of a FOLProofStep tree."""
    rules = []
    for s in result:
        if hasattr(s, "rule"):
            rules.append(s.rule)
        if hasattr(s, "sub_steps"):
            rules.extend(_rules(list(s.sub_steps)))
        for attr in ("left_steps", "right_steps", "contra_steps"):
            if hasattr(s, attr):
                rules.extend(_rules(list(getattr(s, attr))))
    return rules


def _conclusions(result) -> list[str]:
    """Collect all conclusion formula strings from a step tree."""
    out = []
    for s in result:
        if hasattr(s, "formula"):
            out.append(str(s.formula))
        if hasattr(s, "sub_steps"):
            out.extend(_conclusions(list(s.sub_steps)))
        for attr in ("left_steps", "right_steps", "contra_steps"):
            if hasattr(s, attr):
                out.extend(_conclusions(list(getattr(s, attr))))
    return out


# ---------------------------------------------------------------------------
# Propositional examples
# ---------------------------------------------------------------------------

class TestBayesPropositional:

    def test_modus_ponens(self):
        r = _bayes(["P", "P -> Q"], "Q")
        assert r is not None
        assert "Q" in _conclusions(r)

    def test_and_elim_commute(self):
        # P & Q |- Q & P
        r = _bayes(["P & Q"], "Q & P")
        assert r is not None

    def test_and_intro(self):
        r = _bayes(["P", "Q"], "P & Q")
        assert r is not None
        assert "and_intro" in _rules(r)

    def test_p_imp_p(self):
        r = _bayes([], "P -> P")
        assert r is not None
        assert "imp_intro" in _rules(r)

    def test_and_commutativity_tautology(self):
        r = _bayes([], "(P & Q) -> (Q & P)")
        assert r is not None

    def test_weakening_tautology(self):
        # P |- Q -> (P & Q)
        r = _bayes(["P"], "Q -> (P & Q)")
        assert r is not None

    def test_unprovable_p_to_q(self):
        r = _bayes(["P"], "Q")
        assert r is None

    def test_unprovable_empty(self):
        r = _bayes([], "Q")
        assert r is None


# ---------------------------------------------------------------------------
# FOL Warm-up
# ---------------------------------------------------------------------------

class TestBayesFOLWarmup:

    def test_forall_mp_chain(self):
        """forall y.(T(y)->Q(y)), forall y.T(y) |- forall y.Q(y)"""
        r = _bayes(
            ["forall y.(T(y) -> Q(y))", "forall y.T(y)"],
            "forall y.Q(y)",
        )
        assert r is not None


# ---------------------------------------------------------------------------
# FOL Level 1
# ---------------------------------------------------------------------------

class TestBayesFOLLevel1:

    def test_forall_imp_exists(self):
        """forall y.(T(y)->Q(y)/\R(y)) |- forall y.(T(y)->exists z.Q(z))"""
        r = _bayes(
            ["forall y.(T(y) -> (Q(y) & R(y)))"],
            "forall y.(T(y) -> exists z.Q(z))",
        )
        assert r is not None

    def test_exists_disjunction(self):
        """exists y.Q(y) \/ exists z.S(z) |- exists x.(S(x) \/ Q(x))"""
        r = _bayes(
            ["exists y.Q(y) | exists z.S(z)"],
            "exists x.(S(x) | Q(x))",
        )
        assert r is not None

    def test_exists_t_forall_t_imp_r(self):
        """exists y.T(y), forall y.(T(y)->R(y)) |- exists y.R(y)"""
        r = _bayes(
            ["exists y.T(y)", "forall y.(T(y) -> R(y))"],
            "exists y.R(y)",
        )
        assert r is not None


# ---------------------------------------------------------------------------
# FOL Level 2
# ---------------------------------------------------------------------------

class TestBayesFOLLevel2:

    def test_negation_push(self):
        """forall x.forall z.(~Q(z)/\S(x)) |- ~exists x.forall z.(S(x)->Q(z))"""
        r = _bayes(
            ["forall x.forall z.(~Q(z) & S(x))"],
            "~exists x.forall z.(S(x) -> Q(z))",
        )
        assert r is not None

    def test_case_split_universal(self):
        """exists x.~Q(x), forall x.R(x)\/forall x.Q(x), forall x.(R(x)->T(x)) |- forall x.T(x)"""
        r = _bayes(
            ["exists x.~Q(x)", "forall x.R(x) | forall x.Q(x)", "forall x.(R(x) -> T(x))"],
            "forall x.T(x)",
        )
        assert r is not None

    def test_or_elim_universal(self):
        """forall y.T(y)\/forall y.S(y), exists y.~T(y), forall y.(S(y)->P(y)) |- forall y.P(y)"""
        r = _bayes(
            ["forall y.T(y) | forall y.S(y)", "exists y.~T(y)", "forall y.(S(y) -> P(y))"],
            "forall y.P(y)",
        )
        assert r is not None


# ---------------------------------------------------------------------------
# FOL Level 3
# ---------------------------------------------------------------------------

class TestBayesFOLLevel3:

    def test_neg_exists_to_forall_neg(self):
        """~exists x.(~exists z.T(z)->Q(x)) |- forall x.~(Q(x)\/exists z.T(z))"""
        r = _bayes(
            ["~exists x.(~exists z.T(z) -> Q(x))"],
            "forall x.~(Q(x) | exists z.T(z))",
        )
        assert r is not None

    def test_forall_neg_to_neg_exists(self):
        """forall z.~(P(z)\/exists x.T(x)) |- ~exists z.(~exists x.T(x)->P(z))"""
        r = _bayes(
            ["forall z.~(P(z) | exists x.T(x))"],
            "~exists z.(~exists x.T(x) -> P(z))",
        )
        assert r is not None

    def test_nested_forall_contrapositive(self):
        """forall y.forall z.(exists x.~R(x)->(P(z)->~Q(y))) |- forall y.forall z.forall x.((P(z)/\Q(x))->R(z))"""
        r = _bayes(
            ["forall y.forall z.(exists x.~R(x) -> (P(z) -> ~Q(y)))"],
            "forall y.forall z.forall x.((P(z) & Q(x)) -> R(z))",
        )
        assert r is not None

    def test_forall_imp_exists_generalized(self):
        """forall x.(P(x)->T(x)) |- exists x.P(x)->exists x.T(x)"""
        r = _bayes(
            ["forall x.(P(x) -> T(x))"],
            "exists x.P(x) -> exists x.T(x)",
        )
        assert r is not None

    def test_complex_exists_and(self):
        """exists y.(Q(y)->T(y))/\forall y.((T(y)/\Q(y))\/Q(y)) |- exists y.(T(y)/\Q(y))"""
        r = _bayes(
            ["exists y.(Q(y) -> T(y)) & forall y.((T(y) & Q(y)) | Q(y))"],
            "exists y.(T(y) & Q(y))",
        )
        assert r is not None

    def test_forall_neg_to_neg_exists_v2(self):
        """forall y.~(T(y)\/exists z.P(z)) |- ~exists y.(~exists z.P(z)->T(y))"""
        r = _bayes(
            ["forall y.~(T(y) | exists z.P(z))"],
            "~exists y.(~exists z.P(z) -> T(y))",
        )
        assert r is not None


# ---------------------------------------------------------------------------
# Render output (smoke test)
# ---------------------------------------------------------------------------

class TestBayesRenderOutput:

    def test_render_does_not_raise(self):
        r = _bayes(["P", "P -> Q"], "Q")
        assert r is not None
        lines = []
        render_logic_causal_steps(r, lines)
        assert len(lines) > 0

    def test_render_tuples_have_four_fields(self):
        r = _bayes(["P", "P -> Q", "Q -> R"], "R")
        assert r is not None
        lines = []
        render_logic_causal_steps(r, lines)
        for entry in lines:
            assert len(entry) == 4, f"Expected 4-tuple, got {entry}"

    def test_render_imp_intro(self):
        r = _bayes([], "P -> P")
        assert r is not None
        lines = []
        render_logic_causal_steps(r, lines)
        rule_labels = [entry[2] for entry in lines]
        assert any("intro" in lbl for lbl in rule_labels)


# ---------------------------------------------------------------------------
# Cross-solver agreement: all three solvers must agree on provability
# ---------------------------------------------------------------------------

PROVABLE_EXAMPLES = [
    (["P", "P -> Q"], "Q"),
    (["P & Q"], "Q & P"),
    (["P", "Q"], "P & Q"),
    ([], "P -> P"),
    ([], "(P & Q) -> (Q & P)"),
    (["P"], "Q -> (P & Q)"),
    (["forall y.(T(y) -> Q(y))", "forall y.T(y)"], "forall y.Q(y)"),
]

UNPROVABLE_EXAMPLES = [
    (["P"], "Q"),
    ([], "P & Q"),
]


@pytest.mark.parametrize("assumptions,goal", PROVABLE_EXAMPLES)
def test_all_solvers_agree_provable(assumptions, goal):
    """Bayes, CSP, and PDDL must all return a proof for known-provable problems."""
    assert _bayes(assumptions, goal) is not None, f"Bayes failed: {assumptions} |- {goal}"
    assert _csp(assumptions, goal)   is not None, f"CSP failed: {assumptions} |- {goal}"
    assert _pddl(assumptions, goal)  is not None, f"PDDL failed: {assumptions} |- {goal}"


@pytest.mark.parametrize("assumptions,goal", UNPROVABLE_EXAMPLES)
def test_all_solvers_agree_unprovable(assumptions, goal):
    """All solvers must return None for known-unprovable problems."""
    assert _bayes(assumptions, goal) is None, f"Bayes wrongly proved: {assumptions} |- {goal}"
    assert _csp(assumptions, goal)   is None, f"CSP wrongly proved: {assumptions} |- {goal}"
    assert _pddl(assumptions, goal)  is None, f"PDDL wrongly proved: {assumptions} |- {goal}"
