"""
Tests for first-order quantifier support.

Covers:
  - AST nodes: ForAll, Exists, Predicate
  - Parser: forall/exists syntax, predicates with arguments
  - Substitution: free vs bound occurrences, shadowing
  - Bayesian solver rules: universal_instantiation, existential_intro
  - Combined proofs mixing quantifiers with propositional rules
  - Failure cases (goals that should not be provable)
"""

import pytest

from parser.parser import parse_formula
from parser.ast import Atom, And, Imp, Not, Predicate, ForAll, Exists
from logic.substitution import substitute, free_vars, collect_terms
from bayes.solver import solve_bayes


# ──────────────────────────────────────────────────────────────────────────────
# Parser tests
# ──────────────────────────────────────────────────────────────────────────────

class TestParser:
    def test_predicate_one_arg(self):
        f = parse_formula("P(x)")
        assert isinstance(f, Predicate)
        assert f.name == "P"
        assert f.args == ("x",)

    def test_predicate_two_args(self):
        f = parse_formula("R(x, y)")
        assert isinstance(f, Predicate)
        assert f.name == "R"
        assert f.args == ("x", "y")

    def test_predicate_constant_arg(self):
        f = parse_formula("P(A)")
        assert isinstance(f, Predicate)
        assert f.args == ("A",)

    def test_predicate_mixed_args(self):
        f = parse_formula("Q(x, A)")
        assert isinstance(f, Predicate)
        assert f.args == ("x", "A")

    def test_forall_simple(self):
        f = parse_formula("forall x. P(x)")
        assert isinstance(f, ForAll)
        assert f.var == "x"
        assert isinstance(f.body, Predicate)
        assert f.body.name == "P"
        assert f.body.args == ("x",)

    def test_exists_simple(self):
        f = parse_formula("exists x. Q(x)")
        assert isinstance(f, Exists)
        assert f.var == "x"

    def test_forall_with_implication(self):
        f = parse_formula("forall x. (P(x) -> Q(x))")
        assert isinstance(f, ForAll)
        assert isinstance(f.body, Imp)
        assert isinstance(f.body.left,  Predicate)
        assert isinstance(f.body.right, Predicate)

    def test_forall_with_conjunction(self):
        f = parse_formula("forall x. (P(x) & Q(x))")
        assert isinstance(f, ForAll)
        assert isinstance(f.body, And)

    def test_nested_quantifiers(self):
        f = parse_formula("forall x. exists y. R(x, y)")
        assert isinstance(f, ForAll)
        assert isinstance(f.body, Exists)
        assert isinstance(f.body.body, Predicate)
        assert f.body.body.args == ("x", "y")

    def test_quantifier_in_conjunction(self):
        f = parse_formula("P & (forall x. Q(x))")
        assert isinstance(f, And)
        assert isinstance(f.right, ForAll)

    def test_str_roundtrip_predicate(self):
        original = "P(x)"
        assert str(parse_formula(original)) == original

    def test_str_roundtrip_forall(self):
        f = parse_formula("forall x. P(x)")
        assert str(f) == "forall x. P(x)"

    def test_str_roundtrip_exists(self):
        f = parse_formula("exists x. Q(x)")
        assert str(f) == "exists x. Q(x)"


# ──────────────────────────────────────────────────────────────────────────────
# Substitution tests
# ──────────────────────────────────────────────────────────────────────────────

class TestSubstitution:
    def test_predicate_substitution(self):
        p = Predicate("P", ("x",))
        result = substitute(p, "x", "A")
        assert result == Predicate("P", ("A",))

    def test_predicate_substitution_multi_arg(self):
        p = Predicate("R", ("x", "y"))
        result = substitute(p, "x", "A")
        assert result == Predicate("R", ("A", "y"))

    def test_predicate_no_substitution_on_other_var(self):
        p = Predicate("R", ("x", "y"))
        result = substitute(p, "z", "A")
        assert result == p

    def test_atom_unchanged(self):
        a = Atom("P")
        assert substitute(a, "x", "A") is a

    def test_forall_shadowing(self):
        # forall x. P(x) — x is bound, so substitute(., "x", "A") must not
        # change the body because the binder shadows the substitution.
        f = parse_formula("forall x. P(x)")
        result = substitute(f, "x", "A")
        assert result == f

    def test_forall_different_var(self):
        # forall y. P(y) — substituting x -> A should not touch y
        f = ForAll("y", Predicate("P", ("y",)))
        result = substitute(f, "x", "A")
        assert result == f

    def test_exists_shadowing(self):
        f = parse_formula("exists x. P(x)")
        result = substitute(f, "x", "B")
        assert result == f

    def test_imp_substitution(self):
        f = parse_formula("P(x) -> Q(x)")
        result = substitute(f, "x", "A")
        assert result == Imp(Predicate("P", ("A",)), Predicate("Q", ("A",)))

    def test_and_substitution(self):
        f = parse_formula("P(x) & Q(y)")
        result = substitute(f, "x", "C")
        assert result == And(Predicate("P", ("C",)), Predicate("Q", ("y",)))

    def test_not_substitution(self):
        f = parse_formula("~P(x)")
        result = substitute(f, "x", "A")
        assert result == Not(Predicate("P", ("A",)))


class TestFreeVars:
    def test_predicate_has_free_var(self):
        assert free_vars(parse_formula("P(x)")) == {"x"}

    def test_constant_arg_not_free_var(self):
        assert free_vars(parse_formula("P(A)")) == set()

    def test_forall_binds_var(self):
        assert free_vars(parse_formula("forall x. P(x)")) == set()

    def test_exists_binds_var(self):
        assert free_vars(parse_formula("exists x. P(x)")) == set()

    def test_free_in_conjunction(self):
        f = parse_formula("P(x) & Q(y)")
        assert free_vars(f) == {"x", "y"}

    def test_partial_binding(self):
        # forall x. (P(x) & Q(y)) — x bound, y free
        f = parse_formula("forall x. (P(x) & Q(y))")
        assert free_vars(f) == {"y"}


class TestCollectTerms:
    def test_atom_name_is_term(self):
        out: set[str] = set()
        collect_terms(Atom("P"), out)
        assert "P" in out

    def test_predicate_args_are_terms(self):
        out: set[str] = set()
        collect_terms(Predicate("R", ("x", "A")), out)
        assert "x" in out
        assert "A" in out

    def test_collects_through_quantifier(self):
        out: set[str] = set()
        f = parse_formula("forall x. P(x)")
        collect_terms(f, out)
        assert "x" in out


# ──────────────────────────────────────────────────────────────────────────────
# Bayesian solver — universal instantiation
# ──────────────────────────────────────────────────────────────────────────────

class TestUniversalInstantiation:
    def test_ui_direct(self):
        """∀x.P(x) ⊢ P(A)"""
        assumptions = [parse_formula("forall x. P(x)")]
        goal = parse_formula("P(A)")
        result = solve_bayes(assumptions, goal, max_steps=2)
        assert result is not None
        assert len(result) == 1
        assert result[0].rule == "universal_instantiation"
        assert result[0].formula == Predicate("P", ("A",))

    def test_ui_two_constants(self):
        """∀x.P(x), ∀x.Q(x) ⊢ P(B) & Q(B)"""
        assumptions = [
            parse_formula("forall x. P(x)"),
            parse_formula("forall x. Q(x)"),
        ]
        goal = parse_formula("P(B) & Q(B)")
        result = solve_bayes(assumptions, goal, max_steps=4)
        assert result is not None
        rules = [s.rule for s in result]
        assert "universal_instantiation" in rules
        assert "and_intro" in rules

    def test_ui_then_mp(self):
        """∀x.(P(x) -> Q(x)), P(A) ⊢ Q(A)"""
        assumptions = [
            parse_formula("forall x. (P(x) -> Q(x))"),
            parse_formula("P(A)"),
        ]
        goal = parse_formula("Q(A)")
        result = solve_bayes(assumptions, goal, max_steps=3)
        assert result is not None
        rules = [s.rule for s in result]
        assert "universal_instantiation" in rules
        assert "modus_ponens" in rules

    def test_ui_chain(self):
        """∀x.(P(x)->Q(x)), ∀x.(Q(x)->R(x)), P(A) ⊢ R(A)"""
        assumptions = [
            parse_formula("forall x. (P(x) -> Q(x))"),
            parse_formula("forall x. (Q(x) -> R(x))"),
            parse_formula("P(A)"),
        ]
        goal = parse_formula("R(A)")
        result = solve_bayes(assumptions, goal, max_steps=4)
        assert result is not None

    def test_ui_multiple_terms(self):
        """∀x.P(x), goal P(B) where B appears only in goal — terms are collected from goal."""
        assumptions = [parse_formula("forall x. P(x)")]
        goal = parse_formula("P(B)")
        result = solve_bayes(assumptions, goal, max_steps=2)
        assert result is not None
        assert result[0].formula == Predicate("P", ("B",))


# ──────────────────────────────────────────────────────────────────────────────
# Bayesian solver — existential introduction
# ──────────────────────────────────────────────────────────────────────────────

class TestExistentialIntro:
    def test_ei_direct(self):
        """P(A) ⊢ ∃x.P(x)"""
        assumptions = [parse_formula("P(A)")]
        goal = parse_formula("exists x. P(x)")
        result = solve_bayes(assumptions, goal, max_steps=2)
        assert result is not None
        assert result[-1].rule == "existential_intro"

    def test_ei_after_ui(self):
        """∀x.P(x) ⊢ ∃x.P(x)  (needs UI first, then EI)"""
        assumptions = [parse_formula("forall x. P(x)")]
        goal = parse_formula("exists x. P(x)")
        result = solve_bayes(assumptions, goal, max_steps=3)
        assert result is not None
        rules = [s.rule for s in result]
        assert "universal_instantiation" in rules
        assert "existential_intro" in rules

    def test_ei_from_conjunction(self):
        """P(A) & Q(A) ⊢ ∃x.P(x)"""
        assumptions = [parse_formula("P(A) & Q(A)")]
        goal = parse_formula("exists x. P(x)")
        result = solve_bayes(assumptions, goal, max_steps=3)
        assert result is not None

    def test_ei_witness_from_mp(self):
        """P(A), P(A) -> Q(A), ⊢ ∃x.Q(x)"""
        assumptions = [
            parse_formula("P(A)"),
            parse_formula("P(A) -> Q(A)"),
        ]
        goal = parse_formula("exists x. Q(x)")
        result = solve_bayes(assumptions, goal, max_steps=3)
        assert result is not None
        rules = [s.rule for s in result]
        assert "existential_intro" in rules


# ──────────────────────────────────────────────────────────────────────────────
# Mixed propositional + quantifier proofs
# ──────────────────────────────────────────────────────────────────────────────

class TestMixed:
    def test_propositional_unaffected(self):
        """Basic propositional proofs still work unchanged."""
        assumptions = [
            parse_formula("P"),
            parse_formula("P -> Q"),
            parse_formula("Q -> R"),
        ]
        goal = parse_formula("R")
        result = solve_bayes(assumptions, goal, max_steps=3)
        assert result is not None
        assert all(s.rule == "modus_ponens" for s in result)

    def test_propositional_atom_and_predicate_mixed(self):
        """P (propositional atom) alongside forall x.Q(x) ⊢ P & Q(A)"""
        assumptions = [
            parse_formula("P"),
            parse_formula("forall x. Q(x)"),
        ]
        goal = parse_formula("P & Q(A)")
        result = solve_bayes(assumptions, goal, max_steps=4)
        assert result is not None
        rules = [s.rule for s in result]
        assert "universal_instantiation" in rules
        assert "and_intro" in rules

    def test_quantified_chain_plus_conjunction(self):
        """∀x.(P(x)->Q(x)), P(A) & P(B) ⊢ Q(A) & Q(B)"""
        assumptions = [
            parse_formula("forall x. (P(x) -> Q(x))"),
            parse_formula("P(A) & P(B)"),
        ]
        goal = parse_formula("Q(A) & Q(B)")
        result = solve_bayes(assumptions, goal, max_steps=6)
        assert result is not None

    def test_ui_ei_chain(self):
        """∀x.(P(x)->Q(x)), P(A) ⊢ ∃y.Q(y)"""
        assumptions = [
            parse_formula("forall x. (P(x) -> Q(x))"),
            parse_formula("P(A)"),
        ]
        goal = parse_formula("exists y. Q(y)")
        result = solve_bayes(assumptions, goal, max_steps=4)
        assert result is not None
        rules = [s.rule for s in result]
        assert "universal_instantiation" in rules
        assert "modus_ponens" in rules
        assert "existential_intro" in rules


# ──────────────────────────────────────────────────────────────────────────────
# Failure cases
# ──────────────────────────────────────────────────────────────────────────────

class TestFailures:
    def test_wrong_predicate_name(self):
        """∀x.P(x) cannot prove Q(A) — wrong predicate."""
        assumptions = [parse_formula("forall x. P(x)")]
        goal = parse_formula("Q(A)")
        result = solve_bayes(assumptions, goal, max_steps=3)
        assert result is None

    def test_no_witness_for_exists(self):
        """∀x.P(x) — but goal is ∃x.Q(x) — no Q witness available."""
        assumptions = [parse_formula("forall x. P(x)")]
        goal = parse_formula("exists x. Q(x)")
        result = solve_bayes(assumptions, goal, max_steps=4)
        assert result is None

    def test_unrelated_propositional(self):
        """P alone cannot prove Q (propositional)."""
        result = solve_bayes(
            [parse_formula("P")], parse_formula("Q"), max_steps=3
        )
        assert result is None

    def test_wrong_constant(self):
        """∀x.P(x) gives P(A), but goal P(B) should work — different constant B
        is reachable only if B appears somewhere in the problem."""
        # B does appear in the goal, so terms = {x, B} and UI instantiates with B.
        assumptions = [parse_formula("forall x. P(x)")]
        goal = parse_formula("P(B)")
        result = solve_bayes(assumptions, goal, max_steps=2)
        assert result is not None  # B comes from the goal
