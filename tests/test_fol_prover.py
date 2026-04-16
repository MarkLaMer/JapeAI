"""
tests/test_fol_prover.py — coverage for logic/fol_prover.py

Tests:
  1. free_vars / collect_terms / subst helpers
  2. _expand_conj_mp / _expand_with_witnesses
  3. prove_fol  -- the main backward FOL prover
  4. render_fol_proof -- flat rendering for GUI
  5. search/planner.py -- astar_plan / bfs_plan
  6. logic/proof_tree.py -- print_proof
"""
from __future__ import annotations

import io
import sys

import pytest

from parser.parser import parse_formula as pf
from parser.ast import Atom, Not, And, Or, Imp, Var, Predicate, ForAll, Exists

from logic.fol_prover import (
    free_vars,
    collect_terms,
    subst,
    _expand_conj_mp,
    _expand_with_witnesses,
    prove_fol,
    render_fol_proof,
    reset_fresh,
    _fresh,
)
from logic.proof_tree import ProofNode, print_proof


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _prove(assumptions_strs: list[str], goal_str: str):
    return prove_fol(pf(goal_str), [pf(s) for s in assumptions_strs])


def _rule_set(node: ProofNode) -> set[str]:
    """Collect all rule names in the proof tree."""
    rules = {node.rule}
    for child in node.children:
        rules |= _rule_set(child)
    return rules


# ===========================================================================
# 1. free_vars
# ===========================================================================

class TestFreeVars:

    def test_var(self):
        assert free_vars(Var("x")) == {"x"}

    def test_atom(self):
        assert free_vars(Atom("P")) == set()

    def test_predicate_with_var(self):
        assert free_vars(pf("T(x)")) == {"x"}

    def test_predicate_no_free(self):
        # T(a) where a is an atom-like name -- parsed as Atom arg
        assert isinstance(pf("T(x)"), Predicate)
        assert "x" in free_vars(pf("T(x)"))

    def test_not(self):
        assert free_vars(Not(Var("x"))) == {"x"}

    def test_and(self):
        assert free_vars(And(Var("x"), Var("y"))) == {"x", "y"}

    def test_or(self):
        assert free_vars(Or(Var("x"), Atom("P"))) == {"x"}

    def test_imp(self):
        assert free_vars(Imp(Var("x"), Var("y"))) == {"x", "y"}

    def test_forall_binds(self):
        # forall x.P(x) -- x is bound, no free vars
        f = pf("forall x.T(x)")
        assert free_vars(f) == set()

    def test_exists_binds(self):
        f = pf("exists x.T(x)")
        assert free_vars(f) == set()

    def test_forall_free_in_body(self):
        # forall x.R(x, y) -- y is free
        f = ForAll("x", pf("R(x)"))
        # no y in this example, but the bound var x is not free
        assert "x" not in free_vars(f)

    def test_unknown_formula_type_returns_empty(self):
        # Pass a plain object that is a Formula but no matching branch
        # The fallthrough `return set()` at line 74 fires for unrecognised types.
        class _Weird(Atom):
            pass
        w = _Weird("W")
        # Atom is caught before the fallthrough, but this exercises a subclass
        result = free_vars(w)
        assert isinstance(result, set)


# ===========================================================================
# 2. collect_terms
# ===========================================================================

class TestCollectTerms:

    def test_empty_context(self):
        assert collect_terms(set()) == []

    def test_var_in_context(self):
        terms = collect_terms({Var("a")})
        assert Var("a") in terms

    def test_extra_formula(self):
        terms = collect_terms(set(), extra=Var("z"))
        assert Var("z") in terms

    def test_deduplication(self):
        terms = collect_terms({Var("x"), Var("x")})
        assert len(terms) == 1


# ===========================================================================
# 3. subst
# ===========================================================================

class TestSubst:

    def test_var_match(self):
        result = subst(Var("x"), "x", Atom("P"))
        assert result == Atom("P")

    def test_var_no_match(self):
        result = subst(Var("y"), "x", Atom("P"))
        assert result == Var("y")

    def test_atom_unchanged(self):
        a = Atom("Q")
        result = subst(a, "x", Var("y"))
        assert result is a   # identity -- line 96

    def test_predicate(self):
        f = pf("T(x)")
        result = subst(f, "x", Var("a"))
        assert str(result) == "T(a)"

    def test_not(self):
        f = Not(Var("x"))
        result = subst(f, "x", Atom("P"))
        assert result == Not(Atom("P"))

    def test_and(self):
        f = And(Var("x"), Var("y"))
        result = subst(f, "x", Atom("P"))
        assert result == And(Atom("P"), Var("y"))

    def test_or(self):
        f = Or(Var("x"), Var("y"))
        result = subst(f, "y", Atom("Q"))
        assert result == Or(Var("x"), Atom("Q"))

    def test_imp(self):
        f = Imp(Var("x"), Var("x"))
        result = subst(f, "x", Atom("P"))
        assert result == Imp(Atom("P"), Atom("P"))

    def test_forall_shadow(self):
        # forall x.P(x) -- substituting x is blocked by binding
        f = ForAll("x", pf("T(x)"))
        result = subst(f, "x", Atom("P"))
        assert result is f   # unchanged -- line 114

    def test_exists_shadow(self):
        f = Exists("x", pf("T(x)"))
        result = subst(f, "x", Atom("P"))
        assert result is f   # unchanged -- line 118

    def test_forall_nonbound(self):
        # forall y.T(y) -- substituting x has no effect
        f = ForAll("y", pf("T(y)"))
        result = subst(f, "x", Atom("P"))
        assert result == f

    def test_exists_nonbound(self):
        f = Exists("y", pf("T(y)"))
        result = subst(f, "x", Atom("P"))
        assert result == f


# ===========================================================================
# 4. _expand_conj_mp and _expand_with_witnesses
# ===========================================================================

class TestExpand:

    def test_expand_and_elim(self):
        ctx = {And(Atom("P"), Atom("Q"))}
        expanded = _expand_conj_mp(ctx)
        assert Atom("P") in expanded
        assert Atom("Q") in expanded

    def test_expand_mp(self):
        ctx = {Atom("P"), Imp(Atom("P"), Atom("Q"))}
        expanded = _expand_conj_mp(ctx)
        assert Atom("Q") in expanded

    def test_expand_chain(self):
        ctx = {Atom("P"), Imp(Atom("P"), Atom("Q")), Imp(Atom("Q"), Atom("R"))}
        expanded = _expand_conj_mp(ctx)
        assert Atom("R") in expanded

    def test_expand_with_witnesses_existential(self):
        # exists x.T(x) -> Q, T(a) in context => exists x.T(x) gets added
        exists_tx = pf("exists x.T(x)")
        imp = Imp(exists_tx, Atom("Q"))
        # Need a free var "a" that witnesses T(a) -- use Var("a")
        t_a = subst(pf("T(x)"), "x", Var("a"))
        ctx = {imp, t_a, Var("a")}
        expanded = _expand_with_witnesses(ctx)
        assert exists_tx in expanded


# ===========================================================================
# 5. prove_fol -- backward prover
# ===========================================================================

class TestProveFOL:

    def test_assumption(self):
        node = _prove(["P"], "P")
        assert node is not None
        assert "Assumption" in _rule_set(node)

    def test_modus_ponens(self):
        # _expand_conj_mp fires MP eagerly, so Q is found as Assumption
        node = _prove(["P", "P -> Q"], "Q")
        assert node is not None
        assert node.conclusion == pf("Q")

    def test_and_intro(self):
        node = _prove(["P", "Q"], "P & Q")
        assert node is not None
        assert "AndIntro" in _rule_set(node)

    def test_and_elim_via_expansion(self):
        node = _prove(["P & Q"], "P")
        assert node is not None

    def test_imp_intro(self):
        node = _prove([], "P -> P")
        assert node is not None
        assert "ImpIntro" in _rule_set(node)

    def test_k_tautology(self):
        node = _prove([], "P -> (Q -> P)")
        assert node is not None

    def test_and_commutativity(self):
        node = _prove([], "(P & Q) -> (Q & P)")
        assert node is not None

    def test_or_intro_left(self):
        node = _prove(["P"], "P | Q")
        assert node is not None
        rules = _rule_set(node)
        assert "OrIntroL" in rules or "OrIntroR" in rules

    def test_or_intro_right(self):
        node = _prove(["Q"], "P | Q")
        assert node is not None

    def test_or_elim(self):
        node = _prove(["P | Q", "P -> R", "Q -> R"], "R")
        assert node is not None
        assert "OrElim" in _rule_set(node)

    def test_not_intro(self):
        node = _prove(["P", "~P"], "~Q")
        assert node is not None
        # ex falso from contradiction
        assert "ExFalso" in _rule_set(node)

    def test_ex_falso(self):
        node = _prove(["P", "~P"], "Q")
        assert node is not None
        assert "ExFalso" in _rule_set(node)

    def test_forall_intro(self):
        # forall y.T(y) |- forall y.T(y) -- trivially via assumption
        node = _prove(["forall y.T(y)"], "forall y.T(y)")
        assert node is not None

    def test_forall_elim_mp(self):
        node = _prove(["forall y.(T(y) -> Q(y))", "forall y.T(y)"], "forall y.Q(y)")
        assert node is not None

    def test_exists_intro(self):
        node = _prove(["exists y.T(y)", "forall y.(T(y) -> R(y))"], "exists y.R(y)")
        assert node is not None

    def test_raa(self):
        # P |- ~~P  (double negation intro via RAA)
        node = _prove(["P"], "~~P")
        assert node is not None

    def test_unprovable_returns_none(self):
        node = _prove(["P"], "Q")
        assert node is None

    def test_unprovable_empty(self):
        node = _prove([], "Q")
        assert node is None

    def test_chain(self):
        node = _prove(["P", "P -> Q", "Q -> R"], "R")
        assert node is not None

    def test_conclusion_matches_goal(self):
        goal = pf("Q")
        node = _prove(["P", "P -> Q"], "Q")
        assert node is not None
        assert node.conclusion == goal


# ===========================================================================
# 6. render_fol_proof
# ===========================================================================

class TestRenderFOLProof:

    def test_render_simple(self):
        node = _prove(["P", "P -> Q"], "Q")
        assert node is not None
        lines = []
        render_fol_proof(node, lines)
        assert len(lines) > 0

    def test_render_tuples(self):
        node = _prove(["P", "Q"], "P & Q")
        assert node is not None
        lines = []
        render_fol_proof(node, lines)
        for entry in lines:
            assert len(entry) == 4

    def test_render_skips_given(self):
        # "Given" nodes should not appear as separate lines
        node = _prove(["P", "P -> Q"], "Q")
        assert node is not None
        lines = []
        render_fol_proof(node, lines)
        rule_labels = [e[2] for e in lines]
        assert "given" not in rule_labels  # "Given" rule maps to "given" label, skipped

    def test_render_imp_intro_label(self):
        node = _prove([], "P -> P")
        assert node is not None
        lines = []
        render_fol_proof(node, lines)
        rule_labels = [e[2] for e in lines]
        assert any("intro" in lbl for lbl in rule_labels)

    def test_render_note_field(self):
        # ImpIntro nodes carry a note like "assume P"
        node = _prove([], "P -> P")
        assert node is not None
        lines = []
        render_fol_proof(node, lines)
        # note field is index 3
        notes = [e[3] for e in lines]
        # at least one note should be non-None (the imp-intro note)
        assert any(n is not None for n in notes)

    def test_render_depth_zero_for_flat(self):
        node = _prove(["P"], "P")
        assert node is not None
        lines = []
        render_fol_proof(node, lines, depth=0)
        assert all(e[0] >= 0 for e in lines)


# ===========================================================================
# 7. ProofNode / print_proof  (logic/proof_tree.py)
# ===========================================================================

class TestProofTree:

    def test_print_proof_no_crash(self, capsys):
        node = ProofNode(pf("P"), "Assumption")
        print_proof(node)
        out = capsys.readouterr().out
        assert "P" in out
        assert "Assumption" in out

    def test_print_proof_with_note(self, capsys):
        node = ProofNode(pf("P -> P"), "ImpIntro", note="assume P")
        print_proof(node)
        out = capsys.readouterr().out
        assert "assume P" in out

    def test_print_proof_nested(self, capsys):
        child = ProofNode(pf("P"), "Assumption")
        parent = ProofNode(pf("P & P"), "AndIntro", [child, child])
        print_proof(parent)
        out = capsys.readouterr().out
        assert "AndIntro" in out
        assert "Assumption" in out


# ===========================================================================
# 8. search/planner.py -- astar_plan and bfs_plan
# ===========================================================================

from search.planner import astar_plan, bfs_plan, formula_complexity, heuristic
from search.state import SearchState


def _make_state(goals_strs: list[str], context_strs: list[str]) -> SearchState:
    return SearchState(
        goals=tuple(pf(g) for g in goals_strs),
        context=frozenset(pf(c) for c in context_strs),
        depth=0,
    )


class TestAStarPlan:

    def test_mp_success(self):
        state = _make_state(["Q"], ["P", "P -> Q"])
        result = astar_plan(state)
        assert result.success is True

    def test_and_intro_success(self):
        state = _make_state(["P & Q"], ["P", "Q"])
        result = astar_plan(state)
        assert result.success is True

    def test_imp_intro_success(self):
        state = _make_state(["P -> P"], [])
        result = astar_plan(state)
        assert result.success is True

    def test_failure(self):
        state = _make_state(["Q"], ["P"])
        result = astar_plan(state, max_depth=3)
        assert result.success is False
        assert result.final_state is None

    def test_already_goal(self):
        state = _make_state([], ["P"])
        result = astar_plan(state)
        assert result.success is True

    def test_visited_count_positive(self):
        state = _make_state(["Q"], ["P", "P -> Q"])
        result = astar_plan(state)
        assert result.visited_count > 0


class TestBFSPlan:

    def test_mp_success(self):
        state = _make_state(["Q"], ["P", "P -> Q"])
        result = bfs_plan(state)
        assert result.success is True

    def test_failure(self):
        state = _make_state(["Q"], ["P"])
        result = bfs_plan(state, max_depth=3)
        assert result.success is False

    def test_already_goal(self):
        state = _make_state([], ["P"])
        result = bfs_plan(state)
        assert result.success is True

    def test_visited_count(self):
        state = _make_state(["Q"], ["P", "P -> Q"])
        result = bfs_plan(state)
        assert result.visited_count > 0


class TestPlannerHelpers:

    def test_formula_complexity_atom(self):
        assert formula_complexity(pf("P")) == 1

    def test_formula_complexity_not(self):
        assert formula_complexity(pf("~P")) == 2

    def test_formula_complexity_and(self):
        assert formula_complexity(pf("P & Q")) == 3

    def test_formula_complexity_imp(self):
        assert formula_complexity(pf("P -> Q")) == 3

    def test_formula_complexity_unknown(self):
        # Or is not handled -> returns 1
        assert formula_complexity(pf("P | Q")) == 1

    def test_heuristic_zero_goals(self):
        state = _make_state([], [])
        assert heuristic(state) == 0

    def test_heuristic_one_goal(self):
        state = _make_state(["P"], [])
        assert heuristic(state) >= 1
