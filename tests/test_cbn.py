"""
tests/test_cbn.py — comprehensive test suite for the CBN / SCM / NL-solver layer.

Coverage:
  1. CausalGraph  — construction, traversal, cycle detection
  2. d-separation — Bayes-ball, all three path types (chain, fork, collider)
  3. graph_from_string  — parsing edge-list strings
  4. d_separation_trace — produces correct verdict AND a non-empty trace
  5. SCM construction   — Wet-Grass demo model
  6. SCM.sample         — forward sampling respects topological order
  7. SCM.abduction      — finds consistent noise assignments
  8. SCM.counterfactual — abduct → intervene → predict roundtrip
  9. SCM.marginal       — probabilities sum to 1
 10. NL solver          — each supported query type
"""
from __future__ import annotations

import pytest

from cbn.graph import CausalGraph, graph_from_string, d_separation_trace
from cbn.scm   import SCM, SCMVariable, NoiseVar, binary_noise, make_wet_grass_scm
from cbn.nl_solver import solve_causal, CausalStep


# ===========================================================================
# 1.  CausalGraph — construction and traversal
# ===========================================================================

def _wet_grass_graph() -> CausalGraph:
    return CausalGraph(
        nodes=["Season", "Rain", "Sprinkler", "WetGrass"],
        edges=[
            ("Season", "Rain"),
            ("Season", "Sprinkler"),
            ("Rain",   "WetGrass"),
            ("Sprinkler", "WetGrass"),
        ],
    )


def test_graph_nodes():
    g = _wet_grass_graph()
    assert g.nodes == {"Season", "Rain", "Sprinkler", "WetGrass"}


def test_graph_edges():
    g = _wet_grass_graph()
    assert ("Season", "Rain") in g.edges
    assert ("Rain",   "WetGrass") in g.edges


def test_graph_parents():
    g = _wet_grass_graph()
    assert g.parents("WetGrass") == {"Rain", "Sprinkler"}
    assert g.parents("Season")   == frozenset()


def test_graph_children():
    g = _wet_grass_graph()
    assert g.children("Season") == {"Rain", "Sprinkler"}
    assert g.children("WetGrass") == frozenset()


def test_graph_ancestors():
    g = _wet_grass_graph()
    assert g.ancestors("WetGrass") == {"Season", "Rain", "Sprinkler"}
    assert g.ancestors("Season")   == frozenset()


def test_graph_descendants():
    g = _wet_grass_graph()
    assert g.descendants("Season") == {"Rain", "Sprinkler", "WetGrass"}
    assert g.descendants("WetGrass") == frozenset()


def test_graph_markov_blanket():
    g = _wet_grass_graph()
    # MB(Rain) = parents(Rain) ∪ children(Rain) ∪ other-parents-of-children
    # parents = {Season}, children = {WetGrass}, other parents of WetGrass = {Sprinkler}
    assert g.markov_blanket("Rain") == {"Season", "WetGrass", "Sprinkler"}


def test_topological_sort_root_first():
    g = _wet_grass_graph()
    order = g.topological_sort()
    assert order.index("Season") < order.index("Rain")
    assert order.index("Season") < order.index("Sprinkler")
    assert order.index("Rain")   < order.index("WetGrass")
    assert order.index("Sprinkler") < order.index("WetGrass")


def test_graph_cycle_raises():
    with pytest.raises(ValueError, match="cycle"):
        CausalGraph(
            nodes=["A", "B", "C"],
            edges=[("A", "B"), ("B", "C"), ("C", "A")],
        )


def test_graph_self_loop_raises():
    with pytest.raises(ValueError, match="Self-loop"):
        CausalGraph(nodes=["A"], edges=[("A", "A")])


def test_graph_unknown_node_raises():
    with pytest.raises(ValueError, match="Unknown"):
        CausalGraph(nodes=["A"], edges=[("A", "B")])


def test_graph_method_unknown_node_raises():
    g = CausalGraph(nodes=["A", "B"], edges=[("A", "B")])
    with pytest.raises(ValueError, match="Unknown node"):
        g.parents("C")
    with pytest.raises(ValueError, match="Unknown node"):
        g.children("C")
    with pytest.raises(ValueError, match="Unknown node"):
        g.markov_blanket("C")


def test_d_separated_unknown_node_raises():
    g = CausalGraph(nodes=["A", "B"], edges=[("A", "B")])
    with pytest.raises(ValueError, match="Unknown graph node"):
        g.d_separated("A", "C")


def test_trace_unknown_node_raises():
    g = CausalGraph(nodes=["A", "B"], edges=[("A", "B")])
    with pytest.raises(ValueError, match="Unknown graph node"):
        d_separation_trace(g, "A", "C")


# ===========================================================================
# 2.  D-separation — Bayes-ball
# ===========================================================================

class TestDSeparation:
    """All six classic wet-grass d-separation assertions."""

    def setup_method(self):
        self.g = _wet_grass_graph()

    # --- Season → Rain → WetGrass  (chain) ---

    def test_chain_not_blocked_empty_Z(self):
        # Season and WetGrass are d-connected with Z=∅  (via Rain)
        assert self.g.d_separated("Season", "WetGrass") is False

    def test_chain_blocked_by_Rain(self):
        # Season ⊥ WetGrass | {Rain, Sprinkler}
        assert self.g.d_separated("Season", "WetGrass", {"Rain", "Sprinkler"}) is True

    # --- Season ← ? → Sprinkler  (fork) ---

    def test_fork_not_blocked_empty_Z(self):
        # Rain and Sprinkler are d-connected via Season fork
        assert self.g.d_separated("Rain", "Sprinkler") is False

    def test_fork_blocked_by_Season(self):
        # Rain ⊥ Sprinkler | Season
        assert self.g.d_separated("Rain", "Sprinkler", {"Season"}) is True

    # --- Rain → WetGrass ← Sprinkler  (collider) ---

    def test_collider_blocked_empty_Z(self):
        # Rain ⊥ Season | ∅  (collider WetGrass is closed)
        # Actually Rain and Season are d-connected via Season→Rain (direct edge)!
        # Let's use a graph without direct path.
        pass  # covered in separate graph below

    def test_collider_opens_when_conditioned(self):
        # Rain and Sprinkler are d-connected when conditioning on WetGrass (collider)
        assert self.g.d_separated("Rain", "Sprinkler", {"WetGrass"}) is False

    def test_collider_stays_blocked_without_conditioning(self):
        # Pure collider test: Rain ⊥ Sprinkler given Season (fork blocked)
        # but Rain and Sprinkler are independent only if Season is observed
        assert self.g.d_separated("Rain", "Sprinkler", {"Season"}) is True


def test_collider_pure():
    """Isolated collider A → C ← B with no other paths: A ⊥ B | ∅ but not | {C}."""
    g = CausalGraph(nodes=["A", "B", "C"], edges=[("A", "C"), ("B", "C")])
    assert g.d_separated("A", "B")        is True   # collider closed
    assert g.d_separated("A", "B", {"C"}) is False  # collider opens


def test_chain_pure():
    """Simple chain X → M → Y: X and Y are d-connected without conditioning."""
    g = CausalGraph(nodes=["X", "M", "Y"], edges=[("X", "M"), ("M", "Y")])
    assert g.d_separated("X", "Y")        is False  # connected
    assert g.d_separated("X", "Y", {"M"}) is True   # mediator blocks


def test_fork_pure():
    """Pure fork X ← Z → Y."""
    g = CausalGraph(nodes=["X", "Y", "Z"], edges=[("Z", "X"), ("Z", "Y")])
    assert g.d_separated("X", "Y")        is False  # connected via Z
    assert g.d_separated("X", "Y", {"Z"}) is True   # Z blocks


def test_collider_descendant_activates():
    """A → B ← C, B → D.  Conditioning on D (descendant of B) opens the collider."""
    g = CausalGraph(
        nodes=["A", "B", "C", "D"],
        edges=[("A", "B"), ("C", "B"), ("B", "D")],
    )
    assert g.d_separated("A", "C")        is True   # B closed, D not observed
    assert g.d_separated("A", "C", {"B"}) is False  # B observed → collider opens
    assert g.d_separated("A", "C", {"D"}) is False  # D observed → collider activates


def test_dsep_set_X_set_Y():
    """d_separated accepts sets, not just single strings."""
    g = CausalGraph(nodes=["A", "B", "C"], edges=[("A", "B"), ("B", "C")])
    assert g.d_separated({"A"}, {"C"}, set()) is False
    assert g.d_separated({"A"}, {"C"}, {"B"}) is True


# ===========================================================================
# 3.  graph_from_string
# ===========================================================================

def test_graph_from_string_arrow():
    g = graph_from_string("Season→Rain, Season→Sprinkler, Rain→WetGrass, Sprinkler→WetGrass")
    assert "Season" in g.nodes
    assert ("Season", "Rain") in g.edges


def test_graph_from_string_ascii_arrow():
    g = graph_from_string("A->B, B->C")
    assert ("A", "B") in g.edges
    assert ("B", "C") in g.edges


def test_graph_from_string_long_arrow():
    g = graph_from_string("X-->Y")
    assert ("X", "Y") in g.edges


# ===========================================================================
# 4.  d_separation_trace
# ===========================================================================

def test_trace_returns_correct_verdict_dsep():
    g = _wet_grass_graph()
    is_sep, moves = d_separation_trace(g, "Season", "WetGrass", {"Rain", "Sprinkler"})
    assert is_sep is True
    assert len(moves) > 0


def test_trace_returns_correct_verdict_connected():
    g = _wet_grass_graph()
    is_sep, moves = d_separation_trace(g, "Season", "WetGrass")
    assert is_sep is False
    # The "reached" move must be present
    assert any(m.action == "reached" for m in moves)


def test_trace_contains_blocked_moves():
    g = _wet_grass_graph()
    is_sep, moves = d_separation_trace(g, "Season", "WetGrass", {"Rain", "Sprinkler"})
    assert any(m.action == "blocked" for m in moves)


# ===========================================================================
# 5 & 6.  SCM — construction and forward sampling
# ===========================================================================

def test_scm_builds():
    scm = make_wet_grass_scm()
    assert set(scm.graph.nodes) == {"Season", "Rain", "Sprinkler", "WetGrass"}


def test_scm_sample_keys():
    scm = make_wet_grass_scm()
    vals = scm.sample()
    assert set(vals.keys()) == {"Season", "Rain", "Sprinkler", "WetGrass"}


def test_scm_sample_binary_values():
    scm = make_wet_grass_scm()
    for _ in range(20):
        vals = scm.sample()
        for v in vals.values():
            assert v in (0, 1)


def test_scm_wet_grass_determinism():
    """WetGrass must equal Rain OR Sprinkler."""
    scm = make_wet_grass_scm()
    for _ in range(50):
        vals = scm.sample()
        expected = 1 if (vals["Rain"] == 1 or vals["Sprinkler"] == 1) else 0
        assert vals["WetGrass"] == expected


def test_scm_intervention_overrides():
    """do(Season=1) should force Season=1 in every sample."""
    scm = make_wet_grass_scm()
    for _ in range(20):
        vals = scm.sample(interventions={"Season": 1})
        assert vals["Season"] == 1


def test_scm_sample_trace():
    scm = make_wet_grass_scm()
    vals, steps = scm.sample(trace=True)
    assert isinstance(steps, list)
    assert len(steps) == 4  # one per node
    for step in steps:
        assert step.kind in ("sample", "intervene")


def test_scm_unknown_intervention_raises():
    scm = make_wet_grass_scm()
    with pytest.raises(ValueError, match="interventions contains unknown variables"):
        scm.sample(interventions={"Unknown": 1})


def test_scm_unknown_noise_override_raises():
    scm = make_wet_grass_scm()
    with pytest.raises(ValueError, match="noise_override contains unknown variables"):
        scm.sample(noise_override={"Unknown": 0})


def test_scm_unknown_marginal_query_raises():
    scm = make_wet_grass_scm()
    with pytest.raises(ValueError, match="Unknown query node"):
        scm.marginal("Unknown")


def test_scm_unknown_abduction_observation_raises():
    scm = make_wet_grass_scm()
    with pytest.raises(ValueError, match="observations contains unknown variables"):
        scm.abduction({"Unknown": 1})


# ===========================================================================
# 7.  SCM.abduction
# ===========================================================================

def test_abduction_finds_consistent_noise():
    scm = make_wet_grass_scm()
    # Observe WetGrass=1; there must be at least one consistent noise assignment
    consistent = scm.abduction({"WetGrass": 1})
    assert len(consistent) > 0
    # All returned assignments must have WetGrass=1 under replay
    for noise, _ in consistent:
        vals = scm.sample(noise_override=noise)
        assert vals["WetGrass"] == 1


def test_abduction_dry_grass_consistent():
    scm = make_wet_grass_scm()
    consistent = scm.abduction({"WetGrass": 0})
    assert len(consistent) > 0
    for noise, _ in consistent:
        vals = scm.sample(noise_override=noise)
        assert vals["WetGrass"] == 0


def test_abduction_trace_steps():
    scm = make_wet_grass_scm()
    consistent = scm.abduction({"Season": 1})
    assert consistent
    _, steps = consistent[0]
    assert len(steps) > 0
    assert all(s.kind == "abduct" for s in steps)


# ===========================================================================
# 8.  SCM.counterfactual
# ===========================================================================

def test_counterfactual_winter_to_summer():
    """
    Observe Season=1 (winter), then ask: if Season had been 0 (summer), what
    would Rain be?

    Under the model: Rain=1 iff (Season=winter AND U_Rain=1).
    If we force Season=0, Rain becomes 0 regardless of U_Rain.
    """
    scm = make_wet_grass_scm()
    # Observe winter and rain
    obs = {"Season": 1, "Rain": 1}
    do  = {"Season": 0}  # intervene to summer
    results = scm.counterfactual(obs, do)
    assert len(results) > 0
    # In the counterfactual world with Season=0, Rain should be 0 (model design)
    for noise, cf_vals, _ in results:
        assert cf_vals["Season"] == 0  # intervention took effect
        assert cf_vals["Rain"] == 0    # Summer → no rain in this model


# ===========================================================================
# 9.  SCM.marginal
# ===========================================================================

def test_marginal_sums_to_one():
    scm = make_wet_grass_scm()
    dist = scm.marginal("WetGrass")
    total = sum(dist.values())
    assert abs(total - 1.0) < 1e-9


def test_marginal_intervention_summer():
    """P(Rain=1 | do(Season=0)) should be 0 (summer → no rain in this model)."""
    scm = make_wet_grass_scm()
    dist = scm.marginal("Rain", interventions={"Season": 0})
    assert dist.get(1, 0.0) == pytest.approx(0.0)


def test_marginal_intervention_winter():
    """P(Rain=1 | do(Season=1)) should be 0.8 (noise bias)."""
    scm = make_wet_grass_scm()
    dist = scm.marginal("Rain", interventions={"Season": 1})
    assert dist.get(1, 0.0) == pytest.approx(0.8)


# ===========================================================================
# 10.  NL solver — each supported query type
# ===========================================================================

WG_MODEL = "Season→Rain, Season→Sprinkler, Rain→WetGrass, Sprinkler→WetGrass"


def _has_result(steps: list[CausalStep] | None) -> bool:
    return steps is not None and any(s.kind == "result" for s in steps)


def _has_error(steps: list[CausalStep] | None) -> bool:
    return steps is not None and any(s.kind == "error" for s in steps)


def test_nl_dsep_independent():
    steps = solve_causal(WG_MODEL, "Is Season independent of WetGrass given {Rain, Sprinkler}?")
    assert _has_result(steps)
    result_step = next(s for s in steps if s.kind == "result")
    assert "d-separated" in result_step.text


def test_nl_dsep_connected():
    steps = solve_causal(WG_MODEL, "Is Season independent of WetGrass?")
    assert _has_result(steps)
    result_step = next(s for s in steps if s.kind == "result")
    assert "d-connected" in result_step.text


def test_nl_dsep_collider_opens():
    steps = solve_causal(WG_MODEL, "Is Rain independent of Sprinkler given WetGrass?")
    assert _has_result(steps)
    result_step = next(s for s in steps if s.kind == "result")
    assert "d-connected" in result_step.text  # collider opens


def test_nl_dsep_fork_blocked():
    steps = solve_causal(WG_MODEL, "Is Rain d-separated from Sprinkler given Season?")
    assert _has_result(steps)
    result_step = next(s for s in steps if s.kind == "result")
    assert "d-separated" in result_step.text


def test_nl_cause_yes():
    steps = solve_causal(WG_MODEL, "Does Season cause WetGrass?")
    assert _has_result(steps)
    result_step = next(s for s in steps if s.kind == "result")
    assert "YES" in result_step.text


def test_nl_cause_no():
    steps = solve_causal(WG_MODEL, "Does WetGrass cause Season?")
    assert _has_result(steps)
    result_step = next(s for s in steps if s.kind == "result")
    assert "NO" in result_step.text


def test_nl_parents_query():
    steps = solve_causal(WG_MODEL, "What are the parents of WetGrass?")
    assert _has_result(steps)
    result_step = next(s for s in steps if s.kind == "result")
    assert "Rain" in result_step.text
    assert "Sprinkler" in result_step.text


def test_nl_children_query():
    steps = solve_causal(WG_MODEL, "What are the children of Season?")
    assert _has_result(steps)
    result_step = next(s for s in steps if s.kind == "result")
    assert "Rain" in result_step.text
    assert "Sprinkler" in result_step.text


def test_nl_ancestors_query():
    steps = solve_causal(WG_MODEL, "What are the ancestors of WetGrass?")
    assert _has_result(steps)
    result_step = next(s for s in steps if s.kind == "result")
    assert "Season" in result_step.text


def test_nl_descendants_query():
    steps = solve_causal(WG_MODEL, "What are the descendants of Season?")
    assert _has_result(steps)
    result_step = next(s for s in steps if s.kind == "result")
    assert "WetGrass" in result_step.text


def test_nl_markov_blanket():
    steps = solve_causal(WG_MODEL, "What is the Markov blanket of Rain?")
    assert _has_result(steps)
    result_step = next(s for s in steps if s.kind == "result")
    assert "Season" in result_step.text or "WetGrass" in result_step.text


def test_nl_topological_order():
    steps = solve_causal(WG_MODEL, "What is the topological order?")
    assert _has_result(steps)
    result_step = next(s for s in steps if s.kind == "result")
    assert "Season" in result_step.text


def test_nl_marginal():
    steps = solve_causal(WG_MODEL, "What is the probability of WetGrass=1?")
    assert _has_result(steps)
    result_step = next(s for s in steps if s.kind == "result")
    assert "WetGrass=1" in result_step.text


def test_nl_marginal_with_intervention():
    steps = solve_causal(WG_MODEL, "What is the probability of WetGrass=1 given do(Season=1)?")
    assert _has_result(steps)
    result_step = next(s for s in steps if s.kind == "result")
    assert "WetGrass=1" in result_step.text


def test_nl_counterfactual():
    steps = solve_causal(WG_MODEL, "If Season=0, what would WetGrass be?")
    # Should at least run without crashing and produce steps
    assert steps is not None
    assert len(steps) > 0


def test_nl_parse_error_graceful():
    steps = solve_causal("NOT_A_VALID_MODEL!!!", "some query")
    # Should return an error step, not raise
    assert steps is not None


def test_nl_unknown_query_fallback():
    """An unrecognised query should return some steps (may be error or fallback)."""
    steps = solve_causal(WG_MODEL, "XYZ ZZZ ???")
    assert steps is not None


# ===========================================================================
# 11.  NoiseVar helpers
# ===========================================================================

def test_noise_var_domain_mismatch():
    with pytest.raises(ValueError, match="same length"):
        NoiseVar("U", [0, 1], [1.0])


def test_noise_var_probs_not_sum_to_one():
    with pytest.raises(ValueError, match="sum to 1"):
        NoiseVar("U", [0, 1], [0.3, 0.3])


def test_binary_noise_values():
    n = binary_noise("U", p_true=1.0)
    assert n.sample() == 1


def test_noise_most_likely():
    n = NoiseVar("U", ["a", "b", "c"], [0.1, 0.7, 0.2])
    assert n.most_likely() == "b"


# ===========================================================================
# 12.  Edge cases
# ===========================================================================

def test_single_node_graph():
    g = CausalGraph(nodes=["A"], edges=[])
    assert g.parents("A") == frozenset()
    assert g.children("A") == frozenset()
    assert g.topological_sort() == ["A"]


def test_dsep_same_node():
    """d_separated(X, X, Z) with X ∉ Z: trivially d-connected (trivial path of length 0)."""
    g = _wet_grass_graph()
    # X = Y = "Rain" with no conditioning — the ball immediately reaches Y
    assert g.d_separated("Rain", "Rain") is False


def test_dsep_non_existent_node_raises():
    """Unknown query nodes should raise a clear validation error."""
    g = _wet_grass_graph()
    with pytest.raises(ValueError, match="Unknown graph node"):
        g.d_separated("Season", "Fog")


def test_scm_mismatch_raises():
    g = CausalGraph(nodes=["A", "B"], edges=[("A", "B")])
    # Only provide variable for A, not B
    with pytest.raises(ValueError, match="missing variables"):
        SCM(graph=g, variables={
            "A": SCMVariable("A", [], lambda pa, u: u, binary_noise("UA"), [0, 1]),
        })


# ===========================================================================
# 13.  logic_causal — CBN/SCM-backed natural deduction
# ===========================================================================

from cbn.logic_causal import solve_logic_causal
from parser.parser import parse_formula as pf2


def _lc(assumptions_strs: list[str], goal_str: str) -> list[str] | None:
    """Helper: parse strings and call solve_logic_causal."""
    return solve_logic_causal(
        [pf2(s) for s in assumptions_strs],
        pf2(goal_str),
    )


class TestLogicCausal:
    """solve_logic_causal -- Bayesian best-first FOL proof solver."""

    def _rules(self, result):
        """Collect all rule names from a flat or nested FOLProofStep list."""
        from csp.fol_csp import (
            FOLStep, FOLImpIntroStep, FOLForAllIntroStep,
            FOLExistsElimStep, FOLOrElimStep,
        )
        rules = []
        for s in result:
            if isinstance(s, FOLStep):
                rules.append(s.rule)
            elif hasattr(s, "rule"):
                rules.append(s.rule)
                if hasattr(s, "sub_steps"):
                    rules.extend(self._rules(list(s.sub_steps)))
        return rules

    def _conclusions(self, result):
        """Collect all conclusion formula strings from a step list."""
        conclusions = []
        for s in result:
            conclusions.append(str(s.formula))
            if hasattr(s, "sub_steps"):
                conclusions.extend(self._conclusions(list(s.sub_steps)))
        return conclusions

    def test_modus_ponens_simple(self):
        result = _lc(["P", "P -> Q"], "Q")
        assert result is not None
        rules = self._rules(result)
        assert "mp" in rules

    def test_mp_chain_two_steps(self):
        result = _lc(["P", "P -> Q", "Q -> R"], "R")
        assert result is not None
        conclusions = self._conclusions(result)
        assert "Q" in conclusions
        assert "R" in conclusions

    def test_mp_chain_three_steps(self):
        result = _lc(["P", "P -> Q", "Q -> R", "R -> S"], "S")
        assert result is not None
        conclusions = self._conclusions(result)
        assert "S" in conclusions

    def test_and_elim_left(self):
        result = _lc(["P & Q"], "P")
        assert result is not None
        rules = self._rules(result)
        assert any("and_elim" in r for r in rules)

    def test_and_elim_right(self):
        result = _lc(["P & Q"], "Q")
        assert result is not None
        rules = self._rules(result)
        assert any("and_elim" in r for r in rules)

    def test_and_elim_then_mp(self):
        result = _lc(["P & Q", "(P & Q) -> R"], "R")
        assert result is not None
        rules = self._rules(result)
        assert "mp" in rules

    def test_and_intro(self):
        result = _lc(["P", "Q"], "P & Q")
        assert result is not None
        rules = self._rules(result)
        assert "and_intro" in rules

    def test_already_known(self):
        """Goal is directly in assumptions -- no steps needed."""
        result = _lc(["P", "Q"], "P")
        assert result is not None
        assert len(result) == 0

    def test_unprovable_returns_none(self):
        result = _lc(["P"], "Q")
        assert result is None

    def test_unprovable_empty_assumptions(self):
        result = _lc([], "Q")
        assert result is None

    def test_steps_are_fol_proof_steps(self):
        """solve_logic_causal now returns FOLProofStep objects, not strings."""
        from csp.fol_csp import FOLStep
        result = _lc(["P", "P -> Q"], "Q")
        assert result is not None
        assert len(result) > 0
        # Top-level result should be FOLProofStep instances
        for s in result:
            assert hasattr(s, "formula")
            assert hasattr(s, "rule")

    def test_step_contains_conclusion(self):
        """The final derived formula should be the goal."""
        result = _lc(["P", "P -> Q", "Q -> R"], "R")
        assert result is not None
        conclusions = self._conclusions(result)
        assert "R" in conclusions

    def test_imp_intro_tautology(self):
        """P -> P should be provable via imp-intro with no assumptions."""
        result = _lc([], "P -> P")
        assert result is not None
        rules = self._rules(result)
        assert "imp_intro" in rules

    def test_and_commutativity(self):
        """(P & Q) -> (Q & P) tautology via imp-intro."""
        result = _lc([], "(P & Q) -> (Q & P)")
        assert result is not None


def test_logic_causal_is_independent_from_csp(monkeypatch):
    from csp import fol_csp
    from csp.fol_csp import FOLStep

    def _boom(*args, **kwargs):
        raise AssertionError("CBN solver delegated to CSP")

    monkeypatch.setattr(fol_csp, "solve_fol_csp", _boom)

    result = _lc(["P", "P -> Q"], "Q")
    assert result is not None
    assert any(isinstance(step, FOLStep) and step.rule == "mp" for step in result)


class TestLogicCausalCBNStructure:
    """Verify the causal graph and d-separation filter work correctly."""

    def test_graph_builds_from_imp(self):
        """The causal graph extracted from P->Q should have edge P -> Q."""
        from cbn.logic_causal import _build_causal_graph
        from parser.parser import parse_formula
        g, _ = _build_causal_graph(
            [parse_formula("P"), parse_formula("P -> Q")], parse_formula("Q"))
        assert ("P", "Q") in g.edges

    def test_graph_topo_order_respected(self):
        """Topological sort must put P before Q before R for P->Q->R chain."""
        from cbn.logic_causal import _build_causal_graph
        from parser.parser import parse_formula
        g, _ = _build_causal_graph(
            [parse_formula("P"), parse_formula("P -> Q"), parse_formula("Q -> R")],
            parse_formula("R"))
        order = g.topological_sort()
        assert order.index("P") < order.index("Q") < order.index("R")

    def test_dsep_filter_keeps_relevant(self):
        """D-separation filter must keep formulas on the path to the goal."""
        from cbn.logic_causal import _build_causal_graph, _dsep_filter, _atom_nodes
        from cbn.graph import CausalGraph
        from parser.ast import Atom
        from parser.parser import parse_formula
        assumptions = [parse_formula("P"), parse_formula("P -> Q")]
        goal = parse_formula("Q")
        graph, _ = _build_causal_graph(assumptions, goal)
        domain = {Atom("P"), Atom("Q")}
        assumption_atoms = {"P"}
        goal_atoms = {"Q"}
        filtered = _dsep_filter(domain, graph, assumption_atoms, goal_atoms)
        # Q must be kept -- it is the goal
        assert Atom("Q") in filtered

    def test_dsep_filter_not_empty(self):
        """D-separation filter must never return an empty domain."""
        from cbn.logic_causal import _build_causal_graph, _dsep_filter
        from parser.ast import Atom
        from parser.parser import parse_formula
        assumptions = [parse_formula("P"), parse_formula("P -> Q")]
        goal = parse_formula("Q")
        graph, _ = _build_causal_graph(assumptions, goal)
        domain = {Atom("P"), Atom("Q"), Atom("R")}
        filtered = _dsep_filter(domain, graph, {"P"}, {"Q"})
        assert len(filtered) > 0
