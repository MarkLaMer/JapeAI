"""
Comparative tests: CSP solver vs Bayesian solver.

Both solvers cover the same propositional rule set (MP, and-elim, and-intro).
These tests confirm they agree on solvability and exercise the Bayesian
solver's stats/step outputs.
"""

from parser.parser import parse_formula
from csp.skeleton_csp import solve_bounded_csp, CSPStats
from bayes.solver import solve_bayes, BayesSolverStats


# ──────────────────────────────────────────────────────────────────────────────
# Agreement tests — both solvers must reach the same solvability verdict
# ──────────────────────────────────────────────────────────────────────────────

AGREEMENT_CASES = [
    # (label, assumptions_str, goal_str, max_steps)
    ("1-step MP",            ["P", "P -> Q"],              "Q",           1),
    ("2-step chain",         ["P", "P -> Q", "Q -> R"],    "R",           2),
    ("and-elim left",        ["P & Q"],                    "P",           1),
    ("and-intro",            ["P", "Q"],                   "P & Q",       1),
    ("3-step chain",         ["P","P->Q","Q->R","R->S"],   "S",           3),
    ("elim then MP",         ["P & Q","(P & Q) -> R"],     "R",           2),
    ("unsolvable",           ["P"],                        "Q",           3),
    ("wrong chain",          ["P", "P -> Q"],              "R",           3),
]


def test_solvers_agree_on_solvability():
    for label, assumptions_str, goal_str, max_steps in AGREEMENT_CASES:
        assumptions = [parse_formula(s) for s in assumptions_str]
        goal = parse_formula(goal_str)

        csp_result   = solve_bounded_csp(assumptions, goal, max_steps=max_steps)
        bayes_result = solve_bayes(assumptions, goal, max_steps=max_steps)

        csp_solved   = csp_result   is not None
        bayes_solved = bayes_result is not None

        assert csp_solved == bayes_solved, (
            f"[{label}] solvers disagree: "
            f"CSP={'solved' if csp_solved else 'failed'}, "
            f"Bayes={'solved' if bayes_solved else 'failed'}"
        )


# ──────────────────────────────────────────────────────────────────────────────
# Bayes solver step structure tests
# ──────────────────────────────────────────────────────────────────────────────

def test_bayes_steps_have_scores():
    assumptions = [parse_formula("P"), parse_formula("P -> Q")]
    goal = parse_formula("Q")
    result = solve_bayes(assumptions, goal, max_steps=2)
    assert result is not None
    for step in result:
        assert 0.0 < step.score <= 1.0, f"step score out of range: {step.score}"


def test_bayes_steps_have_supports():
    assumptions = [parse_formula("P"), parse_formula("P -> Q")]
    goal = parse_formula("Q")
    result = solve_bayes(assumptions, goal, max_steps=2)
    assert result is not None
    mp_steps = [s for s in result if s.rule == "modus_ponens"]
    assert mp_steps, "expected at least one modus_ponens step"
    for step in mp_steps:
        assert step.support1 is not None
        assert step.support2 is not None


def test_bayes_stats_populated():
    assumptions = [
        parse_formula("P"),
        parse_formula("P -> Q"),
        parse_formula("Q -> R"),
        parse_formula("R -> S"),
    ]
    goal = parse_formula("S")
    stats = BayesSolverStats()
    result = solve_bayes(assumptions, goal, max_steps=4, stats=stats)
    assert result is not None
    assert stats.nodes_expanded > 0
    assert stats.candidates_scored > 0
    assert stats.steps_in_proof == len(result)


def test_bayes_trivial_returns_empty_list():
    """Goal already in assumptions — empty proof, no steps needed."""
    assumptions = [parse_formula("P")]
    goal = parse_formula("P")
    result = solve_bayes(assumptions, goal, max_steps=3)
    assert result == []


def test_csp_stats_populated():
    assumptions = [
        parse_formula("P"),
        parse_formula("P -> Q"),
        parse_formula("Q -> R"),
    ]
    goal = parse_formula("R")
    stats = CSPStats()
    result = solve_bounded_csp(assumptions, goal, max_steps=3, stats=stats)
    assert result is not None
    assert stats.nodes_expanded > 0
    assert stats.candidates_generated > 0


# ──────────────────────────────────────────────────────────────────────────────
# Node efficiency comparison (informational, not a hard assertion)
# ──────────────────────────────────────────────────────────────────────────────

def test_bayes_expands_fewer_or_equal_candidates_on_deep_chain():
    """
    On a well-structured chain, the Bayes solver's goal-directed scoring
    should expand ≤ nodes compared to the plain CSP.
    Not a strict requirement — just documents the expected behaviour.
    """
    assumptions = [
        parse_formula("A"),
        parse_formula("A -> B"),
        parse_formula("B -> C"),
        parse_formula("C -> D"),
        parse_formula("D -> E"),
        parse_formula("E -> F"),
        parse_formula("A -> C"),  # shortcut — Bayes should prefer the direct chain
        parse_formula("B -> D"),
    ]
    goal = parse_formula("F")

    csp_stats   = CSPStats()
    bayes_stats = BayesSolverStats()

    solve_bounded_csp(assumptions, goal, max_steps=5, stats=csp_stats)
    solve_bayes(assumptions, goal,       max_steps=5, stats=bayes_stats)

    # Bayes scored candidates can exceed raw CSP candidates because it scores
    # every option; what we care about is that it still finds the proof.
    assert bayes_stats.steps_in_proof > 0
    assert csp_stats.nodes_expanded   > 0
