from parser.parser import parse_formula

from csp.skeleton_csp import (
    CSPStats,
    candidate_formula_domain,
    solve_bounded_csp,
)


def test_bayes_formula_domain_reorder():
    assumptions = [parse_formula("P")]
    goal = parse_formula("Q")

    baseline = candidate_formula_domain(assumptions, goal, use_bayes=False)
    bayes = candidate_formula_domain(assumptions, goal, use_bayes=True)

    assert baseline != bayes
    assert bayes[0] == goal


def test_bayes_stats_comparison():
    assumptions = [
        parse_formula("P"),
        parse_formula("P -> Q"),
        parse_formula("Q -> R"),
        parse_formula("R -> S"),
        parse_formula("P -> (Q & R)"),
        parse_formula("(Q & R) -> S"),
    ]
    goal = parse_formula("S")

    baseline_stats = CSPStats()
    bayes_stats = CSPStats()

    baseline_solution = solve_bounded_csp(
        assumptions,
        goal,
        max_steps=3,
        use_bayes=False,
        stats=baseline_stats,
    )
    bayes_solution = solve_bounded_csp(
        assumptions,
        goal,
        max_steps=3,
        use_bayes=True,
        stats=bayes_stats,
    )

    assert baseline_solution is not None
    assert bayes_solution is not None
    assert baseline_stats.nodes_expanded > 0
    assert bayes_stats.nodes_expanded > 0

    # These prints show the comparison when running pytest -s.
    print("Baseline stats:", baseline_stats)
    print("Bayes stats:", bayes_stats)


def test_bayes_cutoff_triggers(monkeypatch):
    # Force aggressive cutoff behavior so we can observe pruning in a test.
    import csp.skeleton_csp as csp

    monkeypatch.setattr(csp, "BN_PARTIAL_CUTOFF_MIN_DOMAIN", 1)
    monkeypatch.setattr(csp, "BN_PARTIAL_SUCCESS_THRESHOLD", 0.99)

    assumptions = [parse_formula("P")]
    goal = parse_formula("Q")

    stats = CSPStats()
    result = solve_bounded_csp(
        assumptions,
        goal,
        max_steps=2,
        use_bayes=True,
        stats=stats,
    )

    assert result is None
    assert stats.bayes_cutoffs > 0
