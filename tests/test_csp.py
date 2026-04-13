from parser.parser import parse_formula
from csp.skeleton_csp import (
    solve_bounded_csp,
    solve_csp,
    CSPImpIntroStep,
    print_csp_proof,
)


def print_result(name, assumptions, goal, result):
    """
    Helper to print experiment results so we can
    easily copy them into the report tables.
    """

    print("\n----------------------------------")
    print("Problem:", name)
    print("Assumptions:", assumptions)
    print("Goal:", goal)

    if result is None:
        print("Result: failure")
        return

    print("Result: success")
    print("Steps found:", len(result))
    print_csp_proof(result)


# ────────────────────────────────────────────────
# Original forward-rule tests (unchanged semantics)
# ────────────────────────────────────────────────

def test_csp_and_intro():
    assumptions = [parse_formula("P"), parse_formula("Q")]
    goal = parse_formula("P & Q")

    result = solve_bounded_csp(assumptions, goal, max_steps=2)

    print_result("prove_p_and_q_from_p_q", ["P", "Q"], "P & Q", result)
    assert result is not None


def test_csp_and_elim():
    assumptions = [parse_formula("P & Q")]
    goal = parse_formula("P")

    result = solve_bounded_csp(assumptions, goal, max_steps=2)

    print_result("prove_p_from_p_and_q", ["P & Q"], "P", result)
    assert result is not None


def test_csp_modus_ponens():
    assumptions = [parse_formula("P"), parse_formula("P -> Q")]
    goal = parse_formula("Q")

    result = solve_bounded_csp(assumptions, goal, max_steps=2)

    print_result("prove_q_from_p_imp_q", ["P", "P -> Q"], "Q", result)
    assert result is not None


def test_csp_two_step_chain():
    assumptions = [
        parse_formula("P"),
        parse_formula("P -> Q"),
        parse_formula("Q -> R"),
    ]
    goal = parse_formula("R")

    result = solve_bounded_csp(assumptions, goal, max_steps=3)

    print_result(
        "prove_r_from_p_imp_q_q_imp_r",
        ["P", "P -> Q", "Q -> R"],
        "R",
        result,
    )
    assert result is not None


def test_csp_failure():
    assumptions = [parse_formula("P")]
    goal = parse_formula("Q")

    result = solve_bounded_csp(assumptions, goal, max_steps=3)

    print_result("unprovable_example", ["P"], "Q", result)
    assert result is None


# ────────────────────────────────────────────────
# Implication Introduction tests
# ────────────────────────────────────────────────

def test_csp_imp_intro_reflexive():
    """Prove P -> P from no assumptions (identity tautology)."""
    assumptions: list = []
    goal = parse_formula("P -> P")

    result = solve_csp(assumptions, goal)

    print_result("prove_p_imp_p", [], "P -> P", result)
    assert result is not None
    # Should be a single CSPImpIntroStep
    assert len(result) == 1
    assert isinstance(result[0], CSPImpIntroStep)
    assert result[0].rule == "imp_intro"


def test_csp_imp_intro_weakening():
    """Prove P -> (Q -> P) from no assumptions (K tautology)."""
    assumptions: list = []
    goal = parse_formula("P -> (Q -> P)")

    result = solve_csp(assumptions, goal)

    print_result("prove_p_imp_q_imp_p", [], "P -> (Q -> P)", result)
    assert result is not None


def test_csp_imp_intro_with_context():
    """Prove Q -> (P & Q) given P is already known."""
    assumptions = [parse_formula("P")]
    goal = parse_formula("Q -> (P & Q)")

    result = solve_csp(assumptions, goal)

    print_result("prove_q_imp_p_and_q_from_p", ["P"], "Q -> (P & Q)", result)
    assert result is not None


def test_csp_imp_intro_and_commute():
    """Prove (P & Q) -> (Q & P) from no assumptions."""
    assumptions: list = []
    goal = parse_formula("(P & Q) -> (Q & P)")

    result = solve_csp(assumptions, goal)

    print_result("prove_and_commute", [], "(P & Q) -> (Q & P)", result)
    assert result is not None


def test_csp_chain_from_imp_intro():
    """Prove P -> R given (P -> Q) -> R is an assumption and P -> Q is provable."""
    # From P->Q (assumption) and (P->Q)->R (assumption), prove P->R.
    assumptions = [
        parse_formula("P -> Q"),
        parse_formula("(P -> Q) -> R"),
    ]
    goal = parse_formula("P -> R")

    result = solve_csp(assumptions, goal)

    print_result("prove_p_imp_r_via_chain", ["P -> Q", "(P -> Q) -> R"], "P -> R", result)
    assert result is not None


# ────────────────────────────────────────────────
# Longer chain tests
# ────────────────────────────────────────────────

def test_csp_three_step_chain():
    """Prove S from a four-link MP chain."""
    assumptions = [
        parse_formula("P"),
        parse_formula("P -> Q"),
        parse_formula("Q -> R"),
        parse_formula("R -> S"),
    ]
    goal = parse_formula("S")

    result = solve_csp(assumptions, goal)

    print_result("prove_s_four_link_chain", ["P", "P->Q", "Q->R", "R->S"], "S", result)
    assert result is not None


def test_csp_five_step_chain():
    """Prove U from a six-link MP chain."""
    assumptions = [
        parse_formula("P"),
        parse_formula("P -> Q"),
        parse_formula("Q -> R"),
        parse_formula("R -> S"),
        parse_formula("S -> U"),
    ]
    goal = parse_formula("U")

    result = solve_csp(assumptions, goal)

    print_result("prove_u_six_link_chain", ["P", "P->Q", "Q->R", "R->S", "S->U"], "U", result)
    assert result is not None


def test_csp_iterative_deepening_finds_shortest():
    """solve_csp should find the 1-step proof, not a longer redundant one."""
    assumptions = [parse_formula("P"), parse_formula("Q")]
    goal = parse_formula("P & Q")

    result = solve_csp(assumptions, goal)

    print_result("prove_p_and_q_shortest", ["P", "Q"], "P & Q", result)
    assert result is not None
    # Shortest proof is 1 step (AND-INTRO)
    assert len(result) == 1


# ────────────────────────────────────────────────
# Internal PDDL planner tests
# ────────────────────────────────────────────────

def test_internal_planner_mp():
    from planning.internal_planner import plan_forward
    assumptions = [parse_formula("P"), parse_formula("P -> Q")]
    goal = parse_formula("Q")

    result = plan_forward(assumptions, goal)
    assert result is not None
    print("\n[internal planner] MP plan:", result)


def test_internal_planner_chain():
    from planning.internal_planner import plan_forward
    assumptions = [
        parse_formula("P"),
        parse_formula("P -> Q"),
        parse_formula("Q -> R"),
    ]
    goal = parse_formula("R")

    result = plan_forward(assumptions, goal)
    assert result is not None
    print("\n[internal planner] chain plan:", result)


def test_internal_planner_imp_intro():
    from planning.internal_planner import plan_forward
    assumptions: list = []
    goal = parse_formula("P -> P")

    result = plan_forward(assumptions, goal)
    assert result is not None
    print("\n[internal planner] P->P plan:", result)


def test_internal_planner_failure():
    from planning.internal_planner import plan_forward
    assumptions = [parse_formula("P")]
    goal = parse_formula("Q")

    result = plan_forward(assumptions, goal, max_depth=5)
    assert result is None
    print("\n[internal planner] correctly returned None for unprovable P |- Q")
