from parser.parser import parse_formula
from csp.skeleton_csp import solve_bounded_csp


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

    for i, step in enumerate(result):
        print(f"  Step {i+1}: {step.rule} -> {step.formula}")


# Problem 1
def test_csp_and_intro():
    assumptions = [parse_formula("P"), parse_formula("Q")]
    goal = parse_formula("P & Q")

    result = solve_bounded_csp(assumptions, goal, max_steps=2)

    print_result(
        "prove_p_and_q_from_p_q",
        ["P", "Q"],
        "P & Q",
        result,
    )

    assert result is not None

# Problem 2
def test_csp_and_elim():
    assumptions = [parse_formula("P & Q")]
    goal = parse_formula("P")

    result = solve_bounded_csp(assumptions, goal, max_steps=2)

    print_result(
        "prove_p_from_p_and_q",
        ["P & Q"],
        "P",
        result,
    )

    assert result is not None


# Problem 3
def test_csp_modus_ponens():
    assumptions = [parse_formula("P"), parse_formula("P -> Q")]
    goal = parse_formula("Q")

    result = solve_bounded_csp(assumptions, goal, max_steps=2)

    print_result(
        "prove_q_from_p_imp_q",
        ["P", "P -> Q"],
        "Q",
        result,
    )

    assert result is not None


# Problem 4
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

    print_result(
        "unprovable_example",
        ["P"],
        "Q",
        result,
    )

    assert result is None