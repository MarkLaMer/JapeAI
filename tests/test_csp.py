from parser.parser import parse_formula
from csp.skeleton_csp import solve_bounded_csp


def test_csp_modus_ponens():
    assumptions = [parse_formula("P"), parse_formula("P -> Q")]
    goal = parse_formula("Q")

    result = solve_bounded_csp(assumptions, goal, max_steps=2)
    assert result is not None


def test_csp_and_elim():
    assumptions = [parse_formula("P & Q")]
    goal = parse_formula("P")

    result = solve_bounded_csp(assumptions, goal, max_steps=2)
    assert result is not None


def test_csp_and_intro():
    assumptions = [parse_formula("P"), parse_formula("Q")]
    goal = parse_formula("P & Q")

    result = solve_bounded_csp(assumptions, goal, max_steps=2)
    assert result is not None


def test_csp_two_step_chain():
    assumptions = [
        parse_formula("P"),
        parse_formula("P -> Q"),
        parse_formula("Q -> R"),
    ]
    goal = parse_formula("R")

    result = solve_bounded_csp(assumptions, goal, max_steps=3)
    assert result is not None


def test_csp_failure():
    assumptions = [parse_formula("P")]
    goal = parse_formula("Q")

    result = solve_bounded_csp(assumptions, goal, max_steps=3)
    assert result is None