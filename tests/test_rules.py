from parser.parser import parse_formula
from logic.rules import prove


def pf(text: str):
    return parse_formula(text)


def test_assumption():
    context = {pf("P")}
    goal = pf("P")
    assert prove(goal, context) is not None


def test_and_elim_from_context():
    context = {pf("P & Q")}
    goal = pf("P")
    assert prove(goal, context) is not None


def test_modus_ponens():
    context = {pf("P"), pf("P -> Q")}
    goal = pf("Q")
    assert prove(goal, context) is not None


def test_imp_intro():
    context = set()
    goal = pf("P -> P")
    assert prove(goal, context) is not None


def test_and_intro():
    context = {pf("P"), pf("Q")}
    goal = pf("P & Q")
    assert prove(goal, context) is not None


def test_chain_mp():
    context = {pf("P"), pf("P -> Q"), pf("Q -> R")}
    goal = pf("R")
    assert prove(goal, context) is not None


def test_failure_case():
    context = {pf("P")}
    goal = pf("Q")
    assert prove(goal, context) is None