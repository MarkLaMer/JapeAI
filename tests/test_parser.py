import pytest
from parser.ast import Atom, Not, And, Imp
from parser.parser import parse_formula


def test_parse_atom():
    assert parse_formula("P") == Atom("P")


def test_parse_negation():
    assert parse_formula("~P") == Not(Atom("P"))


def test_parse_conjunction():
    assert parse_formula("P & Q") == And(Atom("P"), Atom("Q"))


def test_parse_implication():
    assert parse_formula("P -> Q") == Imp(Atom("P"), Atom("Q"))


def test_parse_parentheses():
    assert parse_formula("(P & Q) -> R") == Imp(
        And(Atom("P"), Atom("Q")),
        Atom("R")
    )


def test_parse_precedence():
    assert parse_formula("~P & Q") == And(
        Not(Atom("P")),
        Atom("Q")
    )


def test_parse_right_associative_implication():
    assert parse_formula("P -> Q -> R") == Imp(
        Atom("P"),
        Imp(Atom("Q"), Atom("R"))
    )

def test_invalid_formula_double_and():
    with pytest.raises(Exception):
        parse_formula("P & & Q")


def test_invalid_formula_missing_operand():
    with pytest.raises(Exception):
        parse_formula("P ->")


def test_invalid_formula_unclosed_parenthesis():
    with pytest.raises(Exception):
        parse_formula("(P & Q")