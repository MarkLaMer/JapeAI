from parser.ast import Atom, Not, And, Imp


def test_atom_str():
    assert str(Atom("P")) == "P"


def test_not_atom_str():
    assert str(Not(Atom("P"))) == "~P"


def test_not_complex_str():
    assert str(Not(And(Atom("P"), Atom("Q")))) == "~((P & Q))" or str(Not(And(Atom("P"), Atom("Q")))) == "~(P & Q)"


def test_and_str():
    assert str(And(Atom("P"), Atom("Q"))) == "(P & Q)"


def test_imp_str():
    assert str(Imp(Atom("P"), Atom("Q"))) == "(P -> Q)"


def test_formula_equality():
    assert Atom("P") == Atom("P")
    assert And(Atom("P"), Atom("Q")) == And(Atom("P"), Atom("Q"))