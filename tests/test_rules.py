# NOT YET IMPLEMENTED

# from parser.ast import Atom, And, Imp
# from logic.rules import assumption_rule, and_elim_left, modus_ponens


# def test_assumption_rule_success():
#     goal = Atom("P")
#     context = {Atom("P")}
#     assert assumption_rule(goal, context) is True


# def test_assumption_rule_failure():
#     goal = Atom("Q")
#     context = {Atom("P")}
#     assert assumption_rule(goal, context) is False


# def test_and_elim_left():
#     formula = And(Atom("P"), Atom("Q"))
#     assert and_elim_left(formula) == Atom("P")


# def test_modus_ponens():
#     context = {Atom("P"), Imp(Atom("P"), Atom("Q"))}
#     derived = modus_ponens(context)
#     assert Atom("Q") in derived