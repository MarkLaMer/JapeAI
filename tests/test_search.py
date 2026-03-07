# NOT YET IMPLEMENTED

# from parser.ast import Atom, And, Imp
# from search.prover import prove


# def test_prove_assumption():
#     proof = prove(goal=Atom("P"), assumptions={Atom("P")})
#     assert proof is not None


# def test_prove_and_elim():
#     proof = prove(goal=Atom("P"), assumptions={And(Atom("P"), Atom("Q"))})
#     assert proof is not None


# def test_prove_modus_ponens():
#     proof = prove(
#         goal=Atom("Q"),
#         assumptions={Atom("P"), Imp(Atom("P"), Atom("Q"))}
#     )
#     assert proof is not None


# def test_unprovable_goal():
#     proof = prove(goal=Atom("Q"), assumptions={Atom("P")})
#     assert proof is None