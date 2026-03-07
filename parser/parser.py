from lark import Lark, Transformer, v_args

from parser.ast import Atom, Not, And, Imp

GRAMMER = r""" #lark syntax, don't ask
?start: formula #The parser should start by parsing a formula.
?formula: implication #Every formula is an implication-level expression

?implication: conjunction #Defines implication expressions
    | conjunction "->" implication -> imp  #Case: When this rule matches, call the transformer function imp()

?conjunction: unary
    | conjunction "&" unary -> and_op #Case: When this rule matches, call the transformer function and_op()

?unary: atom  # case 1: atom
    | "~" unary # case 2: neg
    | "(" formula ")" #case 3: parentheses

atom: /[A-Z][A-Z0-9_]*/

%import common.WS
%ignore WS #whitespace is allowed but irrelevant! :P
"""

@v_args(inline=True)
class FormmulaTransformer(Transformer):
    """
    Transforms parse trees produced by the Lark grammar into internal Abstract Syntax Tree (AST) objects representing propositional logic formulas.

    The parser first reads an input string (e.g. "(P & Q) -> R") and produces a parse tree according to the grammar rules.
    This transformer walks that parse tree and converts each matched rule into the corresponding Formula object.

    Each method corresponds to a grammar rule:
        atom    = Atom(name)
        not_op  = Not(child)
        and_op  = And(left, right)
        imp     = Imp(left, right)

    e.g.,
        Input string:
            "(P & Q) -> R"

        Parse tree:
            imp
             |─ and_op
             │   |─ atom(P)
             │   |─ atom(Q)
             |─ atom(R)

        Transformed AST:
            Imp(
                And(Atom("P"), Atom("Q")),
                Atom("R")
            )
    The resulting AST objects are used by the theorem prover for proof search, rule application, and proof tree construction.
    """
    
    def atom(self, token):
        return Atom(str(token))
    def not_op(self, child):
        return Not(child)
    def and_op(self, left, right):
        return And(left, right)
    def imp(self, left, right):
        return Imp(left, right)
    
_parser = Lark(GRAMMER, parser="lalr", transformer=FormmulaTransformer())

def parse_formula(text: str):
    return _parser.parse(text)

