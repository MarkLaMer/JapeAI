from lark import Lark, Transformer, v_args

from .ast import Atom, Not, And, Imp, Predicate, ForAll, Exists

# Grammar covers propositional logic + first-order quantifiers.
#
# Precedence (low → high):
#   quantifiers  <  implication  <  conjunction  <  negation  <  primary
#
# Terminals:
#   NAME  — /[A-Z][A-Z0-9_]*/   propositional atoms and predicate/constant names
#   VAR   — /[a-z][a-z0-9_]*/   first-order variables (bound by ∀/∃)
#
# Anonymous terminals ("forall", "exists", "->", "&", "~", "(", ")", ",", ".")
# are filtered out of the transformer args by Lark automatically.

GRAMMAR = r"""
?start: formula

?formula: implication
    | "forall" VAR "." formula  -> forall_op
    | "exists" VAR "." formula  -> exists_op

?implication: conjunction
    | conjunction "->" implication  -> imp

?conjunction: unary
    | conjunction "&" unary  -> and_op

?unary: primary
    | "~" unary  -> not_op

?primary: "(" formula ")"
    | NAME "(" arglist ")"  -> predicate
    | NAME                  -> atom

arglist: term ("," term)*

?term: VAR   -> var_term
     | NAME  -> const_term

NAME: /[A-Z][A-Z0-9_]*/
VAR:  /[a-z][a-z0-9_]*/

%import common.WS
%ignore WS
"""


@v_args(inline=True)
class FormulaTransformer(Transformer):
    """
    Transforms a Lark parse tree into internal AST objects.

    Propositional rules (unchanged from original):
      atom        →  Atom(name)
      not_op      →  Not(child)
      and_op      →  And(left, right)
      imp         →  Imp(left, right)

    First-order rules (new):
      predicate   →  Predicate(name, args)
      forall_op   →  ForAll(var, body)
      exists_op   →  Exists(var, body)
      var_term    →  str  (variable name)
      const_term  →  str  (constant name)
    """

    # ── propositional ─────────────────────────────────────────────────────

    def atom(self, token):
        return Atom(str(token))

    def not_op(self, child):
        return Not(child)

    def and_op(self, left, right):
        return And(left, right)

    def imp(self, left, right):
        return Imp(left, right)

    # ── first-order ───────────────────────────────────────────────────────

    def predicate(self, name, args):
        # `args` is the list returned by arglist()
        return Predicate(str(name), tuple(args))

    def arglist(self, *terms):
        # Anonymous "," separators are filtered by Lark; only term results remain.
        return list(terms)

    def var_term(self, token):
        return str(token)

    def const_term(self, token):
        return str(token)

    def forall_op(self, var, body):
        return ForAll(str(var), body)

    def exists_op(self, var, body):
        return Exists(str(var), body)


_parser = Lark(GRAMMAR, parser="lalr", transformer=FormulaTransformer())


def parse_formula(text: str) -> "Formula":
    return _parser.parse(text)
