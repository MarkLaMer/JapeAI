from lark import Lark, Transformer, v_args

from .ast import Atom, Not, And, Imp, Or, Var, Predicate, ForAll, Exists

# ---------------------------------------------------------------------------
# Grammar
#
# Operator precedence (tightest → loosest):
#   atoms / predicates
#   negation        ~   ¬
#   quantifiers     ∀   ∃  (at unary level — bind smallest scope without parens)
#   conjunction     &   ∧
#   disjunction     |   ∨
#   implication     ->  →  (right-associative)
#
# Putting quantifiers at the unary level means:
#   ∃y.Q(y) ∨ ∃z.S(z)  parses as  (∃y.Q(y)) ∨ (∃z.S(z))   CHECK!
#   ∀y.(T(y)→Q(y))      parens give implication scope     CHECK!
#   ∀y.∀z.(body)         nested quantifiers work fine     CHECK!
# ---------------------------------------------------------------------------
GRAMMAR = r"""
?start: formula

?formula: implication
    | implication "->"  formula  -> imp
    | implication "\u2192" formula -> imp

?implication: disjunction

?disjunction: conjunction
    | disjunction "|"        conjunction -> or_op
    | disjunction "\u2228"   conjunction -> or_op

?conjunction: unary
    | conjunction "&"        unary -> and_op
    | conjunction "\u2227"   unary -> and_op

?unary: primary
    | "~"         unary -> not_op
    | "\u00AC"    unary -> not_op
    | "\u2200" VAR "." unary -> forall
    | "forall"    VAR "." unary -> forall
    | "\u2203" VAR "." unary -> exists
    | "exists"    VAR "." unary -> exists

?primary: predicate
    | propvar
    | "(" formula ")"

predicate : UNAME "(" varlist ")"
propvar   : UNAME
varlist   : VAR ("," VAR)*

UNAME : /[A-Z][A-Z0-9_]*/
VAR   : /[a-z][a-z0-9_]*/

%import common.WS
%ignore WS
"""


@v_args(inline=True)
class _Transformer(Transformer):

    # ── Propositional connectives ────────────────────────────────────────────
    def not_op(self, child):
        return Not(child)

    def and_op(self, left, right):
        return And(left, right)

    def or_op(self, left, right):
        return Or(left, right)

    def imp(self, left, right):
        return Imp(left, right)

    # ── FOL quantifiers ──────────────────────────────────────────────────────
    def forall(self, var_token, body):
        return ForAll(str(var_token), body)

    def exists(self, var_token, body):
        return Exists(str(var_token), body)

    # ── Atoms / predicates ───────────────────────────────────────────────────
    def propvar(self, token):
        return Atom(str(token))

    def predicate(self, name_token, varlist):
        return Predicate(str(name_token), tuple(varlist))

    # varlist is NOT inline — receives a list of VAR tokens
    @v_args(inline=False)
    def varlist(self, tokens):
        return [Var(str(t)) for t in tokens]


_parser = Lark(GRAMMAR, parser="lalr", transformer=_Transformer())


def parse_formula(text: str):
    return _parser.parse(text)
