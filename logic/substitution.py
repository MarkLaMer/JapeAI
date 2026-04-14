"""
Substitution utilities for first-order formulas.

substitute(φ, var, term) replaces every FREE occurrence of variable `var`
with the string `term` throughout formula φ.  Bound occurrences (under a
ForAll/Exists that rebinds `var`) are left untouched.

free_vars(φ) returns the set of free variable names in φ.

collect_terms(φ, out) gathers every name that can serve as a concrete
instantiation term — predicate arguments and atom names.
"""

from __future__ import annotations

from parser.ast import Formula, Atom, Not, And, Imp, Predicate, ForAll, Exists


# ──────────────────────────────────────────────────────────────────────────────
# substitute
# ──────────────────────────────────────────────────────────────────────────────

def substitute(formula: Formula, var: str, term: str) -> Formula:
    """
    Return a copy of `formula` where every free occurrence of variable `var`
    is replaced with the name `term`.

    Parameters
    ----------
    formula : the formula to rewrite
    var     : the variable name to replace (e.g. "x")
    term    : the term name to substitute in (e.g. "A" for a constant)

    Notes
    -----
    • Propositional Atom nodes have no variables, so they are returned as-is.
    • ForAll/Exists nodes whose bound variable equals `var` shadow the free
      occurrence — substitution stops there (standard capture-avoidance).
    • Predicate arguments that equal `var` are replaced; argument positions
      that hold constants or different variables are unchanged.
    """
    if isinstance(formula, Atom):
        return formula  # propositional atoms carry no variable positions

    if isinstance(formula, Predicate):
        new_args = tuple(term if a == var else a for a in formula.args)
        return Predicate(formula.name, new_args)

    if isinstance(formula, Not):
        return Not(substitute(formula.child, var, term))

    if isinstance(formula, And):
        return And(
            substitute(formula.left, var, term),
            substitute(formula.right, var, term),
        )

    if isinstance(formula, Imp):
        return Imp(
            substitute(formula.left, var, term),
            substitute(formula.right, var, term),
        )

    if isinstance(formula, ForAll):
        if formula.var == var:
            return formula  # bound variable shadows — do not substitute inside
        return ForAll(formula.var, substitute(formula.body, var, term))

    if isinstance(formula, Exists):
        if formula.var == var:
            return formula  # same shadowing rule
        return Exists(formula.var, substitute(formula.body, var, term))

    return formula  # unknown formula type — leave unchanged


# ──────────────────────────────────────────────────────────────────────────────
# free_vars
# ──────────────────────────────────────────────────────────────────────────────

def free_vars(formula: Formula) -> set[str]:
    """
    Return the set of variable names that occur free in `formula`.

    Convention: variable names are lowercase strings (matching VAR in the
    grammar); uppercase names are treated as constants and are NOT returned.
    """
    out: set[str] = set()
    _collect_free(formula, bound=frozenset(), out=out)
    return out


def _collect_free(
    formula: Formula,
    bound: frozenset[str],
    out: set[str],
) -> None:
    if isinstance(formula, Atom):
        return  # atoms are propositional constants, not variables

    if isinstance(formula, Predicate):
        for arg in formula.args:
            if arg[0].islower() and arg not in bound:
                out.add(arg)
        return

    if isinstance(formula, Not):
        _collect_free(formula.child, bound, out)
        return

    if isinstance(formula, (And, Imp)):
        _collect_free(formula.left, bound, out)
        _collect_free(formula.right, bound, out)
        return

    if isinstance(formula, ForAll):
        _collect_free(formula.body, bound | {formula.var}, out)
        return

    if isinstance(formula, Exists):
        _collect_free(formula.body, bound | {formula.var}, out)
        return


# ──────────────────────────────────────────────────────────────────────────────
# collect_terms
# ──────────────────────────────────────────────────────────────────────────────

def collect_terms(formula: Formula, out: set[str]) -> None:
    """
    Collect all names that can serve as concrete instantiation terms.

    These are:
    - Every argument appearing in a Predicate  (both constants and variables
      — variables in predicate args have already been bound by a quantifier
      in the enclosing scope, or they are Skolem-like names the prover can
      use for instantiation).
    - The names of propositional Atom nodes (they act as constants).

    Bound variable names in ForAll/Exists binders are NOT collected because
    they are not ground terms; instead, the arguments *inside* the body are
    collected (and those may coincide with the bound variable name when no
    other constant is available — this gives the prover at least one term to
    instantiate with).
    """
    if isinstance(formula, Atom):
        out.add(formula.name)
        return

    if isinstance(formula, Predicate):
        out.update(formula.args)
        return

    if isinstance(formula, Not):
        collect_terms(formula.child, out)
        return

    if isinstance(formula, (And, Imp)):
        collect_terms(formula.left, out)
        collect_terms(formula.right, out)
        return

    if isinstance(formula, (ForAll, Exists)):
        collect_terms(formula.body, out)
        return
