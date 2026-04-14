from __future__ import annotations
from dataclasses import dataclass

class Formula:
    pass

@dataclass(frozen=True)
class Atom(Formula):
    """The most basic building block of a logical formula"""
    name: str

    def __str__(self) -> str:
        return self.name

@dataclass(frozen=True)
class Not(Formula):
    """Negation"""
    child: Formula

    def __str__(self) -> str:
        # No parens needed for simple atoms/vars/predicates
        if isinstance(self.child, (Atom, "Var", "Predicate")):  # forward ref handled below
            return f"~{self.child}"
        return f"~({self.child})"

@dataclass(frozen=True)
class And(Formula):
    """Conjunction"""
    left: Formula
    right: Formula

    def __str__(self):
        return f"({self.left} & {self.right})"

@dataclass(frozen=True)
class Imp(Formula):
    """Implication = if P then Q"""
    left: Formula
    right: Formula

    def __str__(self) -> str:
        return f"({self.left} -> {self.right})"

# ---------------------------------------------------------------------------
# First-order logic extensions
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Or(Formula):
    """Disjunction  A ∨ B"""
    left: Formula
    right: Formula

    def __str__(self) -> str:
        return f"({self.left} ∨ {self.right})"

@dataclass(frozen=True)
class Var(Formula):
    """A logical variable (lowercase), used as an argument to predicates
    and introduced during proof search as fresh Skolem constants."""
    name: str

    def __str__(self) -> str:
        return self.name

@dataclass(frozen=True)
class Predicate(Formula):
    """A predicate applied to a tuple of Var arguments.  T(y),  Q(x,z), …"""
    name: str
    args: tuple  # tuple[Var, ...]

    def __str__(self) -> str:
        return f"{self.name}({', '.join(str(a) for a in self.args)})"

@dataclass(frozen=True)
class ForAll(Formula):
    """Universal quantifier  ∀var.body"""
    var: str     # name of the bound variable
    body: Formula

    def __str__(self) -> str:
        return f"∀{self.var}.{self.body}"

@dataclass(frozen=True)
class Exists(Formula):
    """Existential quantifier  ∃var.body"""
    var: str
    body: Formula

    def __str__(self) -> str:
        return f"∃{self.var}.{self.body}"


# Patch Not.__str__ so it handles Var and Predicate without extra parens.
# (Defined after the new classes so the isinstance checks work.)
def _not_str(self) -> str:
    if isinstance(self.child, (Atom, Var, Predicate)):
        return f"~{self.child}"
    return f"~({self.child})"

Not.__str__ = _not_str  # type: ignore[method-assign]
