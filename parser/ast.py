from __future__ import annotations
from dataclasses import dataclass


class Formula:
    pass


@dataclass(frozen=True)
class Atom(Formula):
    """Propositional atom — a truth-valued constant such as P, Q, R."""
    name: str

    def __str__(self) -> str:
        return self.name


@dataclass(frozen=True)
class Not(Formula):
    """Negation: ~φ"""
    child: Formula

    def __str__(self) -> str:
        if isinstance(self.child, Atom):
            return f"~{self.child}"
        return f"~({self.child})"


@dataclass(frozen=True)
class And(Formula):
    """Conjunction: φ ∧ ψ"""
    left: Formula
    right: Formula

    def __str__(self) -> str:
        return f"({self.left} & {self.right})"


@dataclass(frozen=True)
class Imp(Formula):
    """Implication: φ → ψ"""
    left: Formula
    right: Formula

    def __str__(self) -> str:
        return f"({self.left} -> {self.right})"


# ──────────────────────────────────────────────────────────────────────────────
# First-order extensions
# ──────────────────────────────────────────────────────────────────────────────

@dataclass(frozen=True)
class Predicate(Formula):
    """
    First-order predicate applied to a tuple of term names.

    Examples
    --------
    P(x)          → Predicate("P", ("x",))
    R(x, A)       → Predicate("R", ("x", "A"))
    P()           → Predicate("P", ())   (equivalent to propositional atom P)

    Convention: uppercase arg names are constants (A, B, JOHN),
                lowercase arg names are variables (x, y, z).
    """
    name: str
    args: tuple[str, ...]

    def __str__(self) -> str:
        if not self.args:
            return self.name
        return f"{self.name}({', '.join(self.args)})"


@dataclass(frozen=True)
class ForAll(Formula):
    """
    Universal quantification: ∀var.body

    Example: forall x. P(x)  →  ForAll("x", Predicate("P", ("x",)))
    """
    var: str
    body: Formula

    def __str__(self) -> str:
        return f"forall {self.var}. {self.body}"


@dataclass(frozen=True)
class Exists(Formula):
    """
    Existential quantification: ∃var.body

    Example: exists x. P(x)  →  Exists("x", Predicate("P", ("x",)))
    """
    var: str
    body: Formula

    def __str__(self) -> str:
        return f"exists {self.var}. {self.body}"
