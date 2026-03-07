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
        if isinstance(self.child, Atom):
            return f"~{self.child}" # simple Atom negation: ~P
        return f"~({self.child})" #give brackets ~(P AND Q)
    
@dataclass(frozen=True)
class And(Formula):
    """Conjunction"""
    left: Formula  # P 
    right: Formula # Q

    def __str__(self):
        return f"({self.left} & {self.right})"
    
@dataclass(frozen=True)
class Imp(Formula):
    """Implication = if P then Q"""
    left: Formula
    right: Formula

    def __str__(self) -> str:
        return f"({self.left} -> {self.right})"
