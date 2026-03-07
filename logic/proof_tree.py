from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional

from parser.ast import Formula

@dataclass
class ProofNode:
    """
    This class represents one step in a proof.
    Each node contains:
    - what formula we proved
    - which rule we used
    - what earlier steps justify it

    The structure forms a tree.
    """
    conclusion: Formula # This is the formula proven at this step.
    rule: str           # Which inference rule produced the formula. e.g., assumptions, modus_ponems, imp_intro, etc. 
    children: list["ProofNode"] = field(default_factory=list) # This stores the premises used to derive the conclusion.
    note: Optional[str] = None

def print_proof(node: ProofNode, indent: int = 0) -> None:
    prefix= " "* indent
    extra = f" [{node.note}]" if node.note else ""
    print(f"{prefix}{node.conclusion}         by {node.rule}{extra}")
    for child in node.children:
        print_proof(child, indent + 1)


