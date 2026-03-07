from __future__ import annotations

from typing import Optional

from parser.ast import Formula, And, Imp
from logic.matcher import expand_context, implications_with_conclusion
from logic.proof_tree import ProofNode


def prove(
    goal: Formula,
    context: set[Formula],
    depth: int = 0,
    max_depth: int = 10,
) -> Optional[ProofNode]:
    """
    Tiny backward prover for propositional logic.

    Supported:
    - Assumption
    - And Introduction
    - And Elimination (via context expansion)
    - Implication Introduction
    - Modus Ponens
    """
    if depth > max_depth:
        return None

    expanded = expand_context(context)

    # Rule 1: Assumption
    if goal in expanded:
        return ProofNode(conclusion=goal, rule="Assumption")

    # Rule 2: And Introduction
    if isinstance(goal, And):
        left_proof = prove(goal.left, context, depth + 1, max_depth)
        if left_proof is None:
            return None

        right_proof = prove(goal.right, context, depth + 1, max_depth)
        if right_proof is None:
            return None

        return ProofNode(
            conclusion=goal,
            rule="AndIntro",
            children=[left_proof, right_proof],
        )

    # Rule 3: Implication Introduction
    if isinstance(goal, Imp):
        new_context = set(context)
        new_context.add(goal.left)

        child_proof = prove(goal.right, new_context, depth + 1, max_depth)
        if child_proof is not None:
            return ProofNode(
                conclusion=goal,
                rule="ImpIntro",
                children=[child_proof],
                note=f"assume {goal.left}",
            )

    # Rule 4: Modus Ponens
    for implication in implications_with_conclusion(goal, expanded):
        antecedent_proof = prove(implication.left, context, depth + 1, max_depth)
        if antecedent_proof is not None:
            return ProofNode(
                conclusion=goal,
                rule="MP",
                children=[
                    antecedent_proof,
                    ProofNode(conclusion=implication, rule="Given"),
                ],
            )

    return None