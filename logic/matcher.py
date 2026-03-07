from parser.ast import Formula, And, Imp
# A shape-checker for formulas.
# Its job is to answer questions like:
# - are these two formulas exactly the same?
# - is this formula an implication?
# - if this is P -> Q, what are the left and right parts?
# - does this conjunction have the goal on the left or right

def expand_context(context: set[Formula]) -> set[Formula]:
    """
    Expand context using conjunction elimination:
    if (A & B) is known, then A and B are known
    """

    expanded = set(context)
    changed = True

    while changed:
        changed = False
        new_items: set[Formula] = set()

        for formula in expanded:
            if isinstance(formula, And):
                if formula.left not in expanded:
                    new_items.add(formula.left)
                if formula.right not in expanded:
                    new_items.add(formula.right)
        
        if new_items:
            expanded |= new_items
            changed = True

    return expanded

def implications_with_conclusion(goal: Formula, context: set[Formula]) -> list[Imp]:
    """
    Return all implications in context whose consequent matches the goal.
    """
    matches = []
    for formula in context:
        if isinstance(formula, Imp) and formula.right == goal:
            matches.append(formula)
    return matches