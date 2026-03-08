from __future__ import annotations

from pathlib import Path #used to write the generated PDDL file

from parser.ast import Formula, Atom, And, Imp, Not

# Convert a formula AST into a stable PDDL object name. Same formula alays gets same identifier
# Example:
# P       -> f_p
# P & Q   -> f_and_p_q
# P -> Q  -> f_imp_p_q
def formula_name(formula: Formula) -> str:
    '''
    This function converts a formula AST into a PDDL object name.
    '''
    if isinstance(formula, Atom):
        return f"f_{formula.name.lower()}"

    if isinstance(formula, And):
        left_name = formula_name(formula.left)[2:]
        right_name = formula_name(formula.right)[2:]
        return f"f_and_{left_name}_{right_name}"

    if isinstance(formula, Imp):
        left_name = formula_name(formula.left)[2:]
        right_name = formula_name(formula.right)[2:]
        return f"f_imp_{left_name}_{right_name}"

    if isinstance(formula, Not):
        child_name = formula_name(formula.child)[2:]
        return f"f_not_{child_name}"

    # Fallback in case we extend Formula later
    return "f_unknown"

# Recursively collect every formula/subformula we need to mention in the PDDL problem.
# This is important because compound formulas need both:
# - themselves as objects
# - their parts as objects too
def collect_formulas(formula: Formula, out: set[Formula]) -> None:
    '''
    Find every formula and subformula needed for the PDDL problem.

    E.g. P -> (Q & R)
    We must include: P, Q, R, Q & R, P -> (Q & R)
    '''
    if formula in out: # Avoid collecting the same formula twice!
        return

    out.add(formula) #current formula

    #Recursively collect their components:
    if isinstance(formula, And) or isinstance(formula, Imp):
        collect_formulas(formula.left, out)
        collect_formulas(formula.right, out)

    elif isinstance(formula, Not):
        collect_formulas(formula.child, out)


# Build the structural facts that tell the planner how compound formulas are built.
# These are the facts the actions use in the domain.
def structural_facts(formulas: set[Formula]) -> list[str]:
    '''
    This generates the facts describing formula structure for the planner.
    '''
    facts: list[str] = []

    for formula in formulas:
        if isinstance(formula, And):
            facts.append(
                f"(conjunction {formula_name(formula.left)} {formula_name(formula.right)} {formula_name(formula)})"
            )

        elif isinstance(formula, Imp):
            facts.append(
                f"(implication {formula_name(formula.left)} {formula_name(formula.right)} {formula_name(formula)})"
            )

    return sorted(facts)


# Turn one theorem-proving task into a full PDDL problem string.
# Assumptions become known facts in the initial state.
# Goal becomes the target known fact.
def encode_problem(problem_name: str, assumptions: list[Formula], goal: Formula) -> str:
    formulas: set[Formula] = set()

    # Collect everything that shows up anywhere in the problem
    for assumption in assumptions:
        collect_formulas(assumption, formulas)

    collect_formulas(goal, formulas)

    # Create all PDDL objects
    objects = sorted(formula_name(formula) for formula in formulas)

    # Initial known formulas = assumptions
    init_known = sorted(f"(known {formula_name(assumption)})" for assumption in assumptions)

    # Structural facts say which objects represent implications / conjunctions
    init_structural = structural_facts(formulas)

    goal_fact = f"(known {formula_name(goal)})"

    # Build the final problem text
    lines: list[str] = []
    lines.append(f"(define (problem {problem_name})")
    lines.append("  (:domain theorem-proving)")
    lines.append("")
    lines.append("  (:objects")
    lines.append(f"    {' '.join(objects)} - formula")
    lines.append("  )")
    lines.append("")
    lines.append("  (:init")

    for fact in init_known:
        lines.append(f"    {fact}")

    for fact in init_structural:
        lines.append(f"    {fact}")

    lines.append("  )")
    lines.append("")
    lines.append("  (:goal")
    lines.append(f"    {goal_fact}")
    lines.append("  )")
    lines.append(")")

    return "\n".join(lines)


# Write a generated PDDL problem to disk.
# This is what we will call from main.py or a small helper script.
def write_problem_file(
    path: str | Path,
    problem_name: str,
    assumptions: list[Formula],
    goal: Formula,
) -> None:
    problem_text = encode_problem(problem_name, assumptions, goal)
    Path(path).write_text(problem_text, encoding="utf-8")