from parser.parser import parse_formula

from planning.encoder import write_problem_file
from csp.skeleton_csp import solve_bounded_csp

def generate_example_problem() -> None:
    # Simple example: from P and P -> Q, prove Q
    assumptions = [
        parse_formula("P"),
        parse_formula("P -> Q"),
    ]
    goal = parse_formula("Q")

    write_problem_file(
        "planning/problems/prove_q_from_p_imp_q.pddl",
        "prove-q-from-p-imp-q",
        assumptions,
        goal,
    )

    print("Generated planning/problems/prove_q_from_p_imp_q.pddl")

def run_csp_demo() -> None:
    assumptions = [
        parse_formula("P"),
        parse_formula("P -> Q"),
        parse_formula("Q -> R"),
    ]
    goal = parse_formula("R")

    solution = solve_bounded_csp(assumptions, goal, max_steps=3)

    print("=" * 60)
    print("CSP demo")
    print("Assumptions:", [str(a) for a in assumptions])
    print("Goal:", goal)

    if solution is None:
        print("No CSP proof skeleton found.")
        return

    print("Found proof skeleton:")
    for i, step in enumerate(solution):
        print(
            f"  Step {i}: {step.formula} by {step.rule} "
            f"(supports: {step.support1}, {step.support2})"
        )


if __name__ == "__main__":
    run_csp_demo()