from parser.parser import parse_formula
from planning.encoder import write_problem_file


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


if __name__ == "__main__":
    generate_example_problem()