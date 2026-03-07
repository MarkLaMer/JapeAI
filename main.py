from parser.parser import parse_formula
from logic.rules import prove
from logic.proof_tree import print_proof


def run_case(context_strings: list[str], goal_string: str, max_depth: int = 10) -> None:
    context = {parse_formula(s) for s in context_strings}
    goal = parse_formula(goal_string)

    print("=" * 60)
    print("Context:")
    if context:
        for item in context:
            print(f"  {item}")
    else:
        print("  {}")

    print(f"Goal:\n  {goal}")

    proof = prove(goal, context, max_depth=max_depth)

    if proof is None:
        print("\nResult: FAILED")
    else:
        print("\nResult: SUCCESS")
        print("Proof:")
        print_proof(proof)
    print()


if __name__ == "__main__":
    run_case(["P"], "P")
    run_case(["P & Q"], "P")
    run_case(["P", "P -> Q"], "Q")
    run_case([], "P -> P")
    run_case(["P", "Q"], "P & Q")
    run_case(["P", "P -> Q", "Q -> R"], "R")
    run_case(["P"], "Q")