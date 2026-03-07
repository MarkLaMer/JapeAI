from parser.parser import parse_formula
from logic.rules import prove
from logic.proof_tree import print_proof

from search.state import SearchState
from search.planner import bfs_plan

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

def run_planner_case(context_strings: list[str], goal_string: str):
    context = frozenset(parse_formula(s) for s in context_strings)
    goal = parse_formula(goal_string)

    initial = SearchState(
        goals=(goal,),
        context=context,
        depth=0,
    )

    result = bfs_plan(initial)

    print("=" * 60)
    print("Context:", ", ".join(str(x) for x in context) if context else "{}")
    print("Goal:", goal)
    print("Success:", result.success)
    print("Visited states:", result.visited_count)
    print()


if __name__ == "__main__":
    run_case(["P"], "P")
    run_case(["P & Q"], "P")
    run_case(["P", "P -> Q"], "Q")
    run_case([], "P -> P")
    run_case(["P", "Q"], "P & Q")
    run_case(["P", "P -> Q", "Q -> R"], "R")
    run_case(["P"], "Q")
    # planning tests
    run_planner_case(["P"], "P")
    run_planner_case(["P", "P -> Q"], "Q")
    run_planner_case([], "P -> P")
    run_planner_case(["P", "Q"], "P & Q")
    run_planner_case(["P"], "Q")