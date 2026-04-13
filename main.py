"""
main.py — JapeAI interactive proof runner.

Usage:
  python main.py                  # interactive mode
  python main.py --demo           # run built-in demos
  python main.py --pddl           # also write PDDL problem file
"""

from __future__ import annotations

import sys

from parser.parser import parse_formula
from planning.encoder import write_problem_file
from planning.internal_planner import plan_and_print
from csp.skeleton_csp import solve_csp, print_csp_proof
from logic.rules import prove
from logic.proof_tree import print_proof


# --------------------------------------------------------------------------- #
# Core solve helper used by both interactive and demo modes
# --------------------------------------------------------------------------- #

def solve_problem(
    assumption_strings: list[str],
    goal_string: str,
    *,
    write_pddl: bool = False,
    pddl_name: str = "problem",
) -> None:
    """
    Parse, solve, and pretty-print a natural deduction problem using all three
    available solvers (CSP, internal PDDL planner, backward logic prover).
    """
    try:
        assumptions = [parse_formula(s.strip()) for s in assumption_strings]
        goal = parse_formula(goal_string.strip())
    except Exception as e:
        print(f"Parse error: {e}")
        return

    print()
    print("=" * 60)
    print("Assumptions :", [str(a) for a in assumptions])
    print("Goal        :", goal)
    print("=" * 60)

    # ── CSP solver (forward + ImpIntro, iterative deepening) ────────────────
    print("\n[CSP solver]")
    csp_result = solve_csp(assumptions, goal)
    if csp_result is None:
        print("  No proof found (within step bound).")
    else:
        print(f"  Proof ({len(csp_result)} top-level step(s)):")
        print_csp_proof(csp_result, indent=2)

    # ── Internal PDDL planner (forward BFS) ─────────────────────────────────
    print("\n[Internal PDDL planner]")
    plan_and_print(assumptions, goal)

    # ── Backward logic prover ────────────────────────────────────────────────
    print("\n[Backward logic prover]")
    logic_result = prove(goal, set(assumptions))
    if logic_result is None:
        print("  No proof found.")
    else:
        print("  Proof tree:")
        print_proof(logic_result, indent=2)

    # ── Optionally write PDDL problem file ───────────────────────────────────
    if write_pddl:
        path = f"planning/problems/{pddl_name}.pddl"
        write_problem_file(path, pddl_name, assumptions, goal)
        print(f"\n[PDDL] Problem file written to {path}")


# --------------------------------------------------------------------------- #
# Interactive mode
# --------------------------------------------------------------------------- #

def interactive() -> None:
    print("JapeAI — natural deduction proof assistant")
    print("Syntax: atoms are uppercase (P, Q, R, ...)")
    print("        &  = conjunction,  ->  = implication,  ~  = negation")
    print("Type 'exit' or Ctrl-C to quit.\n")

    while True:
        try:
            raw = input("Assumptions (comma-separated, or blank): ").strip()
        except (KeyboardInterrupt, EOFError):
            print("\nBye.")
            break

        if raw.lower() in ("exit", "quit"):
            break

        assumption_strings = [s for s in raw.split(",") if s.strip()] if raw else []

        try:
            goal_string = input("Goal: ").strip()
        except (KeyboardInterrupt, EOFError):
            print("\nBye.")
            break

        if goal_string.lower() in ("exit", "quit"):
            break

        pddl_flag = input("Write PDDL file? [y/N]: ").strip().lower() == "y"

        safe_name = goal_string.replace(" ", "_").replace("->", "imp").replace("&", "and").replace("~", "not")[:40]
        solve_problem(assumption_strings, goal_string, write_pddl=pddl_flag, pddl_name=f"prove_{safe_name}")
        print()


# --------------------------------------------------------------------------- #
# Built-in demos
# --------------------------------------------------------------------------- #

def run_demos() -> None:
    problems = [
        # (label, assumptions, goal)
        ("MP chain: P, P→Q, Q→R ⊢ R",
         ["P", "P -> Q", "Q -> R"], "R"),

        ("ImpIntro: ⊢ P → P",
         [], "P -> P"),

        ("ImpIntro: ⊢ (P & Q) → (Q & P)  [AND commutativity]",
         [], "(P & Q) -> (Q & P)"),

        ("ImpIntro nested: ⊢ P → (Q → P)  [K tautology]",
         [], "P -> (Q -> P)"),

        ("Long chain: P, P→Q, Q→R, R→S ⊢ S",
         ["P", "P -> Q", "Q -> R", "R -> S"], "S"),

        ("AND-ELIM + MP: (P & Q), (P & Q) → R ⊢ R",
         ["P & Q", "(P & Q) -> R"], "R"),

        ("Context + ImpIntro: P ⊢ Q → (P & Q)",
         ["P"], "Q -> (P & Q)"),

        ("Unprovable: P ⊢ Q  [should fail]",
         ["P"], "Q"),
    ]

    for label, assumptions, goal in problems:
        print(f"\n{'#' * 60}")
        print(f"# {label}")
        solve_problem(assumptions, goal)


# --------------------------------------------------------------------------- #
# Entry point
# --------------------------------------------------------------------------- #

if __name__ == "__main__":
    if "--demo" in sys.argv:
        run_demos()
    elif "--pddl" in sys.argv:
        # Interactive but always write PDDL
        interactive()
    else:
        interactive()
