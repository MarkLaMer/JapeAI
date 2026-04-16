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
from logic.fol_prover import prove_fol, render_fol_proof
from cbn.logic_causal import solve_logic_causal, render_logic_causal_steps


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

    # ── Backward logic prover (FOL) ──────────────────────────────────────────
    print("\n[Backward logic prover]")
    logic_result = prove_fol(goal, assumptions)
    if logic_result is None:
        print("  No proof found.")
    else:
        lines = []
        render_fol_proof(logic_result, lines)
        for depth, formula, rule, note in lines:
            pad = "  " * (depth + 1)
            note_str = f"  [{note}]" if note else ""
            print(f"{pad}{formula}   by {rule}{note_str}")

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

def solve_causal_problem(
    assumption_strings: list[str],
    goal_string: str,
) -> None:
    """
    Solve a natural-deduction problem with the CBN/SCM causal solver and print steps.
    Takes the same format as solve_problem() — list of formula strings + goal string.
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

    print("\n[Causal (CBN/SCM) solver]")
    result = solve_logic_causal(assumptions, goal)
    if result is None:
        print("  No proof found.")
    else:
        lines: list = []
        render_logic_causal_steps(result, lines)
        non_derived = {"assumption", "assumptions", "premise", "premises", "hyp"}
        derived = [(d, f, r, n) for (d, f, r, n) in lines if r not in non_derived]
        print(f"  Proof ({len(derived)} step(s)):")
        for i, (depth, formula, rule, note) in enumerate(derived, 1):
            indent = "  " * depth
            note_str = f"  [{note}]" if note else ""
            print(f"    {i}. {indent}{formula}   ({rule}){note_str}")


def _flag_value(flag: str) -> str | None:
    """Return the value following *flag* in sys.argv, if present."""
    try:
        idx = sys.argv.index(flag)
    except ValueError:
        return None
    if idx + 1 >= len(sys.argv):
        return None
    return sys.argv[idx + 1]


def run_causal_cli() -> int:
    """
    Solve one causal proof from command-line flags.

    Example:
      python main.py --causal-prove --assumptions "P, P -> Q, Q -> R" --goal "R"
    """
    assumptions_arg = _flag_value("--assumptions")
    goal_arg = _flag_value("--goal")
    if goal_arg is None:
        print('Usage: python main.py --causal-prove --assumptions "P, P -> Q" --goal "Q"')
        return 2

    assumption_strings = (
        [s.strip() for s in assumptions_arg.split(",") if s.strip()]
        if assumptions_arg else []
    )
    solve_causal_problem(assumption_strings, goal_arg)
    return 0


def run_causal_demos() -> None:
    """Run built-in causal (CBN/SCM) demos — same problems as main demos."""
    problems = [
        ("MP chain: P, P→Q, Q→R ⊢ R",
         ["P", "P -> Q", "Q -> R"], "R"),

        ("Long chain: P, P→Q, Q→R, R→S ⊢ S",
         ["P", "P -> Q", "Q -> R", "R -> S"], "S"),

        ("AND-ELIM + MP: (P & Q), (P & Q) → R ⊢ R",
         ["P & Q", "(P & Q) -> R"], "R"),

        ("AND intro: P, Q ⊢ P & Q",
         ["P", "Q"], "P & Q"),

        ("AND elim: P & Q ⊢ P",
         ["P & Q"], "P"),

        ("Unprovable: P ⊢ Q  [should fail]",
         ["P"], "Q"),
    ]

    for label, assumptions, goal in problems:
        print(f"\n{'#' * 60}")
        print(f"# {label}")
        solve_causal_problem(assumptions, goal)


def interactive_causal() -> None:
    """Interactive causal (CBN/SCM) proof mode — same UX as interactive()."""
    print("JapeAI — Causal (CBN/SCM) proof assistant")
    print("Syntax: atoms are uppercase (P, Q, R, …),  &  = conjunction,  ->  = implication")
    print("Type 'exit' to quit.\n")

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
        solve_causal_problem(assumption_strings, goal_string)
        print()


if __name__ == "__main__":
    if "--demo" in sys.argv:
        run_demos()
    elif "--causal-prove" in sys.argv:
        raise SystemExit(run_causal_cli())
    elif "--causal-demo" in sys.argv:
        run_causal_demos()
    elif "--causal" in sys.argv:
        interactive_causal()
    elif "--pddl" in sys.argv:
        # Interactive but always write PDDL
        interactive()
    else:
        interactive()
