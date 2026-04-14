"""
JapeAI — propositional + first-order theorem prover demo.

Run with:  python main.py

Shows the CSP solver and the Bayesian solver side-by-side on the same
problems, including the first-order (quantifier) problems that the Bayesian
solver can handle but the CSP cannot.
"""

from __future__ import annotations

from parser.parser import parse_formula
from csp.skeleton_csp import solve_bounded_csp, CSPStats
from bayes.solver import solve_bayes, BayesSolverStats


# ──────────────────────────────────────────────────────────────────────────────
# Problem sets
# ──────────────────────────────────────────────────────────────────────────────

# Propositional problems — both solvers can handle these.
PROPOSITIONAL_PROBLEMS: list[tuple[str, list[str], str, int]] = [
    (
        "Modus Ponens chain  (P → Q → R)",
        ["P", "P -> Q", "Q -> R"],
        "R",
        3,
    ),
    (
        "Conjunction goal  (P & Q & R)",
        ["P", "Q", "R"],
        "(P & (Q & R))",
        3,
    ),
    (
        "Four-step chain  (A → B → C → D → E)",
        ["A", "A -> B", "B -> C", "C -> D", "D -> E"],
        "E",
        4,
    ),
    (
        "Mixed elim + chain",
        ["P & Q", "(P & Q) -> R", "R -> S"],
        "S",
        3,
    ),
    (
        "Conjunction + chain  (R&S→T)",
        ["P", "Q", "P -> R", "Q -> S", "(R & S) -> T"],
        "T",
        4,
    ),
    (
        "Unsolvable  (P does not prove Q)",
        ["P"],
        "Q",
        3,
    ),
]

# First-order problems — Bayesian solver only (CSP does not support quantifiers).
FOL_PROBLEMS: list[tuple[str, list[str], str, int]] = [
    (
        "Universal instantiation",
        ["forall x. P(x)"],
        "P(A)",
        2,
    ),
    (
        "UI then Modus Ponens",
        ["forall x. (P(x) -> Q(x))", "P(A)"],
        "Q(A)",
        3,
    ),
    (
        "UI chain  (P→Q→R)",
        ["forall x. (P(x) -> Q(x))", "forall x. (Q(x) -> R(x))", "P(A)"],
        "R(A)",
        4,
    ),
    (
        "Existential introduction",
        ["P(A)"],
        "exists x. P(x)",
        2,
    ),
    (
        "UI then EI  (∀P → ∃Q)",
        ["forall x. (P(x) -> Q(x))", "P(A)"],
        "exists y. Q(y)",
        4,
    ),
    (
        "Mixed prop + FOL",
        ["P", "forall x. Q(x)"],
        "P & Q(A)",
        3,
    ),
]


# ──────────────────────────────────────────────────────────────────────────────
# Helpers
# ──────────────────────────────────────────────────────────────────────────────

def _print_csp_steps(result: list | None, stats: CSPStats) -> None:
    if result is None:
        print("    → No proof found.")
    else:
        for i, step in enumerate(result):
            sup1 = str(step.support1) if step.support1 is not None else "—"
            sup2 = str(step.support2) if step.support2 is not None else "—"
            print(
                f"    Step {i + 1}: {step.formula}"
                f"  by {step.rule}"
                f"  (supports: {sup1}, {sup2})"
            )
    print(
        f"    nodes={stats.nodes_expanded}"
        f"  candidates={stats.candidates_generated}"
    )


def _print_bayes_steps(result: list | None, stats: BayesSolverStats) -> None:
    if result is None:
        print("    → No proof found.")
    else:
        for i, step in enumerate(result):
            sups = []
            if step.support1 is not None:
                sups.append(str(step.support1))
            if step.support2 is not None:
                sups.append(str(step.support2))
            print(
                f"    Step {i + 1}: {step.formula}"
                f"  by {step.rule}"
                f"  (supports: {', '.join(sups) or '—'})"
                f"  [p={step.score:.3f}]"
            )
    print(
        f"    nodes={stats.nodes_expanded}"
        f"  candidates_scored={stats.candidates_scored}"
        f"  steps_in_proof={stats.steps_in_proof}"
    )


# ──────────────────────────────────────────────────────────────────────────────
# Comparison runners
# ──────────────────────────────────────────────────────────────────────────────

def run_propositional_comparison() -> None:
    """Run both solvers on propositional problems and print proof steps."""
    sep = "─" * 80
    print("\n" + "=" * 80)
    print("  Part 1: Propositional Logic  —  CSP vs Bayesian Solver")
    print("=" * 80)

    for label, assumptions_str, goal_str, max_steps in PROPOSITIONAL_PROBLEMS:
        assumptions = [parse_formula(s) for s in assumptions_str]
        goal        = parse_formula(goal_str)

        csp_stats = CSPStats()
        csp_result = solve_bounded_csp(assumptions, goal,
                                       max_steps=max_steps, stats=csp_stats)

        bayes_stats = BayesSolverStats()
        bayes_result = solve_bayes(assumptions, goal,
                                   max_steps=max_steps, stats=bayes_stats)

        print(f"\n{sep}")
        print(f"  {label}")
        print(f"  Assumptions : {[str(a) for a in assumptions]}")
        print(f"  Goal        : {goal}   (max_steps={max_steps})")
        print(sep)
        print("  [CSP]")
        _print_csp_steps(csp_result, csp_stats)
        print("  [Bayes]")
        _print_bayes_steps(bayes_result, bayes_stats)

    print(f"\n{sep}")


def run_fol_demo() -> None:
    """Demonstrate Bayesian solver on first-order (quantifier) problems."""
    sep = "─" * 80
    print("\n" + "=" * 80)
    print("  Part 2: First-Order Logic  —  Bayesian Solver only")
    print("  (CSP does not support universal/existential quantifiers)")
    print("=" * 80)

    for label, assumptions_str, goal_str, max_steps in FOL_PROBLEMS:
        assumptions = [parse_formula(s) for s in assumptions_str]
        goal        = parse_formula(goal_str)

        bayes_stats = BayesSolverStats()
        bayes_result = solve_bayes(assumptions, goal,
                                   max_steps=max_steps, stats=bayes_stats)

        print(f"\n{sep}")
        print(f"  {label}")
        print(f"  Assumptions : {[str(a) for a in assumptions]}")
        print(f"  Goal        : {goal}   (max_steps={max_steps})")
        print(sep)
        print("  [Bayes]")
        _print_bayes_steps(bayes_result, bayes_stats)

    print(f"\n{sep}")


if __name__ == "__main__":
    run_propositional_comparison()
    run_fol_demo()
