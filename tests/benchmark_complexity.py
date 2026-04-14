"""
Benchmark: CSP vs Bayesian solver across proof complexities.

Run with:  python -m tests.benchmark_complexity
       or: cd project_root && python tests/benchmark_complexity.py
"""

from __future__ import annotations

import time
from parser.parser import parse_formula
from csp.skeleton_csp import solve_bounded_csp, CSPStats
from bayes.solver import solve_bayes, BayesSolverStats


# ──────────────────────────────────────────────────────────────────────────────
# Problem suite
# ──────────────────────────────────────────────────────────────────────────────

PROBLEMS: list[tuple[str, list[str], str, int]] = [
    # 1-step
    ("1-step  MP",            ["P", "P -> Q"],                          "Q",              1),
    ("1-step  and_elim_L",    ["P & Q"],                                "P",              1),
    ("1-step  and_elim_R",    ["P & Q"],                                "Q",              1),
    # 2-step
    ("2-step  chain",         ["P", "P -> Q", "Q -> R"],                "R",              2),
    ("2-step  elim+MP",       ["P & Q", "(P & Q) -> R"],                "R",              2),
    # 3-step
    ("3-step  chain",         ["P","P->Q","Q->R","R->S"],               "S",              3),
    ("3-step  branchy",       ["P","P->Q","P->R","Q->S","R->S","Q->R"], "S",              3),
    ("3-step  conj_goal",     ["P","Q","R"],                            "(P & (Q & R))",  3),
    # 4-step
    ("4-step  chain",         ["A","A->B","B->C","C->D","D->E"],        "E",              4),
    ("4-step  conj+chain",    ["P","Q","P->R","Q->S","(R & S)->T"],     "T",              4),
    # 5-step
    ("5-step  chain",         ["A","A->B","B->C","C->D","D->E","E->F"],"F",              5),
    ("5-step  deep+wide",     ["A","A->B","B->C","C->D","D->E","E->F",
                                "A->C","B->D"],                          "F",              5),
    # Quantifier problems (Bayes only)
    ("UI     direct",         ["forall x. P(x)"],                       "P(A)",           2),
    ("UI+MP  chain",          ["forall x. (P(x) -> Q(x))","P(A)"],     "Q(A)",           3),
    ("EI     from atom",      ["P(A)"],                                  "exists x. P(x)", 2),
    ("UI+EI  chain",          ["forall x. (P(x)->Q(x))","P(A)"],
                               "exists y. Q(y)",                                          4),
    # Failures
    ("fail   unrelated",      ["P"],                                    "Q",              3),
    ("fail   no-witness",     ["forall x. P(x)"],                       "Q(A)",           3),
]


def _parse(strings: list[str]) -> list:
    return [parse_formula(s) for s in strings]


def run_benchmark() -> None:
    sep = "─" * 116

    print("\n" + "=" * 116)
    print("  JapeAI  |  Proof Complexity Benchmark  |  CSP vs Bayesian Solver")
    print("=" * 116)
    print(f"  {'Problem':<32} {'Max':>4}  "
          f"{'CSP':>4} {'CNodes':>7} {'CCands':>8} {'CTime':>8}   "
          f"{'Bayes':>5} {'BNodes':>7} {'BCands':>8} {'BTime':>8}  Notes")
    print(sep)

    for label, assumptions_str, goal_str, max_steps in PROBLEMS:
        assumptions = _parse(assumptions_str)
        goal = parse_formula(goal_str)

        # CSP
        csp_stats = CSPStats()
        t0 = time.perf_counter()
        csp_result = solve_bounded_csp(assumptions, goal, max_steps=max_steps, stats=csp_stats)
        csp_ms = (time.perf_counter() - t0) * 1000

        # Bayes
        bayes_stats = BayesSolverStats()
        t0 = time.perf_counter()
        bayes_result = solve_bayes(assumptions, goal, max_steps=max_steps, stats=bayes_stats)
        bayes_ms = (time.perf_counter() - t0) * 1000

        csp_ok   = "OK"   if csp_result   is not None else "FAIL"
        bayes_ok = "OK"   if bayes_result is not None else "FAIL"

        notes = []
        if any("forall" in s or "exists" in s for s in assumptions_str) or \
           "forall" in goal_str or "exists" in goal_str:
            notes.append("FOL")
        if csp_result is None and bayes_result is not None:
            notes.append("Bayes solves, CSP cannot")
        if bayes_stats.nodes_expanded < csp_stats.nodes_expanded:
            notes.append("Bayes fewer nodes")

        print(
            f"  {label:<32} {max_steps:>4}  "
            f"{csp_ok:>4} {csp_stats.nodes_expanded:>7} {csp_stats.candidates_generated:>8} {csp_ms:>8.2f}   "
            f"{bayes_ok:>5} {bayes_stats.nodes_expanded:>7} {bayes_stats.candidates_scored:>8} {bayes_ms:>8.2f}"
            f"  {', '.join(notes)}"
        )

    print(sep)
    print("""
Notes
─────
FOL rows use universal_instantiation / existential_intro which the CSP
does not support — those rows have FAIL in the CSP column by design.

The Bayes solver uses cumulative log P(success) as its priority, so it
expands the most-confident partial proof first; the CSP uses depth-first
backtracking with a complexity sort key.
""")


if __name__ == "__main__":
    run_benchmark()
