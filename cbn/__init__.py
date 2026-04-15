"""
cbn — Causal Bayesian Network + Structural Causal Model layer for JapeAI.

Public API
----------
CausalGraph        — DAG of named nodes and directed causal edges
graph_from_string  — parse "A→B, A→C" into a CausalGraph
d_separation_trace — Bayes-ball with a human-readable step trace

SCM                — Structural Causal Model (equations + noise)
SCMVariable        — one endogenous variable (equation + noise pair)
NoiseVar           — discrete exogenous noise variable
make_wet_grass_scm — built-in Rain/Sprinkler demo model

solve_causal       — main NL causal solver entry point
CausalStep         — one step in a reasoning trace
print_causal_trace — pretty-print a trace to stdout
"""

from cbn.graph import CausalGraph, graph_from_string, d_separation_trace, BallMove
from cbn.scm   import SCM, SCMVariable, NoiseVar, binary_noise, uniform_noise, make_wet_grass_scm
from cbn.nl_solver import solve_causal, CausalStep, print_causal_trace

__all__ = [
    # graph
    "CausalGraph",
    "graph_from_string",
    "d_separation_trace",
    "BallMove",
    # scm
    "SCM",
    "SCMVariable",
    "NoiseVar",
    "binary_noise",
    "uniform_noise",
    "make_wet_grass_scm",
    # nl solver
    "solve_causal",
    "CausalStep",
    "print_causal_trace",
]
