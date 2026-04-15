"""
cbn/nl_solver.py — Natural-language causal deduction solver.

Mirrors the role of csp/skeleton_csp.py and logic/rules.py but for causal
queries instead of propositional proofs.

Input  : an edge-list model string  +  a natural-language query string
Output : a list of CausalStep objects — a human-readable reasoning trace

Supported query types
---------------------
Graph queries (use CausalGraph only):
  "Is X d-separated from Y?"
  "Is X d-separated from Y given Z?"              Z = node or {N1, N2, …}
  "Is X independent of Y [given Z]?"              alias for d-separation
  "Does X cause Y?"                               Y ∈ descendants(X)?
  "Are X and Y in the same connected component?"
  "What are the parents of X?"
  "What are the children of X?"
  "What are the ancestors of X?"
  "What are the descendants of X?"
  "What is the Markov blanket of X?"
  "What is the topological order?"

SCM queries (require the built-in SCM or a user-described one):
  "What is the probability of X=v?"               marginal
  "What is the probability of X=v given do(Y=w)?" interventional
  "If Y=w, what would X be?"                      counterfactual (uses Wet-Grass SCM)

The solver always returns a list of (depth, text, kind, note) 4-tuples that
map directly to the proof-pane row format already used by the GUI.
"""
from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Any

from cbn.graph import CausalGraph, graph_from_string, d_separation_trace
from cbn.scm import SCM, make_wet_grass_scm


# ---------------------------------------------------------------------------
# Step representation  (matches GUI proof-line tuple format)
# ---------------------------------------------------------------------------

@dataclass
class CausalStep:
    depth: int
    text: str
    kind: str    # "query", "graph", "dsep", "blocked", "collider", "result",
                 # "scm", "abduct", "predict", "error"
    note: str | None = None

    def as_tuple(self) -> tuple:
        return (self.depth, self.text, self.kind, self.note)


# ---------------------------------------------------------------------------
# Query parser helpers
# ---------------------------------------------------------------------------

_ARROW_RE   = re.compile(r"→|->|-->")
_NODE_RE    = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
_SET_RE     = re.compile(r"\{([^}]+)\}")       # {A, B, C}
_GIVEN_RE   = re.compile(r"\bgiven\b", re.I)
_DO_RE      = re.compile(r"do\(([^)]+)\)", re.I)
_ASSIGN_RE  = re.compile(r"([A-Za-z_][A-Za-z0-9_]*)\s*=\s*([^\s,)]+)")


def _normalise(s: str) -> str:
    """Lower-case, collapse whitespace, normalise arrows."""
    s = _ARROW_RE.sub("→", s)
    return " ".join(s.split())


def _parse_node_set(token: str) -> list[str]:
    """
    Parse a node or set of nodes from a string.
    Handles: "X", "{X, Y}", "X, Y"
    Strips trailing punctuation (e.g. "?" or ".") from each node name.
    """
    token = token.strip()
    m = _SET_RE.match(token)
    if m:
        token = m.group(1)
    return [t.strip().rstrip("?.,!;:") for t in token.split(",") if t.strip().rstrip("?.,!;:")]


def _extract_given(query: str) -> tuple[str, list[str]]:
    """
    Split a query on 'given …' and return (query_without_given, Z_nodes).
    """
    norm = _normalise(query)
    parts = _GIVEN_RE.split(norm, maxsplit=1)
    if len(parts) == 2:
        return parts[0].strip(), _parse_node_set(parts[1].strip())
    return norm, []


def _parse_val(val_str: str) -> Any:
    """Cast a value string to int if possible, stripping trailing punctuation first."""
    val_str = val_str.rstrip("?.,!;:")
    try:
        return int(val_str)
    except ValueError:
        return val_str


def _parse_do(token: str) -> dict[str, Any]:
    """Parse do(X=v, Y=w) into {X: v, Y: w}. Values are cast to int if possible."""
    result: dict[str, Any] = {}
    for m in _ASSIGN_RE.finditer(token):
        result[m.group(1)] = _parse_val(m.group(2))
    return result


# ---------------------------------------------------------------------------
# Query type dispatch
# ---------------------------------------------------------------------------

def _is_dsep_query(q: str) -> bool:
    return bool(re.search(r"\bd.?sep(arat(ed|e))?\b|\bindependent\b|\bindependence\b", q, re.I))

def _is_cause_query(q: str) -> bool:
    return bool(re.search(r"\bcause[sd]?\b|\bcausal.effect\b|\baffect[s]?\b", q, re.I))

def _is_parents_query(q: str) -> bool:
    return bool(re.search(r"\bparent[s]?\b", q, re.I))

def _is_children_query(q: str) -> bool:
    return bool(re.search(r"\bchild(ren)?\b", q, re.I))

def _is_ancestors_query(q: str) -> bool:
    return bool(re.search(r"\bancestor[s]?\b", q, re.I))

def _is_descendants_query(q: str) -> bool:
    return bool(re.search(r"\bdescendant[s]?\b|\beffect[s]? of\b", q, re.I))

def _is_markov_query(q: str) -> bool:
    return bool(re.search(r"\bmarkov.blanket\b", q, re.I))

def _is_topo_query(q: str) -> bool:
    return bool(re.search(r"\btopolog\b|\border\b", q, re.I))

def _is_marginal_query(q: str) -> bool:
    return bool(re.search(r"\bprobability\b|\bp\(", q, re.I))

def _is_counterfactual_query(q: str) -> bool:
    return bool(re.search(r"\bwould\b|\bcounterfactual\b|\bhad been\b", q, re.I))


# ---------------------------------------------------------------------------
# Sub-solvers  (each returns list[CausalStep])
# ---------------------------------------------------------------------------

def _solve_dsep(graph: CausalGraph, query: str) -> list[CausalStep]:
    """
    Solve an independence / d-separation query and produce a traced proof.
    Pattern: "Is X independent of Y [given Z]?"
             "Is X d-separated from Y [given Z]?"
    """
    steps: list[CausalStep] = []
    q, Z = _extract_given(query)

    # Find two node names in the query
    nodes_found = [n for n in _NODE_RE.findall(q) if n in graph.nodes]

    # Heuristic: take first two distinct nodes mentioned
    seen: list[str] = []
    for n in nodes_found:
        if n not in seen:
            seen.append(n)
        if len(seen) == 2:
            break

    if len(seen) < 2:
        return [CausalStep(0, f"Could not identify two nodes in query: '{query}'", "error")]

    X, Y = seen[0], seen[1]
    Z_str = "{" + ", ".join(Z) + "}" if Z else "∅"

    steps.append(CausalStep(0,
        f"d-separation query:  {X} ⊥? {Y}  |  Z = {Z_str}", "query"))
    steps.append(CausalStep(0,
        f"Graph nodes: {sorted(graph.nodes)}", "graph"))
    steps.append(CausalStep(0,
        f"Graph edges: {sorted((p,c) for p,c in graph.edges)}", "graph"))

    if Z:
        # Show ancestors of Z
        z_anc: set[str] = set(Z)
        for z in Z:
            z_anc.update(graph.ancestors(z))
        steps.append(CausalStep(0,
            f"Ancestors of Z (for collider activation): anc(Z) ∪ Z = {sorted(z_anc)}", "graph"))

    steps.append(CausalStep(0, f"Running Bayes-ball from {{{X}}} toward {{{Y}}} …", "dsep"))

    is_dsep, ball_moves = d_separation_trace(graph, X, Y, Z if Z else None)

    for move in ball_moves:
        kind_map = {
            "pass": "dsep", "blocked": "blocked",
            "collider": "collider",
            # "reached" is an intermediate trace event, NOT the final verdict → use "dsep"
            "reached": "dsep",
        }
        steps.append(CausalStep(1, move.reason, kind_map.get(move.action, "dsep")))

    sep_symbol = "⊥" if is_dsep else "⊬⊥"
    verdict = "d-separated" if is_dsep else "d-connected"
    color_kind = "result"
    steps.append(CausalStep(0,
        f"Verdict:  {X} {sep_symbol} {Y} | {Z_str}  →  {verdict}",
        color_kind,
        f"{'independent' if is_dsep else 'NOT independent'} given Z",
    ))
    return steps


def _solve_cause(graph: CausalGraph, query: str) -> list[CausalStep]:
    """Solve "Does X cause Y?" via descendant check."""
    steps: list[CausalStep] = []
    nodes_found = [n for n in _NODE_RE.findall(query) if n in graph.nodes]
    seen: list[str] = []
    for n in nodes_found:
        if n not in seen:
            seen.append(n)
        if len(seen) == 2:
            break

    if len(seen) < 2:
        return [CausalStep(0, f"Could not identify two nodes in query: '{query}'", "error")]

    X, Y = seen[0], seen[1]
    steps.append(CausalStep(0, f"Causal-effect query: does {X} cause {Y}?", "query"))

    desc_X = graph.descendants(X)
    steps.append(CausalStep(1, f"Compute descendants({X}) = {sorted(desc_X)}", "graph"))

    if Y in desc_X:
        # Find a directed path
        path = _find_path(graph, X, Y)
        steps.append(CausalStep(1,
            f"{Y} ∈ descendants({X}) — directed path: " + " → ".join(path), "graph"))
        steps.append(CausalStep(0, f"Verdict: YES — {X} causally affects {Y}", "result",
                                "direct or mediated causal effect"))
    else:
        steps.append(CausalStep(1, f"{Y} ∉ descendants({X})", "graph"))
        # Check reverse
        desc_Y = graph.descendants(Y)
        if X in desc_Y:
            steps.append(CausalStep(0,
                f"Verdict: NO — {X} does not cause {Y}  "
                f"(but {Y} causes {X}: {X} ∈ descendants({Y}))", "result",
                "reverse direction"))
        else:
            steps.append(CausalStep(0,
                f"Verdict: NO — {X} does not directly or mediately cause {Y}", "result"))
    return steps


def _find_path(graph: CausalGraph, src: str, dst: str) -> list[str]:
    """BFS for a directed path from src to dst.  Returns the path or []."""
    from collections import deque
    queue: deque[list[str]] = deque([[src]])
    visited: set[str] = {src}
    while queue:
        path = queue.popleft()
        node = path[-1]
        if node == dst:
            return path
        for child in sorted(graph.children(node)):
            if child not in visited:
                visited.add(child)
                queue.append(path + [child])
    return []


def _solve_graph_query(graph: CausalGraph, query: str, kind: str) -> list[CausalStep]:
    """Solve a single-node structural query (parents/children/ancestors/descendants/MB)."""
    nodes_found = [n for n in _NODE_RE.findall(query) if n in graph.nodes]
    if not nodes_found:
        return [CausalStep(0, f"No known node found in query: '{query}'", "error")]

    node = nodes_found[0]
    steps: list[CausalStep] = [
        CausalStep(0, f"Structural query on node: {node}", "query"),
    ]

    if kind == "parents":
        result = sorted(graph.parents(node))
        steps.append(CausalStep(1, f"parents({node}) = {result}", "graph"))
        steps.append(CausalStep(0, f"Verdict: {result}", "result"))
    elif kind == "children":
        result = sorted(graph.children(node))
        steps.append(CausalStep(1, f"children({node}) = {result}", "graph"))
        steps.append(CausalStep(0, f"Verdict: {result}", "result"))
    elif kind == "ancestors":
        result = sorted(graph.ancestors(node))
        steps.append(CausalStep(1,
            f"ancestors({node}): traverse parents transitively", "graph"))
        steps.append(CausalStep(1, f"ancestors({node}) = {result}", "graph"))
        steps.append(CausalStep(0, f"Verdict: {result}", "result"))
    elif kind == "descendants":
        result = sorted(graph.descendants(node))
        steps.append(CausalStep(1,
            f"descendants({node}): traverse children transitively", "graph"))
        steps.append(CausalStep(1, f"descendants({node}) = {result}", "graph"))
        steps.append(CausalStep(0, f"Verdict: {result}", "result"))
    elif kind == "mb":
        result = sorted(graph.markov_blanket(node))
        p  = sorted(graph.parents(node))
        ch = sorted(graph.children(node))
        copo = sorted(set().union(*[graph.parents(c) for c in ch]) - {node})
        steps.append(CausalStep(1, f"parents({node})           = {p}", "graph"))
        steps.append(CausalStep(1, f"children({node})          = {ch}", "graph"))
        steps.append(CausalStep(1, f"co-parents (parents of children) = {copo}", "graph"))
        steps.append(CausalStep(0,
            f"Markov blanket({node}) = parents ∪ children ∪ co-parents = {result}",
            "result"))
    return steps


def _solve_topo(graph: CausalGraph) -> list[CausalStep]:
    """Return topological order with explanation."""
    steps = [CausalStep(0, "Topological order (Kahn's algorithm)", "query")]
    order = graph.topological_sort()
    # Show in-degrees
    in_deg: dict[str, int] = {n: 0 for n in graph.nodes}
    for p, c in graph.edges:
        in_deg[c] += 1
    steps.append(CausalStep(1,
        f"Initial in-degrees: {dict(sorted(in_deg.items()))}", "graph"))
    steps.append(CausalStep(1, f"Topological order: {order}", "graph"))
    steps.append(CausalStep(0, f"Verdict: {' → '.join(order)}", "result"))
    return steps


def _solve_marginal(scm: SCM, query: str) -> list[CausalStep]:
    """Compute P(X=v) or P(X=v | do(Y=w)) via full enumeration."""
    steps: list[CausalStep] = []

    # Extract do() clause if present
    do_match = _DO_RE.search(query)
    interventions: dict[str, Any] = {}
    if do_match:
        interventions = _parse_do(do_match.group(1))

    # Find target variable and value
    assigns = _ASSIGN_RE.findall(query)
    # Filter to variables that are in the model
    target_assigns = [(n, v) for n, v in assigns if n in scm.graph.nodes and n not in interventions]
    if not target_assigns:
        return [CausalStep(0, f"Could not parse target variable from: '{query}'", "error")]

    target_node, target_val_str = target_assigns[0]
    target_val: Any = _parse_val(target_val_str)

    do_str = f" | do({interventions})" if interventions else ""
    steps.append(CausalStep(0,
        f"Marginal query: P({target_node}={target_val}{do_str})", "query"))

    if interventions:
        steps.append(CausalStep(1,
            f"Interventions: {interventions}  (do-calculus: cut incoming edges)", "scm"))

    steps.append(CausalStep(1, "Enumerate all noise combinations …", "scm"))
    dist = scm.marginal(target_node, interventions=interventions if interventions else None)

    for val, prob in sorted(dist.items(), key=lambda x: x[0]):
        steps.append(CausalStep(1,
            f"P({target_node}={val}{do_str}) = {prob:.4f}", "scm"))

    prob_target = dist.get(target_val, 0.0)
    steps.append(CausalStep(0,
        f"Verdict: P({target_node}={target_val}{do_str}) = {prob_target:.4f}", "result"))
    return steps


def _solve_counterfactual(scm: SCM, query: str) -> list[CausalStep]:
    """
    Solve "If Y=w, what would X be?" style queries.
    Uses the twin-network approach: abduct → intervene → predict.
    """
    steps: list[CausalStep] = []

    assigns = _ASSIGN_RE.findall(query)
    model_assigns = [(n, _parse_val(v)) for n, v in assigns if n in scm.graph.nodes]

    # For "If X=v, what would Y be?" style — Y has no "=value" but is named in "would Y be"
    would_match_early = re.search(r"\bwould\b(.+?)\bbe\b", query, re.I)
    if would_match_early:
        extra_targets = [n for n in _NODE_RE.findall(would_match_early.group(1))
                         if n in scm.graph.nodes]
    else:
        extra_targets = []

    if len(model_assigns) < 1:
        return [CausalStep(0, f"Need at least 1 variable=value pair in: '{query}'", "error")]

    # Heuristic: last mentioned variable is the query target,
    # everything before is the observed fact / intervention.
    # User writes "If Y=0, what would X be?"
    # We'll treat the first as observation and second+ as intervention if possible.
    # Better: look for "would" to find the target.
    would_match = re.search(r"\bwould\b(.+?)\bbe\b", query, re.I)
    if would_match:
        target_nodes = [n for n in _NODE_RE.findall(would_match.group(1))
                        if n in scm.graph.nodes]
    elif extra_targets:
        target_nodes = extra_targets
    else:
        target_nodes = [model_assigns[-1][0]] if model_assigns else []

    # The given/observed part: assignments that mention "if" or "given"
    if_match = re.search(r"\bif\b(.+?)\bwould\b|\bgiven\b(.+?)\bwould\b", query, re.I)
    if if_match:
        cond_text = if_match.group(1) or if_match.group(2)
        cond_assigns = [(n, _parse_val(v)) for n, v in _ASSIGN_RE.findall(cond_text)
                        if n in scm.graph.nodes]
    else:
        cond_assigns = model_assigns[:1]

    observations: dict[str, Any] = {name: val for name, val in cond_assigns}

    # Intervention: flip one of the observed variables to a new value
    # For "If Y=0, what would X be if Y had been 1?", parse "had been"
    had_been = re.search(r"\bhad been\b\s+(\d+|\w+)", query, re.I)
    if had_been:
        # Find which node was being conditionalised and what the new value is
        int_val_str = had_been.group(1)
        # The node must be the one mentioned just before "had been"
        pre_had = query[:had_been.start()]
        pre_nodes = [n for n in _NODE_RE.findall(pre_had) if n in scm.graph.nodes]
        if pre_nodes:
            int_node = pre_nodes[-1]
            interventions = {int_node: _parse_val(int_val_str)}
        else:
            interventions = {}
    else:
        interventions = {}

    # If we have no separate intervention, treat the condition as do-intervention
    if not interventions:
        interventions = observations

    obs_str = ", ".join(f"{k}={v}" for k, v in observations.items())
    do_str  = ", ".join(f"{k}={v}" for k, v in interventions.items())
    tgt_str = ", ".join(target_nodes) if target_nodes else "?"

    steps.append(CausalStep(0,
        f"Counterfactual query: Given obs={{{obs_str}}}, if do({{{do_str}}}), what is {tgt_str}?",
        "query"))

    # Step 1: Abduction
    steps.append(CausalStep(0, "Step 1 — Abduction: find noise U consistent with observations", "scm"))
    consistent = scm.abduction(observations)
    if not consistent:
        steps.append(CausalStep(1,
            f"No consistent noise assignment found for {observations}", "error"))
        return steps

    steps.append(CausalStep(1,
        f"Found {len(consistent)} consistent noise assignment(s)", "scm"))
    for noise, abduct_steps in consistent[:3]:   # show up to 3
        noise_str = ", ".join(f"U_{k}={v}" for k, v in noise.items())
        steps.append(CausalStep(1, f"  Noise: {{{noise_str}}}", "scm"))
        for s in abduct_steps:
            steps.append(CausalStep(2, s.detail, "abduct"))

    # Step 2: Intervention
    steps.append(CausalStep(0, f"Step 2 — Intervention: apply do({{{do_str}}})", "scm"))

    # Step 3: Prediction
    steps.append(CausalStep(0, "Step 3 — Prediction: replay model with fixed noise", "scm"))
    cf_results: list[dict] = []
    for noise, _ in consistent:
        cf_values, predict_steps = scm.predict(noise, interventions=interventions)
        cf_results.append(cf_values)
        for s in predict_steps:
            steps.append(CausalStep(2, s.detail, "predict"))
        break  # show first consistent assignment

    if cf_results:
        tgt_vals = {t: cf_results[0].get(t, "?") for t in target_nodes}
        if len(cf_results) == 1 or all(
            all(r.get(t) == cf_results[0].get(t) for t in target_nodes)
            for r in cf_results
        ):
            val_str = ", ".join(f"{t}={v}" for t, v in tgt_vals.items())
            steps.append(CausalStep(0,
                f"Verdict: {val_str}  (identifiable counterfactual)", "result"))
        else:
            steps.append(CausalStep(0,
                f"Verdict: multiple consistent outcomes — counterfactual not point-identified",
                "result"))

    return steps


# ---------------------------------------------------------------------------
# Main entry point
# ---------------------------------------------------------------------------

def solve_causal(
    model_str: str,
    query: str,
    scm: SCM | None = None,
) -> list[CausalStep] | None:
    """
    Parse *model_str* as a CausalGraph, then dispatch *query* to the
    appropriate sub-solver.

    Parameters
    ----------
    model_str : edge-list string, e.g. "Season→Rain, Season→Sprinkler, Rain→WetGrass"
    query     : natural-language query (see module docstring for supported forms)
    scm       : optional pre-built SCM; if None and SCM query detected, the
                built-in Wet-Grass SCM is used when the graph matches.

    Returns a list of CausalStep or None on a fatal parse error.
    """
    try:
        graph = graph_from_string(model_str)
    except Exception as exc:
        return [CausalStep(0, f"Model parse error: {exc}", "error")]

    q_low = query.lower().strip()

    # --- Graph-only queries ---
    if _is_dsep_query(q_low):
        return _solve_dsep(graph, query)

    if _is_cause_query(q_low):
        return _solve_cause(graph, query)

    if _is_parents_query(q_low):
        return _solve_graph_query(graph, query, "parents")

    if _is_children_query(q_low):
        return _solve_graph_query(graph, query, "children")

    if _is_ancestors_query(q_low):
        return _solve_graph_query(graph, query, "ancestors")

    if _is_descendants_query(q_low):
        return _solve_graph_query(graph, query, "descendants")

    if _is_markov_query(q_low):
        return _solve_graph_query(graph, query, "mb")

    if _is_topo_query(q_low):
        return _solve_topo(graph)

    # --- SCM queries (need an SCM object) ---
    if scm is None:
        # Try the built-in Wet-Grass SCM if the graph looks compatible
        wg_nodes = {"Season", "Rain", "Sprinkler", "WetGrass"}
        if graph.nodes == wg_nodes:
            scm = make_wet_grass_scm()

    if scm is None and (_is_marginal_query(q_low) or _is_counterfactual_query(q_low)):
        return [CausalStep(0,
            "SCM required for probability/counterfactual queries. "
            "Use the built-in Wet-Grass model or supply your own SCM.", "error")]

    if _is_marginal_query(q_low):
        return _solve_marginal(scm, query)

    if _is_counterfactual_query(q_low):
        return _solve_counterfactual(scm, query)

    # Fallback: try d-separation anyway
    if any(n in query for n in graph.nodes):
        return _solve_dsep(graph, query)

    return [CausalStep(0, f"Query not recognised: '{query}'", "error")]


# ---------------------------------------------------------------------------
# Render helpers (for CLI and tests)
# ---------------------------------------------------------------------------

def print_causal_trace(steps: list[CausalStep], indent: int = 0) -> None:
    """Pretty-print a causal reasoning trace to stdout."""
    INDENT = "  "
    KIND_PREFIX = {
        "query":     "?  ",
        "graph":     "G  ",
        "dsep":      "~  ",
        "blocked":   "✗  ",
        "collider":  "⊞  ",
        "result":    "✓  ",
        "scm":       "Σ  ",
        "abduct":    "←  ",
        "predict":   "→  ",
        "error":     "!  ",
    }
    for step in steps:
        pad = INDENT * (indent + step.depth)
        prefix = KIND_PREFIX.get(step.kind, "   ")
        note = f"  [{step.note}]" if step.note else ""
        print(f"{pad}{prefix}{step.text}{note}")
