"""
cbn/graph.py — Causal Bayesian Network graph layer.

Provides:
  CausalGraph  — a directed acyclic graph (DAG) of named nodes and causal edges.
  d_separated  — Bayes-ball d-separation test: X ⊥ Y | Z

Both systems (CBN and SCM) share this graph backbone.  The SCM layer in scm.py
replaces the CPD tables with structural-equation + noise pairs and adds the
abduction step, but it inherits the same graph object.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import FrozenSet, Iterable


# ---------------------------------------------------------------------------
# CausalGraph
# ---------------------------------------------------------------------------

class CausalGraph:
    """
    Directed acyclic graph representing causal structure.

    Nodes are plain strings.  Edges are directed (parent → child).
    """

    def __init__(
        self,
        nodes: Iterable[str],
        edges: Iterable[tuple[str, str]],
    ) -> None:
        self._nodes: set[str] = set(nodes)
        self._edges: set[tuple[str, str]] = set()

        for parent, child in edges:
            if parent not in self._nodes:
                raise ValueError(f"Unknown parent node: '{parent}'")
            if child not in self._nodes:
                raise ValueError(f"Unknown child node: '{child}'")
            if parent == child:
                raise ValueError(f"Self-loop not allowed: '{parent}' → '{child}'")
            self._edges.add((parent, child))

        self._validate_acyclic()

    # ------------------------------------------------------------------ #
    # Properties
    # ------------------------------------------------------------------ #

    @property
    def nodes(self) -> frozenset[str]:
        return frozenset(self._nodes)

    @property
    def edges(self) -> frozenset[tuple[str, str]]:
        return frozenset(self._edges)

    def _validate_node(self, node: str) -> None:
        if node not in self._nodes:
            raise ValueError(f"Unknown node: '{node}'")

    def _validate_nodes(self, nodes: Iterable[str]) -> None:
        invalid = set(nodes) - self._nodes
        if invalid:
            raise ValueError(f"Unknown graph node(s): {sorted(invalid)}")

    # ------------------------------------------------------------------ #
    # Graph traversal
    # ------------------------------------------------------------------ #

    def parents(self, node: str) -> frozenset[str]:
        """All nodes with a direct edge INTO *node*."""
        self._validate_node(node)
        return frozenset(p for p, c in self._edges if c == node)

    def children(self, node: str) -> frozenset[str]:
        """All nodes with a direct edge OUT OF *node*."""
        self._validate_node(node)
        return frozenset(c for p, c in self._edges if p == node)

    def ancestors(self, node: str) -> frozenset[str]:
        """All nodes that can reach *node* through directed edges (parents, grandparents, …)."""
        self._validate_node(node)
        result: set[str] = set()
        frontier: set[str] = set(self.parents(node))
        while frontier:
            n = frontier.pop()
            if n not in result:
                result.add(n)
                frontier.update(self.parents(n))
        return frozenset(result)

    def descendants(self, node: str) -> frozenset[str]:
        """All nodes reachable from *node* through directed edges (children, grandchildren, …)."""
        self._validate_node(node)
        result: set[str] = set()
        frontier: set[str] = set(self.children(node))
        while frontier:
            n = frontier.pop()
            if n not in result:
                result.add(n)
                frontier.update(self.children(n))
        return frozenset(result)

    def markov_blanket(self, node: str) -> frozenset[str]:
        """
        Markov blanket of *node*:
          parents ∪ children ∪ {other parents of each child}
        """
        self._validate_node(node)
        mb: set[str] = set()
        mb.update(self.parents(node))
        for child in self.children(node):
            mb.add(child)
            mb.update(self.parents(child) - {node})
        return frozenset(mb)

    def topological_sort(self) -> list[str]:
        """Return all nodes in a topological order (roots first). Kahn's algorithm."""
        in_deg: dict[str, int] = {n: 0 for n in self._nodes}
        for _, c in self._edges:
            in_deg[c] += 1

        # Sort for deterministic output
        frontier: list[str] = sorted(n for n, d in in_deg.items() if d == 0)
        order: list[str] = []
        while frontier:
            node = frontier.pop(0)
            order.append(node)
            for child in sorted(self.children(node)):
                in_deg[child] -= 1
                if in_deg[child] == 0:
                    frontier.append(child)
            frontier.sort()
        return order

    # ------------------------------------------------------------------ #
    # D-separation — Bayes-ball algorithm
    # ------------------------------------------------------------------ #

    def d_separated(
        self,
        X: str | Iterable[str],
        Y: str | Iterable[str],
        Z: str | Iterable[str] | None = None,
    ) -> bool:
        """
        Test whether X and Y are d-separated given Z.

        Returns True  → X ⊥ Y | Z  (conditionally independent)
        Returns False → X and Y are d-connected (not independent)

        Implementation: Bayes-ball (Shachter 1998).
        Each "ball" state is (node, direction) where direction is:
          "up"   — ball arrived from a child, travelling toward parents
          "down" — ball arrived from a parent, travelling toward children

        Propagation rules:
          (node, up),   node ∉ Z : pass to parents (up) and children (down) [fork/chain]
          (node, up),   node ∈ Z : blocked (conditioned non-collider)
          (node, down), node ∉ Z : pass to children (down)
          (node, down), node ∈ Z_ancestors : collider activated — pass to parents (up)
        """
        if isinstance(X, str):
            X = {X}
        if isinstance(Y, str):
            Y = {Y}
        Z_set: set[str] = set(Z) if Z is not None else set()

        X_set = set(X)
        Y_set = set(Y)
        self._validate_nodes(X_set | Y_set | Z_set)

        # Pre-compute the "Z ancestors" set used for collider activation.
        # A collider V is activated if V itself or any of V's descendants is in Z.
        # Equivalently: V activates iff V ∈ ancestors(Z) ∪ Z.
        Z_ancestors: set[str] = set(Z_set)
        for z in Z_set:
            Z_ancestors.update(self.ancestors(z))

        # Bayes-ball reachability from X
        visited: set[tuple[str, str]] = set()
        queue: list[tuple[str, str]] = []

        for x in X_set:
            queue.append((x, "up"))
            queue.append((x, "down"))

        while queue:
            node, direction = queue.pop(0)
            state = (node, direction)
            if state in visited:
                continue
            visited.add(state)

            # If we reach any Y node, X and Y are d-connected.
            if node in Y_set:
                return False

            if direction == "up":
                # Ball travelling upstream (arrived from child).
                if node not in Z_set:
                    # Unobserved non-collider: pass to parents and siblings.
                    for parent in self.parents(node):
                        queue.append((parent, "up"))
                    for child in self.children(node):
                        queue.append((child, "down"))
                # If node ∈ Z_set: path is blocked (observed non-collider).

            else:  # direction == "down"
                # Ball travelling downstream (arrived from parent).
                if node not in Z_set:
                    # Unobserved: pass downstream to children.
                    for child in self.children(node):
                        queue.append((child, "down"))

                # Collider activation: if node or a descendant is observed,
                # the collider opens and the ball can travel upstream.
                if node in Z_ancestors:
                    for parent in self.parents(node):
                        queue.append((parent, "up"))

        # Y was never reached — d-separated.
        return True

    # ------------------------------------------------------------------ #
    # Internal helpers
    # ------------------------------------------------------------------ #

    def _validate_acyclic(self) -> None:
        """Kahn's algorithm to detect cycles."""
        in_deg: dict[str, int] = {n: 0 for n in self._nodes}
        for _, c in self._edges:
            in_deg[c] += 1

        frontier = [n for n, d in in_deg.items() if d == 0]
        visited_count = 0
        while frontier:
            node = frontier.pop()
            visited_count += 1
            for child in self.children(node):
                in_deg[child] -= 1
                if in_deg[child] == 0:
                    frontier.append(child)

        if visited_count != len(self._nodes):
            raise ValueError("CausalGraph contains a cycle — must be a DAG.")

    def __repr__(self) -> str:
        edges = ", ".join(f"{p}→{c}" for p, c in sorted(self._edges))
        return f"CausalGraph(nodes={sorted(self._nodes)}, edges=[{edges}])"


# ---------------------------------------------------------------------------
# D-separation trace  (for the NL solver — produces human-readable steps)
# ---------------------------------------------------------------------------

@dataclass
class BallMove:
    """One ball movement in the Bayes-ball algorithm."""
    node: str
    direction: str      # "up" or "down"
    action: str         # "pass", "blocked", "collider", "reached"
    reason: str         # human-readable explanation
    targets: list[str] = field(default_factory=list)


def d_separation_trace(
    graph: CausalGraph,
    X: str | Iterable[str],
    Y: str | Iterable[str],
    Z: str | Iterable[str] | None = None,
) -> tuple[bool, list[BallMove]]:
    """
    Same as CausalGraph.d_separated but also returns an ordered trace of
    every ball movement, suitable for rendering as proof steps.

    Returns (is_d_separated: bool, moves: list[BallMove]).
    """
    if isinstance(X, str):
        X = {X}
    if isinstance(Y, str):
        Y = {Y}
    Z_set: set[str] = set(Z) if Z is not None else set()

    X_set = set(X)
    Y_set = set(Y)
    invalid = (X_set | Y_set | Z_set) - graph.nodes
    if invalid:
        raise ValueError(f"Unknown graph node(s): {sorted(invalid)}")

    Z_ancestors: set[str] = set(Z_set)
    for z in Z_set:
        Z_ancestors.update(graph.ancestors(z))

    visited: set[tuple[str, str]] = set()
    queue: list[tuple[str, str]] = []
    trace: list[BallMove] = []

    for x in X_set:
        queue.append((x, "up"))
        queue.append((x, "down"))

    while queue:
        node, direction = queue.pop(0)
        state = (node, direction)
        if state in visited:
            continue
        visited.add(state)

        arrow = "↑" if direction == "up" else "↓"

        if node in Y_set:
            trace.append(BallMove(
                node=node, direction=direction,
                action="reached",
                reason=f"({node}, {arrow}) {node} ∈ Y — d-connected path found",
                targets=[],
            ))
            return False, trace

        if direction == "up":
            if node not in Z_set:
                parents_list = sorted(graph.parents(node))
                children_list = sorted(graph.children(node))
                targets = parents_list + children_list
                trace.append(BallMove(
                    node=node, direction=direction,
                    action="pass",
                    reason=(f"({node}, {arrow}) {node} ∉ Z → unobserved non-collider: "
                            f"passes to parents {parents_list} and children {children_list}"),
                    targets=targets,
                ))
                for parent in parents_list:
                    queue.append((parent, "up"))
                for child in children_list:
                    queue.append((child, "down"))
            else:
                trace.append(BallMove(
                    node=node, direction=direction,
                    action="blocked",
                    reason=f"({node}, {arrow}) {node} ∈ Z → observed non-collider: path blocked",
                    targets=[],
                ))

        else:  # down
            downstream_targets: list[str] = []
            upstream_targets: list[str] = []

            if node not in Z_set:
                downstream_targets = sorted(graph.children(node))
                for child in downstream_targets:
                    queue.append((child, "down"))

            if node in Z_ancestors:
                upstream_targets = sorted(graph.parents(node))
                for parent in upstream_targets:
                    queue.append((parent, "up"))

            # Decide what to record in the trace.
            # Key distinction:
            #   node ∈ Z_set  → directly observed; downstream is BLOCKED for this direction
            #   node ∈ Z_ancestors but ∉ Z_set → collider activated by a descendant in Z
            if node in Z_set:
                # The chain / fork path going through this node is blocked (conditioned on).
                # Even though the Bayes-ball also sends the ball upstream (collider activation),
                # the primary semantic for this step is "blocked chain node".
                if upstream_targets:
                    trace.append(BallMove(
                        node=node, direction=direction,
                        action="blocked",
                        reason=(f"({node}, {arrow}) {node} ∈ Z → conditioned on: "
                                f"chain blocked downstream; collider activation sends ball to "
                                f"parents {upstream_targets}"),
                        targets=upstream_targets,
                    ))
                else:
                    trace.append(BallMove(
                        node=node, direction=direction,
                        action="blocked",
                        reason=f"({node}, {arrow}) {node} ∈ Z → conditioned on: path blocked",
                        targets=[],
                    ))
            elif node in Z_ancestors:
                # Collider activated by an observed descendant.
                trace.append(BallMove(
                    node=node, direction=direction,
                    action="collider",
                    reason=(f"({node}, {arrow}) descendant of {node} ∈ Z → collider activated → "
                            f"passes to parents {upstream_targets} and children {downstream_targets}"),
                    targets=upstream_targets + downstream_targets,
                ))
            elif downstream_targets:
                trace.append(BallMove(
                    node=node, direction=direction,
                    action="pass",
                    reason=(f"({node}, {arrow}) {node} ∉ Z → passes downstream to "
                            f"{downstream_targets}"),
                    targets=downstream_targets,
                ))
            else:
                trace.append(BallMove(
                    node=node, direction=direction,
                    action="blocked",
                    reason=f"({node}, {arrow}) {node} has no children and is not in anc(Z) → dead end",
                    targets=[],
                ))

    return True, trace


# ---------------------------------------------------------------------------
# Convenience: build from edge-list string  "A→B, A→C, B→D"
# ---------------------------------------------------------------------------

def graph_from_string(edge_str: str) -> CausalGraph:
    """
    Parse a compact edge-list string and return a CausalGraph.

    Accepted separators: "→", "->", "-->"
    Edges are comma-separated (or newline-separated).

    Example:
        graph_from_string("Season→Rain, Season→Sprinkler, Rain→WetGrass, Sprinkler→WetGrass")
    """
    import re
    nodes: set[str] = set()
    edges: list[tuple[str, str]] = []

    # Normalise arrow variants
    text = edge_str.replace("-->", "→").replace("->", "→")

    for token in re.split(r"[,\n]+", text):
        token = token.strip()
        if not token:
            continue
        if "→" not in token:
            # Single node declaration (no edge)
            nodes.add(token.strip())
            continue
        parts = token.split("→", 1)
        parent = parts[0].strip()
        child  = parts[1].strip()
        if not parent or not child:
            raise ValueError(f"Malformed edge: '{token}'")
        nodes.add(parent)
        nodes.add(child)
        edges.append((parent, child))

    return CausalGraph(nodes, edges)
