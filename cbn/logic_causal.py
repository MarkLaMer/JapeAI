"""
cbn/logic_causal.py — CBN / SCM-backed natural-deduction solver (complete FOL).

Accepts the same (assumptions, goal) input as csp/fol_csp.py and returns
FOLProofStep objects rendered by the same render_fol_csp_steps() function,
so the GUI proof pane looks identical to the CSP solver output.

This module builds the causal graph and SCM, then runs an independent
factor-style propagation solver in cbn/factor_bp.py.  The CBN / SCM layer
provides:
  1. dependency structure via CausalGraph
  2. deterministic reachability / ordering via SCM
  3. guidance for the native proof engine's message-passing schedule
"""
from __future__ import annotations

from dataclasses import dataclass

from parser.ast import Formula, Atom, And, Imp, Not, Or, ForAll, Exists, Var, Predicate
from cbn.graph import CausalGraph
from cbn.scm import SCM, SCMVariable, NoiseVar
from csp.fol_csp import render_fol_csp_steps, FOLProofStep
from cbn.factor_bp import solve_factor_bp


def _atom_nodes(formula: Formula) -> set[str]:
    """Return the string labels of all atomic sub-formulas."""
    if isinstance(formula, (Atom, Var, Predicate)):
        return {str(formula)}
    if isinstance(formula, Not):
        return _atom_nodes(formula.child)
    if isinstance(formula, (And, Or, Imp)):
        return _atom_nodes(formula.left) | _atom_nodes(formula.right)
    if isinstance(formula, (ForAll, Exists)):
        return _atom_nodes(formula.body)
    return {str(formula)}


def _build_graph(
    assumptions: list[Formula],
    goal: Formula,
) -> tuple[CausalGraph, dict[str, Formula]]:
    """
    Build a CausalGraph from implications in the assumptions.

    Nodes  : all unique atomic sub-formulas (labelled by str()).
    Edges  : for each Imp(A, B) in assumptions, edges from every atom of A
             to every atom of B that is not already an atom of A.
    """
    label_map: dict[str, Formula] = {}
    for formula in list(assumptions) + [goal]:
        for label in _atom_nodes(formula):
            if label not in label_map:
                label_map[label] = Atom(label)

    for formula in assumptions:
        if isinstance(formula, (Atom, Var, Predicate)):
            label_map[str(formula)] = formula
    if isinstance(goal, (Atom, Var, Predicate)):
        label_map[str(goal)] = goal

    edges: list[tuple[str, str]] = []
    for formula in assumptions:
        if not isinstance(formula, Imp):
            continue
        ant_labels = _atom_nodes(formula.left)
        con_labels = _atom_nodes(formula.right)
        for ant in ant_labels:
            for con in con_labels:
                if ant != con:
                    edges.append((ant, con))

    edges = list(dict.fromkeys(edges))

    nodes = set(label_map.keys())
    safe: list[tuple[str, str]] = []
    for edge in edges:
        try:
            CausalGraph(nodes, safe + [edge])
            safe.append(edge)
        except ValueError:
            pass

    return CausalGraph(nodes, safe), label_map


def _build_causal_graph(
    assumptions: list[Formula],
    goal: Formula,
) -> tuple[CausalGraph, set[str]]:
    """Compatibility wrapper returning (graph, all_atom_labels)."""
    graph, _ = _build_graph(assumptions, goal)
    all_labels: set[str] = set()
    for formula in list(assumptions) + [goal]:
        all_labels.update(_atom_nodes(formula))
    return graph, all_labels


def _dsep_filter(
    domain: set[Formula],
    graph: CausalGraph,
    assumption_atoms: set[str],
    goal_atoms: set[str],
) -> set[Formula]:
    """
    Keep formulas that are causally connected to the goal atoms.

    This helper is retained for compatibility and tests. The independent
    factor solver does not depend on it for correctness.
    """
    if not graph.nodes or not goal_atoms:
        return domain

    observed = assumption_atoms & graph.nodes
    goal_nodes = goal_atoms & graph.nodes

    kept: set[Formula] = set()
    for formula in domain:
        formula_atoms = _atom_nodes(formula) & graph.nodes
        if not formula_atoms:
            kept.add(formula)
            continue
        relevant = any(
            not graph.d_separated(atom, goal_node, observed)
            for atom in formula_atoms
            for goal_node in goal_nodes
            if atom != goal_node
        )
        if relevant or (formula_atoms & goal_nodes):
            kept.add(formula)

    return kept if kept else domain


def _build_scm(
    assumptions: list[Formula],
    graph: CausalGraph,
    label_map: dict[str, Formula],
) -> SCM:
    """
    Build an SCM over the causal graph.

    Structural equations
    --------------------
    • Root assumptions (atoms given as facts):
          eq(∅, U) = U  with U ~ PointMass(1)  → always True
    • Derivable atoms (consequents of implications):
          eq({parents}, U) = 1 if any antecedent set is fully 1, else U
          with U ~ PointMass(0)  → False unless derived
    • Unknown atoms:
          eq(∅, U) = U  with U ~ PointMass(0)  → always False
    """
    del label_map

    given_labels: set[str] = set()
    for formula in assumptions:
        if isinstance(formula, (Atom, Var, Predicate)):
            given_labels.add(str(formula))

    implication_rules: dict[str, list[tuple[frozenset[str], Formula]]] = {
        node: [] for node in graph.nodes
    }
    for formula in assumptions:
        if not isinstance(formula, Imp):
            continue
        ant_labels = frozenset(_atom_nodes(formula.left))
        for con_label in _atom_nodes(formula.right):
            if con_label in implication_rules:
                implication_rules[con_label].append((ant_labels, formula))

    variables: dict[str, SCMVariable] = {}
    for node in graph.nodes:
        parents_list = sorted(graph.parents(node))

        if node in given_labels:
            def _make_root_eq():
                def eq(pa: dict, u: int) -> int:
                    return u
                return eq

            variable = SCMVariable(
                name=node,
                parents=parents_list,
                equation=_make_root_eq(),
                noise=NoiseVar(f"U_{node}", [1], [1.0]),
                domain=[0, 1],
            )
        elif implication_rules[node]:
            rules = implication_rules[node]

            def _make_derived_eq(rule_list):
                def eq(pa: dict, u: int) -> int:
                    for ant_set, _ in rule_list:
                        if all(pa.get(atom, 0) == 1 for atom in ant_set):
                            return 1
                    return u
                return eq

            variable = SCMVariable(
                name=node,
                parents=parents_list,
                equation=_make_derived_eq(rules),
                noise=NoiseVar(f"U_{node}", [0], [1.0]),
                domain=[0, 1],
            )
        else:
            def _make_false_eq():
                def eq(pa: dict, u: int) -> int:
                    return u
                return eq

            variable = SCMVariable(
                name=node,
                parents=parents_list,
                equation=_make_false_eq(),
                noise=NoiseVar(f"U_{node}", [0], [1.0]),
                domain=[0, 1],
            )

        variables[node] = variable

    return SCM(graph, variables)


@dataclass(frozen=True)
class CausalProofLine:
    """A single derived formula paired with the rule label used."""
    conclusion: str
    action: str


def solve_logic_causal(
    assumptions: list[Formula],
    goal: Formula,
) -> list[FOLProofStep] | None:
    """
    CBN / SCM-backed FOL natural deduction solver.

    Builds the causal graph and SCM, then runs the independent factor /
    message-passing proof engine in cbn/factor_bp.py.

    Handles all connectives and quantifiers: ∀ ∃ ¬ ∨ ∧ → plus RAA.
    """
    graph: CausalGraph | None = None
    scm: SCM | None = None
    try:
        graph, label_map = _build_graph(assumptions, goal)
        scm = _build_scm(assumptions, graph, label_map)
    except Exception:
        pass

    return solve_factor_bp(assumptions, goal, graph=graph, scm=scm)


def explain_logic_causal(
    assumptions: list[Formula],
    goal: Formula,
) -> list[CausalProofLine] | None:
    """
    Return the proof as a flat list of (conclusion, rule_label) pairs.
    Used by the CLI for the "formula   (rule)" output format.
    """
    steps = solve_logic_causal(assumptions, goal)
    if steps is None:
        return None

    lines: list = []
    render_fol_csp_steps(steps, lines)

    result: list[CausalProofLine] = []
    non_derived = {"assumption", "assumptions", "premise", "premises", "hyp"}
    for depth, formula_str, rule_label, note in lines:
        if rule_label in non_derived:
            continue
        indent = "  " * depth
        note_part = f"  [{note}]" if note else ""
        result.append(CausalProofLine(
            conclusion=f"{indent}{formula_str}",
            action=f"{rule_label}{note_part}",
        ))

    return result


def render_logic_causal_steps(
    steps: list[FOLProofStep],
    lines: list,
) -> None:
    """
    Convert CBN proof steps to (depth, formula, rule_label, note) display
    tuples using the same rendering as the FOL CSP solver.
    """
    render_fol_csp_steps(steps, lines)
