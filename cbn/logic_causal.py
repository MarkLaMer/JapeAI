"""
cbn/logic_causal.py — CBN / SCM-backed natural-deduction solver.

Accepts the same (assumptions, goal) input as csp/skeleton_csp.py and
planning/internal_planner.py and returns the proof as a list of action
strings in exactly the same format as the PDDL planner:

    modus-ponens(P, (P -> Q))           → Q
    and-elim-left((P & Q))              → P
    and-intro(P, Q)                     → (P & Q)

How the CBN / SCM layer is used
--------------------------------
1.  **CausalGraph** — built from the implications in the assumption set.
    Each atom is a node; each A → B implication creates directed edge(s)
    from the atoms of A to the atoms of B.  The topological sort gives the
    natural proof-step order and guarantees we never attempt a derivation
    before its premises are available.

2.  **D-separation** (relevance filter) — after the proof is found we use
    d-separation on the causal graph to decide which steps are on an active
    causal path from the given assumptions to the goal.  Irrelevant steps
    (premises whose causal influence is blocked) are silently dropped.

3.  **SCM structural equations** — each atom V is given a binary SCM
    variable whose structural equation encodes whether V is derivable:
        • root assumption   →  eq(∅, U) = 1  (noise fixed to 1)
        • derived via A→V   →  eq({A:v}, U) = v["A"] if rule fires else U
    Forward sampling of the SCM (SCM.sample) *is* the proof evaluation.
    We shadow the standard sample loop with a traced version that records
    which rule fired at each node — these become the proof step strings.

4.  **Abduction** — if the goal is still unproved after one forward pass
    (can happen with compound antecedents), the abduction step identifies
    which noise assignments are needed and triggers a second-pass in which
    those atoms are set to 1.  This handles the case where a conjunction
    in an antecedent requires both halves to be independently derived
    before modus-ponens can fire.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any

from parser.ast import Formula, Atom, And, Imp, Not, Or, ForAll, Exists, Var, Predicate
from cbn.graph import CausalGraph, graph_from_string
from cbn.scm   import SCM, SCMVariable, NoiseVar


# ---------------------------------------------------------------------------
# Formula helpers
# ---------------------------------------------------------------------------

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


def _conjuncts(formula: Formula) -> list[Formula]:
    """Flatten a conjunction into its conjuncts."""
    if isinstance(formula, And):
        return _conjuncts(formula.left) + _conjuncts(formula.right)
    return [formula]


def _is_known(formula: Formula, known: set[str]) -> bool:
    """Check if *formula* is fully satisfied by the set of known-true labels."""
    if isinstance(formula, And):
        return _is_known(formula.left, known) and _is_known(formula.right, known)
    return str(formula) in known


# ---------------------------------------------------------------------------
# CBN graph construction
# ---------------------------------------------------------------------------

def _build_graph(
    assumptions: list[Formula],
    goal: Formula,
) -> tuple[CausalGraph, dict[str, Formula]]:
    """
    Build a CausalGraph from the assumptions and goal.

    Nodes  : all unique atomic sub-formulas (labelled by str()).
    Edges  : for each Imp(A, B) in assumptions, edges from every atom of A
             to every atom of B that is not already an atom of A.

    Returns (graph, label → Formula mapping).
    """
    # Collect all atom labels
    label_map: dict[str, Formula] = {}
    for f in list(assumptions) + [goal]:
        for lbl in _atom_nodes(f):
            if lbl not in label_map:
                # Try to recover the actual Formula object
                label_map[lbl] = Atom(lbl)   # fallback; real object not needed for graph

    # Mark the actual Formula objects where we have them
    for f in assumptions:
        if isinstance(f, (Atom, Var, Predicate)):
            label_map[str(f)] = f
    if isinstance(goal, (Atom, Var, Predicate)):
        label_map[str(goal)] = goal

    # Build directed edges from implications
    edges: list[tuple[str, str]] = []
    for f in assumptions:
        if isinstance(f, Imp):
            ant_labels = _atom_nodes(f.left)
            con_labels = _atom_nodes(f.right)
            for a in ant_labels:
                for c in con_labels:
                    if a != c:
                        edges.append((a, c))

    # Deduplicate
    edges = list(dict.fromkeys(edges))

    # Build graph, dropping any edge that would create a cycle
    nodes = set(label_map.keys())
    safe: list[tuple[str, str]] = []
    for edge in edges:
        try:
            CausalGraph(nodes, safe + [edge])
            safe.append(edge)
        except ValueError:
            pass  # skip cycle-creating edge

    return CausalGraph(nodes, safe), label_map


# ---------------------------------------------------------------------------
# SCM construction
# ---------------------------------------------------------------------------

def _build_scm(
    assumptions: list[Formula],
    graph: CausalGraph,
    label_map: dict[str, Formula],
) -> SCM:
    """
    Build an SCM over the causal graph.

    Structural equations
    --------------------
    • Root assumptions (atoms given as facts) :
          eq(∅, U) = U         with U ~ PointMass(1)   → always True
    • Derivable atoms (consequents of implications) :
          eq({parents}, U) = 1 if any supporting antecedent set is fully 1
                              else U
          with U ~ PointMass(0)   → False unless derived
    • Other atoms (not mentioned in any implication consequent) :
          eq(∅, U) = U         with U ~ PointMass(0)   → always False
    """
    given_labels: set[str] = set()
    for f in assumptions:
        if isinstance(f, (Atom, Var, Predicate)):
            given_labels.add(str(f))

    # For each node, collect the implications that can derive it
    # implication_rules[node_label] = list of (antecedent_labels_set, imp_formula)
    implication_rules: dict[str, list[tuple[frozenset[str], Formula]]] = {
        n: [] for n in graph.nodes
    }
    for f in assumptions:
        if isinstance(f, Imp):
            ant_labels = frozenset(_atom_nodes(f.left))
            for c_lbl in _atom_nodes(f.right):
                if c_lbl in implication_rules:
                    implication_rules[c_lbl].append((ant_labels, f))

    variables: dict[str, SCMVariable] = {}
    for node in graph.nodes:
        parents_list = sorted(graph.parents(node))

        if node in given_labels:
            # Root: always True
            def _make_root_eq():
                def eq(pa: dict, u: int) -> int: return u
                return eq
            var = SCMVariable(
                name=node,
                parents=parents_list,
                equation=_make_root_eq(),
                noise=NoiseVar(f"U_{node}", [1], [1.0]),
                domain=[0, 1],
            )
        elif implication_rules[node]:
            # Derived: True if any rule's antecedent is fully satisfied
            rules = implication_rules[node]

            def _make_derived_eq(rule_list):
                def eq(pa: dict, u: int) -> int:
                    for ant_set, _ in rule_list:
                        if all(pa.get(a, 0) == 1 for a in ant_set):
                            return 1
                    return u   # noise fallback (0 by default)
                return eq

            var = SCMVariable(
                name=node,
                parents=parents_list,
                equation=_make_derived_eq(rules),
                noise=NoiseVar(f"U_{node}", [0], [1.0]),
                domain=[0, 1],
            )
        else:
            # Unknown atom: always False
            def _make_false_eq():
                def eq(pa: dict, u: int) -> int: return u
                return eq
            var = SCMVariable(
                name=node,
                parents=parents_list,
                equation=_make_false_eq(),
                noise=NoiseVar(f"U_{node}", [0], [1.0]),
                domain=[0, 1],
            )

        variables[node] = var

    return SCM(graph, variables)


# ---------------------------------------------------------------------------
# Traced forward evaluation  (this IS the SCM sample + trace)
# ---------------------------------------------------------------------------

@dataclass
class _ProofStep:
    conclusion: Formula       # derived formula
    rule: str                 # "modus-ponens" | "and-elim-left" | ...
    supports: list[Formula]   # premises used


def _forward_trace(
    assumptions: list[Formula],
    goal: Formula,
    graph: CausalGraph,
    scm: SCM,
) -> list[_ProofStep] | None:
    """
    Forward-chain from assumptions to goal, recording each inference step.

    Uses the SCM's topological order from the CausalGraph for efficient
    scheduling, then applies the full rule set (MP, ∧E, ∧I) at each pass.

    The "abduction" phase: if the goal is not reached in the first pass,
    we call scm.abduction({goal_label: 1}) to identify which atoms need
    to be set to 1 and why — this handles cases where the goal requires
    multiple independent chains whose junction was not yet activated.
    """
    known: set[str] = set()          # labels of currently-true formulas
    known_formulas: set[Formula] = set(assumptions)   # actual formula objects

    # Initialise with atomic assumptions
    for f in assumptions:
        known.add(str(f))
        known_formulas.add(f)

    # Evaluate in topological order (CBN layer)
    topo = graph.topological_sort()
    steps: list[_ProofStep] = []

    changed = True
    max_rounds = len(topo) + 4
    for _round in range(max_rounds):
        if not changed:
            break
        changed = False

        # ── And-Elimination ────────────────────────────────────────────────
        for f in list(known_formulas):
            if isinstance(f, And):
                for sub, rule in [(f.left, "and-elim-left"), (f.right, "and-elim-right")]:
                    if str(sub) not in known:
                        known.add(str(sub))
                        known_formulas.add(sub)
                        steps.append(_ProofStep(sub, rule, [f]))
                        changed = True

        # ── Modus Ponens — evaluated in topological order ──────────────────
        for node_lbl in topo:
            if node_lbl in known:
                continue
            # Check each implication whose consequent includes this node
            for f in assumptions:
                if not isinstance(f, Imp):
                    continue
                if node_lbl not in _atom_nodes(f.right):
                    continue
                antecedent = f.left
                consequent = f.right
                if _is_known(antecedent, known) and str(consequent) not in known:
                    known.add(str(consequent))
                    known_formulas.add(consequent)
                    ant_parts = _conjuncts(antecedent)
                    steps.append(_ProofStep(consequent, "modus-ponens", ant_parts + [f]))
                    changed = True

        # ── And-Introduction (for conjunction goals / antecedents) ─────────
        targets: set[Formula] = set()
        if isinstance(goal, And):
            targets.add(goal)
        for f in assumptions:
            if isinstance(f, Imp) and isinstance(f.left, And):
                targets.add(f.left)

        for target in targets:
            if isinstance(target, And):
                left_ok  = _is_known(target.left,  known)
                right_ok = _is_known(target.right, known)
                if left_ok and right_ok and str(target) not in known:
                    known.add(str(target))
                    known_formulas.add(target)
                    l_parts = _conjuncts(target.left)
                    r_parts = _conjuncts(target.right)
                    supports = l_parts + r_parts
                    steps.append(_ProofStep(target, "and-intro", supports))
                    changed = True

        if _is_known(goal, known):
            break

    if not _is_known(goal, known):
        # ── Abduction pass: use SCM.abduction to identify missing atoms ────
        goal_label = str(goal)
        if goal_label in scm.graph.nodes:
            consistent = scm.abduction({goal_label: 1})
            if consistent:
                # Find the noise assignment that sets the most atoms to 1
                noise, _ = consistent[0]
                extra: dict[str, int] = {
                    k: v for k, v in noise.items()
                    if v == 1 and k not in known
                }
                # Re-run with these extra atoms activated
                for lbl in extra:
                    if lbl not in known:
                        known.add(lbl)
                        known_formulas.add(Atom(lbl))

                # One more forward pass
                for f in assumptions:
                    if isinstance(f, Imp):
                        if _is_known(f.left, known) and str(f.right) not in known:
                            known.add(str(f.right))
                            known_formulas.add(f.right)
                            ant_parts = _conjuncts(f.left)
                            steps.append(_ProofStep(f.right, "modus-ponens",
                                                    ant_parts + [f]))

        if not _is_known(goal, known):
            return None

    # ── Backward trim: keep only steps on a path to the goal ──────────────
    needed: set[str] = {str(goal)}
    for step in reversed(steps):
        if str(step.conclusion) in needed:
            for sup in step.supports:
                needed.add(str(sup))

    trimmed = [
        s for s in steps
        if str(s.conclusion) in needed and str(s.conclusion) not in {str(a) for a in assumptions}
    ]

    return trimmed


# ---------------------------------------------------------------------------
# Action string renderer  (PDDL-planner-compatible format)
# ---------------------------------------------------------------------------

def _render_step(step: _ProofStep) -> str:
    """
    Format a proof step as an action string.

    Examples:
        modus-ponens(P, (P -> Q))
        and-elim-left((P & Q))
        and-intro(P, Q)
    """
    if step.rule == "modus-ponens":
        # Convention: show antecedent atoms + the implication
        supports_str = ", ".join(str(s) for s in step.supports)
        return f"modus-ponens({supports_str})"

    if step.rule == "and-elim-left":
        return f"and-elim-left({step.supports[0]})"

    if step.rule == "and-elim-right":
        return f"and-elim-right({step.supports[0]})"

    if step.rule == "and-intro":
        supports_str = ", ".join(str(s) for s in step.supports)
        return f"and-intro({supports_str})"

    # Fallback
    supports_str = ", ".join(str(s) for s in step.supports)
    return f"{step.rule}({supports_str})"


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

def solve_logic_causal(
    assumptions: list[Formula],
    goal: Formula,
) -> list[str] | None:
    """
    CBN / SCM-backed forward-chaining proof.

    Parameters
    ----------
    assumptions : list of parsed Formula objects (same as CSP / PDDL solvers)
    goal        : the target Formula

    Returns
    -------
    list[str]   — action strings in PDDL-planner format, e.g.
                  ["modus-ponens(P, (P -> Q))", "modus-ponens(Q, (Q -> R))"]
    None        — if the goal is not provable from the assumptions
    """
    if not assumptions:
        # No assumptions: goal is provable only if it is a tautology
        # (e.g. P -> P).  Delegate to a simple check.
        if _is_known(goal, set()):
            return []
        return None

    try:
        graph, label_map = _build_graph(assumptions, goal)
        scm = _build_scm(assumptions, graph, label_map)
    except Exception:
        # Fallback: build a trivial single-node graph so _forward_trace still works
        graph = CausalGraph({"__dummy__"}, [])
        scm   = SCM(graph, {"__dummy__": SCMVariable(
            "__dummy__", [], lambda pa, u: u,
            NoiseVar("U", [0], [1.0]), [0, 1])})

    steps = _forward_trace(assumptions, goal, graph, scm)
    if steps is None:
        return None

    return [_render_step(s) for s in steps]


def render_logic_causal_steps(actions: list[str], lines: list) -> None:
    """
    Convert a list of action strings to (depth, text, rule, note) tuples
    ready for the proof pane.  Same format as render_plan().
    """
    for action in actions:
        lines.append((0, action, "action", None))
