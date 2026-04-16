"""
cbn/factor_bp.py — Independent CBN/SCM-guided factor propagation solver.

This solver sits on top of the CBN / SCM layer without delegating proof search
to the CSP or planning engines.  Its execution model is:

1. Build / receive a causal graph and SCM.
2. Use graph order + deterministic SCM reachability as the propagation order.
3. Saturate the current context by message-passing style forward rules
   (∀-elim, ∧-elim, MP, plus target-driven intros).
4. Handle structural goals and scoped rules recursively:
      → intro, ∀ intro, ∃ intro, ∨ intro, ¬ intro, ∃ elim, ∨ elim, RAA.

The result is a full natural-deduction proof tree encoded with the same
FOLProofStep dataclasses used by the GUI renderer.
"""
from __future__ import annotations

from dataclasses import dataclass

from parser.ast import Formula, Atom, Not, And, Imp, Or, ForAll, Exists, Var, Predicate
from logic.fol_prover import subst, collect_terms, _fresh, reset_fresh, _contradiction
from csp.fol_csp import (
    FOLProofStep,
    FOLStep,
    FOLForAllIntroStep,
    FOLImpIntroStep,
    FOLExistsElimStep,
    FOLOrElimStep,
    FOLNotIntroStep,
    FOLRAAStep,
)
from cbn.graph import CausalGraph
from cbn.scm import SCM


MAX_STRUCT_DEPTH = 20
_Keys = frozenset[tuple]


def _atom_nodes(formula: Formula) -> set[str]:
    if isinstance(formula, (Atom, Var, Predicate)):
        return {str(formula)}
    if isinstance(formula, Not):
        return _atom_nodes(formula.child)
    if isinstance(formula, (And, Or, Imp)):
        return _atom_nodes(formula.left) | _atom_nodes(formula.right)
    if isinstance(formula, (ForAll, Exists)):
        return _atom_nodes(formula.body)
    return {str(formula)}


def _collect_subformulas(formula: Formula, out: set[Formula]) -> None:
    if formula in out:
        return
    out.add(formula)
    if isinstance(formula, (And, Or, Imp)):
        _collect_subformulas(formula.left, out)
        _collect_subformulas(formula.right, out)
    elif isinstance(formula, Not):
        _collect_subformulas(formula.child, out)
    elif isinstance(formula, (ForAll, Exists)):
        _collect_subformulas(formula.body, out)


def _build_domain(assumptions: list[Formula], goal: Formula) -> set[Formula]:
    domain: set[Formula] = set()
    for assumption in assumptions:
        _collect_subformulas(assumption, domain)
    _collect_subformulas(goal, domain)
    return domain


def _formula_known(formula: Formula, known: set[Formula]) -> bool:
    if formula in known:
        return True
    if isinstance(formula, And):
        return _formula_known(formula.left, known) and _formula_known(formula.right, known)
    return False


def _extra_term_names(extra_terms: set[Var]) -> set[str]:
    return {term.name for term in extra_terms}


def _available_terms(
    known: set[Formula],
    goal: Formula | None,
    extra_terms: set[Var],
) -> list[Var]:
    names = _extra_term_names(extra_terms)
    names.update(term.name for term in collect_terms(known, goal))
    return [Var(name) for name in sorted(names)]


def _relevant_targets(known: set[Formula], goal: Formula) -> set[Formula]:
    targets: set[Formula] = set()
    if isinstance(goal, (And, Or, Exists)):
        targets.add(goal)
    for formula in known:
        if isinstance(formula, Imp) and isinstance(formula.left, (And, Or, Exists)):
            targets.add(formula.left)
    return targets


def _trim_steps(
    steps: list[FOLStep],
    assumptions: set[Formula],
    goal: Formula,
) -> list[FOLStep]:
    needed: set[Formula] = {goal}
    trimmed: list[FOLStep] = []
    for step in reversed(steps):
        if step.formula not in needed:
            continue
        trimmed.append(step)
        if step.support1 is not None and step.support1 not in assumptions:
            needed.add(step.support1)
        if step.support2 is not None and step.support2 not in assumptions:
            needed.add(step.support2)
    trimmed.reverse()
    return trimmed


def _rank_map(graph: CausalGraph | None) -> dict[str, int]:
    if graph is None:
        return {}
    return {node: idx for idx, node in enumerate(graph.topological_sort())}


def _score_formula(
    formula: Formula,
    rank: dict[str, int],
    reachable: set[str],
) -> tuple[int, int, str]:
    atoms = _atom_nodes(formula)
    first_rank = min((rank.get(atom, 10**6) for atom in atoms), default=10**6)
    all_reachable = 0 if atoms and atoms <= reachable else 1
    return (all_reachable, first_rank, str(formula))


@dataclass
class _PropagationResult:
    known: set[Formula]
    steps: list[FOLStep]


def _propagate(
    assumptions: list[Formula],
    goal: Formula,
    *,
    graph: CausalGraph | None,
    scm: SCM | None,
    domain: set[Formula],
    extra_terms: set[Var],
) -> _PropagationResult:
    known = set(assumptions)
    steps: list[FOLStep] = []
    rank = _rank_map(graph)
    reachable: set[str] = set()
    if scm is not None:
        try:
            reachable = {node for node, value in scm.sample().items() if value == 1}
        except Exception:
            reachable = set()

    changed = True
    while changed:
        changed = False
        terms = _available_terms(known, goal, extra_terms)
        targets = _relevant_targets(known, goal)

        # ∧-elim is deterministic and always useful.
        for formula in sorted(known, key=str):
            if not isinstance(formula, And):
                continue
            for part, rule in ((formula.left, "and_elim_l"), (formula.right, "and_elim_r")):
                if part in known:
                    continue
                known.add(part)
                steps.append(FOLStep(formula=part, rule=rule, support1=formula))
                changed = True

        # Deterministic decompositions of negated compounds.
        for formula in sorted(known, key=str):
            if not isinstance(formula, Not):
                continue

            child = formula.child

            if isinstance(child, Not):
                derived = child.child
                if derived not in known:
                    known.add(derived)
                    steps.append(FOLStep(
                        formula=derived,
                        rule="double_neg_elim",
                        support1=formula,
                    ))
                    changed = True

            elif isinstance(child, Or):
                for derived, rule in (
                    (Not(child.left), "neg_or_elim_l"),
                    (Not(child.right), "neg_or_elim_r"),
                ):
                    if derived in known:
                        continue
                    known.add(derived)
                    steps.append(FOLStep(
                        formula=derived,
                        rule=rule,
                        support1=formula,
                    ))
                    changed = True

            elif isinstance(child, Imp):
                for derived, rule in (
                    (child.left, "neg_imp_elim_l"),
                    (Not(child.right), "neg_imp_elim_r"),
                ):
                    if derived in known:
                        continue
                    known.add(derived)
                    steps.append(FOLStep(
                        formula=derived,
                        rule=rule,
                        support1=formula,
                    ))
                    changed = True

            elif isinstance(child, Exists):
                derived = ForAll(child.var, Not(child.body))
                if derived not in known:
                    known.add(derived)
                    steps.append(FOLStep(
                        formula=derived,
                        rule="neg_exists_elim",
                        support1=formula,
                    ))
                    changed = True

            elif isinstance(child, ForAll):
                derived = Exists(child.var, Not(child.body))
                if derived not in known:
                    known.add(derived)
                    steps.append(FOLStep(
                        formula=derived,
                        rule="neg_forall_elim",
                        support1=formula,
                    ))
                    changed = True

        # ∀-elim in causal/topological order over instantiated bodies.
        universals = sorted(
            (formula for formula in known if isinstance(formula, ForAll)),
            key=lambda f: _score_formula(f.body, rank, reachable),
        )
        for formula in universals:
            for term in terms:
                instance = subst(formula.body, formula.var, term)
                if instance in known:
                    continue
                known.add(instance)
                steps.append(FOLStep(
                    formula=instance,
                    rule="forall_elim",
                    support1=formula,
                    note=f"{formula.var}↦{term}",
                ))
                changed = True

        # Target-driven intros that feed forward propagation.
        for target in sorted(targets, key=lambda f: _score_formula(f, rank, reachable)):
            if target in known:
                continue
            if isinstance(target, And):
                if _formula_known(target.left, known) and _formula_known(target.right, known):
                    known.add(target)
                    steps.append(FOLStep(
                        formula=target,
                        rule="and_intro",
                        support1=target.left,
                        support2=target.right,
                    ))
                    changed = True
            elif isinstance(target, Exists):
                for term in terms:
                    witness = subst(target.body, target.var, term)
                    if witness not in known:
                        continue
                    known.add(target)
                    steps.append(FOLStep(
                        formula=target,
                        rule="exists_intro",
                        support1=witness,
                        note=f"{target.var}↦{term}",
                    ))
                    changed = True
                    break
            elif isinstance(target, Or):
                if _formula_known(target.left, known):
                    known.add(target)
                    steps.append(FOLStep(
                        formula=target,
                        rule="or_intro_l",
                        support1=target.left,
                    ))
                    changed = True
                elif _formula_known(target.right, known):
                    known.add(target)
                    steps.append(FOLStep(
                        formula=target,
                        rule="or_intro_r",
                        support1=target.right,
                    ))
                    changed = True

        # MP ordered by the causal graph / SCM reachability.
        implications = sorted(
            (formula for formula in known if isinstance(formula, Imp)),
            key=lambda f: _score_formula(f.right, rank, reachable),
        )
        for formula in implications:
            if not _formula_known(formula.left, known) or formula.right in known:
                continue
            known.add(formula.right)
            steps.append(FOLStep(
                formula=formula.right,
                rule="mp",
                support1=formula.left,
                support2=formula,
            ))
            changed = True

    return _PropagationResult(known=known, steps=steps)


def _prove_contradiction(
    assumptions: list[Formula],
    *,
    graph: CausalGraph | None,
    scm: SCM | None,
    domain: set[Formula],
    extra_terms: set[Var],
    struct_depth: int,
    keys: _Keys,
) -> list[FOLProofStep] | None:
    if struct_depth > MAX_STRUCT_DEPTH:
        return None

    prop = _propagate(
        assumptions,
        Atom("⊥"),
        graph=graph,
        scm=scm,
        domain=domain,
        extra_terms=extra_terms,
    )
    contra = _contradiction(prop.known)
    if contra is not None:
        pos, neg = contra
        trimmed = _trim_steps(prop.steps, set(assumptions), pos)
        return trimmed + [FOLStep(
            formula=Atom("⊥"),
            rule="contradiction",
            support1=pos,
            support2=neg,
        )]

    available = prop.known

    # ∃-elim
    for formula in sorted(available, key=str):
        if not isinstance(formula, Exists):
            continue
        key = ("∃E⊥", str(formula))
        if key in keys:
            continue
        const = _fresh()
        instance = subst(formula.body, formula.var, const)
        result = _prove_contradiction(
            assumptions + [instance],
            graph=graph,
            scm=scm,
            domain=domain,
            extra_terms=extra_terms | {const},
            struct_depth=struct_depth + 1,
            keys=keys | {key},
        )
        if result is not None:
            return [FOLExistsElimStep(
                formula=Atom("⊥"),
                elim_formula=formula,
                const_name=const.name,
                sub_steps=tuple(result),
            )]

    # ∨-elim
    for formula in sorted(available, key=str):
        if not isinstance(formula, Or):
            continue
        key = ("∨E⊥", str(formula))
        if key in keys:
            continue
        next_keys = keys | {key}
        left = _prove_contradiction(
            assumptions + [formula.left],
            graph=graph,
            scm=scm,
            domain=domain,
            extra_terms=extra_terms,
            struct_depth=struct_depth + 1,
            keys=next_keys,
        )
        if left is None:
            continue
        right = _prove_contradiction(
            assumptions + [formula.right],
            graph=graph,
            scm=scm,
            domain=domain,
            extra_terms=extra_terms,
            struct_depth=struct_depth + 1,
            keys=next_keys,
        )
        if right is not None:
            return [FOLOrElimStep(
                formula=Atom("⊥"),
                or_formula=formula,
                left_steps=tuple(left),
                right_steps=tuple(right),
            )]

    # To close a contradiction from ¬A, try to prove A directly.
    for formula in sorted(available, key=str):
        if not isinstance(formula, Not):
            continue
        key = ("prove+", str(formula.child))
        if key in keys:
            continue
        proof = _prove_goal(
            [f for f in assumptions if f != formula],
            formula.child,
            graph=graph,
            scm=scm,
            domain=domain,
            extra_terms=extra_terms,
            struct_depth=struct_depth + 1,
            keys=keys | {key},
            allow_raa=False,
        )
        if proof is not None:
            return proof + [FOLStep(
                formula=Atom("⊥"),
                rule="contradiction",
                support1=formula.child,
                support2=formula,
            )]

    return None


def _prove_goal(
    assumptions: list[Formula],
    goal: Formula,
    *,
    graph: CausalGraph | None,
    scm: SCM | None,
    domain: set[Formula],
    extra_terms: set[Var],
    struct_depth: int,
    keys: _Keys,
    allow_raa: bool,
) -> list[FOLProofStep] | None:
    if struct_depth > MAX_STRUCT_DEPTH:
        return None

    prop = _propagate(
        assumptions,
        goal,
        graph=graph,
        scm=scm,
        domain=domain,
        extra_terms=extra_terms,
    )
    available = prop.known

    if goal in available:
        return _trim_steps(prop.steps, set(assumptions), goal)

    if _contradiction(available) is not None:
        return _trim_steps(prop.steps, set(assumptions), goal) + [
            FOLStep(formula=goal, rule="ex_falso")
        ]

    # Goal-directed structural rules.
    if isinstance(goal, ForAll):
        const = _fresh()
        subgoal = subst(goal.body, goal.var, const)
        child = _prove_goal(
            list(available),
            subgoal,
            graph=graph,
            scm=scm,
            domain=domain,
            extra_terms=extra_terms | {const},
            struct_depth=struct_depth + 1,
            keys=keys,
            allow_raa=allow_raa,
        )
        if child is not None:
            return [FOLForAllIntroStep(
                formula=goal,
                var=goal.var,
                const_name=const.name,
                sub_steps=tuple(child),
            )]

    if isinstance(goal, Imp):
        child = _prove_goal(
            list(available) + [goal.left],
            goal.right,
            graph=graph,
            scm=scm,
            domain=domain,
            extra_terms=extra_terms,
            struct_depth=struct_depth + 1,
            keys=keys,
            allow_raa=allow_raa,
        )
        if child is not None:
            return [FOLImpIntroStep(
                formula=goal,
                antecedent=goal.left,
                sub_steps=tuple(child),
            )]

    if isinstance(goal, Not):
        contra = _prove_contradiction(
            list(available) + [goal.child],
            graph=graph,
            scm=scm,
            domain=domain,
            extra_terms=extra_terms,
            struct_depth=struct_depth + 1,
            keys=keys,
        )
        if contra is not None:
            return [FOLNotIntroStep(
                formula=goal,
                assumed=goal.child,
                contra_steps=tuple(contra),
            )]

    if isinstance(goal, Exists):
        for term in _available_terms(available, goal, extra_terms):
            key = ("∃I", str(goal), str(term))
            if key in keys:
                continue
            subgoal = subst(goal.body, goal.var, term)
            if subgoal in available:
                return [FOLStep(
                    formula=goal,
                    rule="exists_intro",
                    support1=subgoal,
                    note=f"{goal.var}↦{term}",
                )]
            child = _prove_goal(
                list(available),
                subgoal,
                graph=graph,
                scm=scm,
                domain=domain,
                extra_terms=extra_terms | {term},
                struct_depth=struct_depth + 1,
                keys=keys | {key},
                allow_raa=allow_raa,
            )
            if child is not None:
                return child + [FOLStep(
                    formula=goal,
                    rule="exists_intro",
                    support1=subgoal,
                    note=f"{goal.var}↦{term}",
                )]

    if isinstance(goal, Or):
        left = _prove_goal(
            list(available),
            goal.left,
            graph=graph,
            scm=scm,
            domain=domain,
            extra_terms=extra_terms,
            struct_depth=struct_depth + 1,
            keys=keys | {("∨IL", str(goal))},
            allow_raa=allow_raa,
        )
        if left is not None:
            return left + [FOLStep(formula=goal, rule="or_intro_l", support1=goal.left)]

        right = _prove_goal(
            list(available),
            goal.right,
            graph=graph,
            scm=scm,
            domain=domain,
            extra_terms=extra_terms,
            struct_depth=struct_depth + 1,
            keys=keys | {("∨IR", str(goal))},
            allow_raa=allow_raa,
        )
        if right is not None:
            return right + [FOLStep(formula=goal, rule="or_intro_r", support1=goal.right)]

    if isinstance(goal, And):
        left = _prove_goal(
            list(available),
            goal.left,
            graph=graph,
            scm=scm,
            domain=domain,
            extra_terms=extra_terms,
            struct_depth=struct_depth + 1,
            keys=keys | {("∧I", str(goal), "L")},
            allow_raa=allow_raa,
        )
        if left is not None:
            right = _prove_goal(
                list(available),
                goal.right,
                graph=graph,
                scm=scm,
                domain=domain,
                extra_terms=extra_terms,
                struct_depth=struct_depth + 1,
                keys=keys | {("∧I", str(goal), "R")},
                allow_raa=allow_raa,
            )
            if right is not None:
                return left + right + [FOLStep(
                    formula=goal,
                    rule="and_intro",
                    support1=goal.left,
                    support2=goal.right,
                )]

    # Context structural rules.
    for formula in sorted(available, key=str):
        if isinstance(formula, Exists):
            key = ("∃E", str(formula), str(goal))
            if key in keys:
                continue
            const = _fresh()
            instance = subst(formula.body, formula.var, const)
            child = _prove_goal(
                list(available) + [instance],
                goal,
                graph=graph,
                scm=scm,
                domain=domain,
                extra_terms=extra_terms | {const},
                struct_depth=struct_depth + 1,
                keys=keys | {key},
                allow_raa=allow_raa,
            )
            if child is not None:
                return [FOLExistsElimStep(
                    formula=goal,
                    elim_formula=formula,
                    const_name=const.name,
                    sub_steps=tuple(child),
                )]

        if isinstance(formula, Or):
            key = ("∨E", str(formula), str(goal))
            if key in keys:
                continue
            left = _prove_goal(
                list(available) + [formula.left],
                goal,
                graph=graph,
                scm=scm,
                domain=domain,
                extra_terms=extra_terms,
                struct_depth=struct_depth + 1,
                keys=keys | {key, ("∨EL", str(formula), str(goal))},
                allow_raa=allow_raa,
            )
            if left is None:
                continue
            right = _prove_goal(
                list(available) + [formula.right],
                goal,
                graph=graph,
                scm=scm,
                domain=domain,
                extra_terms=extra_terms,
                struct_depth=struct_depth + 1,
                keys=keys | {key, ("∨ER", str(formula), str(goal))},
                allow_raa=allow_raa,
            )
            if right is not None:
                return [FOLOrElimStep(
                    formula=goal,
                    or_formula=formula,
                    left_steps=tuple(left),
                    right_steps=tuple(right),
                )]

    if allow_raa and not isinstance(goal, Not):
        neg_goal = Not(goal)
        if neg_goal not in available:
            key = ("RAA", str(goal))
            if key not in keys:
                contra = _prove_contradiction(
                    list(available) + [neg_goal],
                    graph=graph,
                    scm=scm,
                    domain=domain,
                    extra_terms=extra_terms,
                    struct_depth=struct_depth + 1,
                    keys=keys | {key},
                )
                if contra is not None:
                    return [FOLRAAStep(
                        formula=goal,
                        neg_assumed=neg_goal,
                        contra_steps=tuple(contra),
                    )]

    return None


def solve_factor_bp(
    assumptions: list[Formula],
    goal: Formula,
    *,
    graph: CausalGraph | None = None,
    scm: SCM | None = None,
) -> list[FOLProofStep] | None:
    """
    Solve a natural-deduction problem using CBN/SCM-guided factor propagation.

    Two-pass strategy:
    1. direct proofs only
    2. classical fallback with RAA
    """
    domain = _build_domain(assumptions, goal)

    # If there are no free terms at all, keep the domain empty and let the
    # structural quantifier rules introduce fresh constants explicitly.
    reset_fresh()
    direct = _prove_goal(
        list(assumptions),
        goal,
        graph=graph,
        scm=scm,
        domain=domain,
        extra_terms=set(),
        struct_depth=0,
        keys=frozenset(),
        allow_raa=False,
    )
    if direct is not None:
        return direct

    reset_fresh()
    return _prove_goal(
        list(assumptions),
        goal,
        graph=graph,
        scm=scm,
        domain=domain,
        extra_terms=set(),
        struct_depth=0,
        keys=frozenset(),
        allow_raa=True,
    )
