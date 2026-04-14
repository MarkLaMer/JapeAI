"""
csp/fol_csp.py — FOL-capable CSP solver.

Architecture (mirrors the propositional CSP but extended for first-order logic):

  Forward rules  (each costs one step from the budget):
      forall_elim   : ∀x.P(x) + term t  →  P(t)
      exists_intro  : P(t)               →  ∃x.P(x)   (when ∃x.P(x) in domain)
      or_intro_l/r  : A  or  B           →  A∨B        (when A∨B in domain)
      mp            : A,  A→B            →  B
      and_intro     : A,  B              →  A∧B
      and_elim_l/r  : A∧B               →  A  or  B

  Structural rules (free — handled via scoped sub-problems):
      forall_intro  : ∀x.B   proved by introducing fresh _c and proving B[x:=_c]
      imp_intro     : A→B    proved by assuming A and proving B
      not_intro     : ¬A     proved by assuming A and deriving ⊥
      exists_elim   : ∃x.B   consumed by introducing fresh _c and adding B[x:=_c]
      or_elim       : A∨B    consumed by proving goal from A AND from B
      raa           : goal   proved by assuming ¬goal and deriving ⊥

The iterative-deepening outer loop tries step budgets 0, 1, 2, … up to MAX_BOUND,
returning the shortest-step proof found.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Optional, FrozenSet, Union

from parser.ast import (
    Formula, Atom, Not, And, Imp, Or, Var, Predicate, ForAll, Exists,
)
from logic.fol_prover import (
    subst, free_vars, collect_terms,
    _fresh, reset_fresh,
    _expand_conj_mp, _contradiction,
)

# ---------------------------------------------------------------------------
# Step types
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class FOLStep:
    """One forward proof step (no sub-proof)."""
    formula: Formula
    rule: str          # forall_elim | exists_intro | or_intro_l | or_intro_r |
                       # mp | and_intro | and_elim_l | and_elim_r | ex_falso
    support1: Optional[Formula] = None
    support2: Optional[Formula] = None
    note:     Optional[str]     = None


@dataclass(frozen=True)
class FOLForAllIntroStep:
    """∀x.B  proved by fresh constant _c, sub-proof of B[x:=_c]."""
    formula:    Formula         # ForAll(var, body)
    var:        str
    const_name: str             # e.g. "_c0"
    sub_steps:  tuple           # tuple[FOLProofStep, ...]
    rule: str = "forall_intro"


@dataclass(frozen=True)
class FOLImpIntroStep:
    """A→B  proved by assuming A and proving B."""
    formula:    Formula         # Imp(antecedent, consequent)
    antecedent: Formula
    sub_steps:  tuple
    rule: str = "imp_intro"


@dataclass(frozen=True)
class FOLExistsElimStep:
    """∃x.B  eliminated: introduce fresh _c, add B[x:=_c], prove goal."""
    formula:      Formula       # the goal that was eventually proved
    elim_formula: Formula       # the Exists(...) that was eliminated
    const_name:   str
    sub_steps:    tuple
    rule: str = "exists_elim"


@dataclass(frozen=True)
class FOLOrElimStep:
    """A∨B  case-split: prove goal from A, and prove goal from B."""
    formula:     Formula        # goal
    or_formula:  Formula        # Or(left, right)
    left_steps:  tuple          # proof of goal assuming left
    right_steps: tuple          # proof of goal assuming right
    rule: str = "or_elim"


@dataclass(frozen=True)
class FOLNotIntroStep:
    """¬A  proved by assuming A and deriving ⊥."""
    formula:      Formula       # Not(assumed)
    assumed:      Formula       # A
    contra_steps: tuple         # proof of ⊥
    rule: str = "not_intro"


@dataclass(frozen=True)
class FOLRAAStep:
    """Classical RAA: assume ¬goal, derive ⊥, conclude goal."""
    formula:      Formula       # goal
    neg_assumed:  Formula       # Not(goal)
    contra_steps: tuple
    rule: str = "raa"


# Union type for all FOL proof steps
FOLProofStep = Union[
    FOLStep, FOLForAllIntroStep, FOLImpIntroStep,
    FOLExistsElimStep, FOLOrElimStep, FOLNotIntroStep, FOLRAAStep,
]

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------
MAX_BOUND       = 25   # iterative-deepening upper bound on forward steps
MAX_STRUCT_DEPTH = 20  # maximum nesting of structural decompositions

# ---------------------------------------------------------------------------
# Context helpers
# ---------------------------------------------------------------------------

def _available_set(steps: list[FOLProofStep],
                   base: list[Formula]) -> set[Formula]:
    """Collect all formulas currently known (base + derived by forward steps)."""
    known: set[Formula] = set(base)
    for s in steps:
        known.add(s.formula)
    return known


def _forward_close(ctx: set[Formula]) -> set[Formula]:
    """∧-elim + eager MP until fixed point (used only in contra-finding)."""
    return _expand_conj_mp(ctx)


def _has_contradiction(ctx: set[Formula]) -> bool:
    return _contradiction(ctx) is not None


def _collect_subformulas(f: Formula, out: set[Formula]) -> None:
    """Recursively collect all subformulas of *f* into *out*."""
    if f in out:
        return
    out.add(f)
    if isinstance(f, (And, Or, Imp)):
        _collect_subformulas(f.left,  out)
        _collect_subformulas(f.right, out)
    elif isinstance(f, Not):
        _collect_subformulas(f.child, out)
    elif isinstance(f, (ForAll, Exists)):
        _collect_subformulas(f.body, out)


def _build_domain(assumptions: list[Formula], goal: Formula) -> set[Formula]:
    """Formula domain = all subformulas of assumptions + goal."""
    domain: set[Formula] = set()
    for a in assumptions:
        _collect_subformulas(a, domain)
    _collect_subformulas(goal, domain)
    return domain


# ---------------------------------------------------------------------------
# Forward step generation
# ---------------------------------------------------------------------------

def _generate_forward_steps(
    available: set[Formula],
    domain:    set[Formula],
) -> list[FOLStep]:
    """
    Generate all valid one-step forward derivations from *available*,
    restricted to formulas that appear in *domain*.
    """
    steps: list[FOLStep] = []
    terms = collect_terms(available)

    for f in list(available):

        # ∀-elim
        if isinstance(f, ForAll):
            for term in terms:
                instance = subst(f.body, f.var, term)
                if instance not in available:
                    steps.append(FOLStep(
                        formula=instance, rule="forall_elim",
                        support1=f, note=f"{f.var}↦{term}",
                    ))

        # ∧-elim L / R  (already in _forward_close, but generate for proof trace)
        if isinstance(f, And):
            if f.left not in available:
                steps.append(FOLStep(formula=f.left,  rule="and_elim_l", support1=f))
            if f.right not in available:
                steps.append(FOLStep(formula=f.right, rule="and_elim_r", support1=f))

    # ∃-intro  (from P(t) → ∃x.P(x), only when the ∃ is in domain)
    for target in domain:
        if isinstance(target, Exists) and target not in available:
            for term in terms:
                witness = subst(target.body, target.var, term)
                if witness in available:
                    steps.append(FOLStep(
                        formula=target, rule="exists_intro",
                        support1=witness, note=f"{target.var}↦{term}",
                    ))
                    break   # one witness is enough

    # ∨-intro L/R  (from A → A∨B, only when A∨B in domain)
    for target in domain:
        if isinstance(target, Or) and target not in available:
            if target.left in available:
                steps.append(FOLStep(
                    formula=target, rule="or_intro_l", support1=target.left,
                ))
            elif target.right in available:
                steps.append(FOLStep(
                    formula=target, rule="or_intro_r", support1=target.right,
                ))

    # MP  (A, A→B → B)
    for f in list(available):
        if isinstance(f, Imp):
            if f.left in available and f.right not in available:
                steps.append(FOLStep(
                    formula=f.right, rule="mp",
                    support1=f.left, support2=f,
                ))

    # ∧-intro  (A, B → A∧B, only when target in domain)
    available_list = list(available)
    for target in domain:
        if isinstance(target, And) and target not in available:
            if target.left in available and target.right in available:
                steps.append(FOLStep(
                    formula=target, rule="and_intro",
                    support1=target.left, support2=target.right,
                ))

    # Deduplicate
    seen: set[Formula] = set()
    unique: list[FOLStep] = []
    for s in steps:
        if s.formula not in seen:
            seen.add(s.formula)
            unique.append(s)
    return unique


# ---------------------------------------------------------------------------
# Core solver
# ---------------------------------------------------------------------------

_Keys = FrozenSet[tuple]


def _fol_solve(
    base:        list[Formula],
    goal:        Formula,
    max_steps:   int,
    struct_depth: int,
    keys:        _Keys,
    domain:      set[Formula],
    allow_raa:   bool = True,
) -> Optional[list[FOLProofStep]]:
    """
    Try to prove *goal* from *base* using at most *max_steps* forward steps.

    All forward derivations (∀-elim, MP, ∧-elim, …) are explicit budget-counted
    steps — nothing is silently absorbed.  This keeps the rendered proof faithful
    to what Jape shows (e.g. an explicit ∀-elim line, then →-elim, then ∧-elim).

    allow_raa=False skips the classical RAA fallback so that direct proofs are
    always preferred over RAA proofs of the same depth.
    """
    if struct_depth > MAX_STRUCT_DEPTH:
        return None

    # Work directly from base — no silent forward-closing.
    available = set(base)

    # ── Fast checks ─────────────────────────────────────────────────────────

    # Success: goal already in context
    if goal in available:
        return []

    # Direct contradiction → ex falso (checks only syntactic A / ¬A pairs)
    if _has_contradiction(available):
        return [FOLStep(formula=goal, rule="ex_falso")]

    # ── Structural decomposition of the GOAL ────────────────────────────────

    # ∀-intro: introduce fresh constant, prove body[var:=c]
    if isinstance(goal, ForAll):
        c = _fresh()
        subgoal = subst(goal.body, goal.var, c)
        sub = _fol_solve(list(available), subgoal,
                         max_steps, struct_depth + 1, keys, domain, allow_raa)
        if sub is not None:
            return [FOLForAllIntroStep(
                formula=goal, var=goal.var, const_name=c.name, sub_steps=tuple(sub),
            )]

    # →-intro: assume antecedent, prove consequent
    if isinstance(goal, Imp):
        augmented = list(available) + [goal.left]
        sub = _fol_solve(augmented, goal.right,
                         max_steps, struct_depth + 1, keys, domain, allow_raa)
        if sub is not None:
            return [FOLImpIntroStep(
                formula=goal, antecedent=goal.left, sub_steps=tuple(sub),
            )]

    # ¬-intro: assume child, derive ⊥
    if isinstance(goal, Not):
        augmented = list(available) + [goal.child]
        contra = _fol_solve_contra(augmented, max_steps, struct_depth + 1, keys, domain)
        if contra is not None:
            return [FOLNotIntroStep(
                formula=goal, assumed=goal.child, contra_steps=tuple(contra),
            )]

    # ∃-intro: try each available term as a witness
    if isinstance(goal, Exists):
        terms = collect_terms(available)
        for term in terms:
            key = ("∃I", str(goal), str(term))
            if key in keys:
                continue
            subgoal = subst(goal.body, goal.var, term)
            if subgoal in available:
                return [FOLStep(
                    formula=goal, rule="exists_intro",
                    support1=subgoal, note=f"{goal.var}↦{term}",
                )]
            sub = _fol_solve(list(available), subgoal,
                             max_steps, struct_depth + 1, keys | {key}, domain, allow_raa)
            if sub is not None:
                return sub + [FOLStep(
                    formula=goal, rule="exists_intro",
                    support1=subgoal, note=f"{goal.var}↦{term}",
                )]

    # ∨-intro: prove either disjunct
    if isinstance(goal, Or):
        key_l = ("∨IL", str(goal))
        if key_l not in keys:
            sub = _fol_solve(list(available), goal.left,
                             max_steps, struct_depth + 1, keys | {key_l}, domain, allow_raa)
            if sub is not None:
                return sub + [FOLStep(
                    formula=goal, rule="or_intro_l", support1=goal.left,
                )]
        key_r = ("∨IR", str(goal))
        if key_r not in keys:
            sub = _fol_solve(list(available), goal.right,
                             max_steps, struct_depth + 1, keys | {key_r}, domain, allow_raa)
            if sub is not None:
                return sub + [FOLStep(
                    formula=goal, rule="or_intro_r", support1=goal.right,
                )]

    # ∧-intro: prove both conjuncts
    if isinstance(goal, And):
        key_a = ("∧I", str(goal))
        if key_a not in keys:
            l_sub = _fol_solve(list(available), goal.left,
                               max_steps, struct_depth + 1, keys | {key_a}, domain, allow_raa)
            if l_sub is not None:
                r_sub = _fol_solve(list(available), goal.right,
                                   max_steps, struct_depth + 1, keys | {key_a}, domain, allow_raa)
                if r_sub is not None:
                    return l_sub + r_sub + [FOLStep(
                        formula=goal, rule="and_intro",
                        support1=goal.left, support2=goal.right,
                    )]

    # ── Structural rules on the CONTEXT ─────────────────────────────────────

    # ∃-elim: introduce fresh constant for each ∃x.B in context
    for f in list(available):
        if not isinstance(f, Exists):
            continue
        key = ("∃E", str(f))
        if key in keys:
            continue
        c = _fresh()
        instance = subst(f.body, f.var, c)
        augmented = list(available) + [instance]
        sub = _fol_solve(augmented, goal,
                         max_steps, struct_depth + 1, keys | {key}, domain, allow_raa)
        if sub is not None:
            return [FOLExistsElimStep(
                formula=goal, elim_formula=f, const_name=c.name, sub_steps=tuple(sub),
            )]

    # ∨-elim: case split on each A∨B in context
    for f in list(available):
        if not isinstance(f, Or):
            continue
        key = ("∨E", str(f))
        if key in keys:
            continue
        new_keys = keys | {key}
        l_sub = _fol_solve(list(available) + [f.left],  goal,
                           max_steps, struct_depth + 1, new_keys, domain, allow_raa)
        if l_sub is not None:
            r_sub = _fol_solve(list(available) + [f.right], goal,
                               max_steps, struct_depth + 1, new_keys, domain, allow_raa)
            if r_sub is not None:
                return [FOLOrElimStep(
                    formula=goal, or_formula=f,
                    left_steps=tuple(l_sub), right_steps=tuple(r_sub),
                )]

    # ── Forward search ───────────────────────────────────────────────────────
    if max_steps > 0:
        candidates = _generate_forward_steps(available, domain)
        # Prioritise steps whose formula IS the goal or is a subformula of it
        goal_subs: set[Formula] = set()
        _collect_subformulas(goal, goal_subs)
        candidates.sort(key=lambda s: (
            s.formula != goal,
            s.formula not in goal_subs,
            str(s.formula),
        ))

        for step in candidates:
            if step.formula in available:
                continue
            new_base = list(available) + [step.formula]
            rest = _fol_solve(new_base, goal,
                              max_steps - 1, struct_depth, keys, domain, allow_raa)
            if rest is not None:
                return [step] + rest

    # ── RAA (classical fallback) ─────────────────────────────────────────────
    if allow_raa and not isinstance(goal, Not):
        neg = Not(goal)
        if neg not in available:
            key = ("RAA", str(goal))
            if key not in keys:
                augmented = list(available) + [neg]
                contra = _fol_solve_contra(
                    augmented, max_steps, struct_depth + 1, keys | {key}, domain,
                )
                if contra is not None:
                    return [FOLRAAStep(
                        formula=goal, neg_assumed=neg, contra_steps=tuple(contra),
                    )]

    return None


def _fol_solve_contra(
    base:        list[Formula],
    max_steps:   int,
    struct_depth: int,
    keys:        _Keys,
    domain:      set[Formula],
) -> Optional[list[FOLProofStep]]:
    """
    Try to derive a contradiction (⊥) from *base*.
    Uses aggressive forward expansion + tries to prove the positive
    form of each negation in context.
    """
    if struct_depth > MAX_STRUCT_DEPTH:
        return None

    # Aggressive expansion: ∧-elim + MP + ∃-witness implications
    from logic.fol_prover import _expand_with_witnesses
    available = _expand_with_witnesses(set(base))

    # Direct contradiction
    contra = _contradiction(available)
    if contra:
        pos, neg = contra
        return [FOLStep(formula=Atom("⊥"), rule="contradiction",
                        support1=pos, support2=neg)]

    terms = collect_terms(available)

    # ∀-elim into context
    for f in list(available):
        if not isinstance(f, ForAll):
            continue
        for term in terms:
            key = ("∀E⊥", str(f), str(term))
            if key in keys:
                continue
            instance = subst(f.body, f.var, term)
            if instance in available:
                continue
            result = _fol_solve_contra(
                list(available) + [instance],
                max_steps, struct_depth + 1, keys | {key}, domain,
            )
            if result is not None:
                return result

    # ∃-elim into context
    for f in list(available):
        if not isinstance(f, Exists):
            continue
        key = ("∃E⊥", str(f))
        if key in keys:
            continue
        c = _fresh()
        instance = subst(f.body, f.var, c)
        result = _fol_solve_contra(
            list(available) + [instance],
            max_steps, struct_depth + 1, keys | {key}, domain,
        )
        if result is not None:
            return result

    # ∨-elim into context
    for f in list(available):
        if not isinstance(f, Or):
            continue
        key = ("∨E⊥", str(f))
        if key in keys:
            continue
        new_keys = keys | {key}
        l = _fol_solve_contra(list(available) + [f.left],
                               max_steps, struct_depth + 1, new_keys, domain)
        if l is not None:
            r = _fol_solve_contra(list(available) + [f.right],
                                   max_steps, struct_depth + 1, new_keys, domain)
            if r is not None:
                return l + r   # both branches reach ⊥

    # Prove the positive form of each negation present
    for f in list(available):
        if not isinstance(f, Not):
            continue
        key = ("prove+", str(f.child))
        if key in keys:
            continue
        proof = _fol_solve(
            list(available - {f}), f.child,
            max_steps, struct_depth + 1, keys | {key}, domain,
        )
        if proof is not None:
            return proof + [FOLStep(formula=Atom("⊥"), rule="contradiction",
                                    support1=f.child, support2=f)]

    return None


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

def solve_fol_csp(
    assumptions: list[Formula],
    goal:        Formula,
    *,
    max_bound: int = MAX_BOUND,
) -> Optional[list[FOLProofStep]]:
    """
    Iterative-deepening FOL CSP solver.

    Two-pass strategy: first try direct proofs (allow_raa=False) at every
    depth — this guarantees a direct proof is always preferred over a longer
    RAA proof.  Only if no direct proof exists at any depth do we retry with
    RAA enabled (for classically required proofs like P9).
    """
    domain = _build_domain(assumptions, goal)

    # Pass 1: direct proofs only
    reset_fresh()
    for max_steps in range(max_bound + 1):
        result = _fol_solve(
            list(assumptions), goal,
            max_steps, 0, frozenset(), domain, allow_raa=False,
        )
        if result is not None:
            return result

    # Pass 2: allow classical RAA
    reset_fresh()
    for max_steps in range(max_bound + 1):
        result = _fol_solve(
            list(assumptions), goal,
            max_steps, 0, frozenset(), domain, allow_raa=True,
        )
        if result is not None:
            return result

    return None


# ---------------------------------------------------------------------------
# Rendering helper (for GUI)
# ---------------------------------------------------------------------------

def render_fol_csp_steps(
    steps: list[FOLProofStep],
    lines: list,
    depth: int = 0,
) -> None:
    """
    Flatten FOL CSP proof steps into display tuples
    (depth, formula_str, rule_label, note_str | None).
    """
    RULE_LABELS = {
        "forall_elim":  "∀ elim",
        "exists_intro": "∃ intro",
        "or_intro_l":   "∨ intro L",
        "or_intro_r":   "∨ intro R",
        "mp":           "→ elim",
        "and_intro":    "∧ intro",
        "and_elim_l":   "∧ elim L",
        "and_elim_r":   "∧ elim R",
        "ex_falso":     "ex falso",
        "contradiction":"⊥",
        "forall_intro": "∀ intro",
        "imp_intro":    "→ intro",
        "exists_elim":  "∃ elim",
        "or_elim":      "∨ elim",
        "not_intro":    "¬ intro",
        "raa":          "RAA",
    }

    for step in steps:

        if isinstance(step, FOLForAllIntroStep):
            lines.append((depth, f"[ ∀-introduce  {step.var} ↦ {step.const_name} ]",
                          "scope", None))
            render_fol_csp_steps(list(step.sub_steps), lines, depth + 1)
            lines.append((depth, str(step.formula), "∀ intro",
                          f"{step.var}↦{step.const_name}"))

        elif isinstance(step, FOLImpIntroStep):
            lines.append((depth, f"[ assume  {step.antecedent} ]", "hyp", None))
            render_fol_csp_steps(list(step.sub_steps), lines, depth + 1)
            lines.append((depth, str(step.formula), "→ intro", None))

        elif isinstance(step, FOLExistsElimStep):
            lines.append((depth,
                          f"[ ∃-eliminate  {step.elim_formula}  ↦  {step.const_name} ]",
                          "scope", None))
            render_fol_csp_steps(list(step.sub_steps), lines, depth + 1)
            lines.append((depth, str(step.formula), "∃ elim",
                          f"{step.const_name}"))

        elif isinstance(step, FOLOrElimStep):
            lines.append((depth, f"[ ∨-cases  {step.or_formula} ]", "scope", None))
            lines.append((depth + 1, f"[ case  {step.or_formula.left} ]", "hyp", None))
            render_fol_csp_steps(list(step.left_steps), lines, depth + 2)
            lines.append((depth + 1, f"[ case  {step.or_formula.right} ]", "hyp", None))
            render_fol_csp_steps(list(step.right_steps), lines, depth + 2)
            lines.append((depth, str(step.formula), "∨ elim", None))

        elif isinstance(step, FOLNotIntroStep):
            lines.append((depth, f"[ assume  {step.assumed} ]", "hyp", None))
            render_fol_csp_steps(list(step.contra_steps), lines, depth + 1)
            lines.append((depth, str(step.formula), "¬ intro", None))

        elif isinstance(step, FOLRAAStep):
            lines.append((depth, f"[ assume  {step.neg_assumed} ]", "hyp", None))
            render_fol_csp_steps(list(step.contra_steps), lines, depth + 1)
            lines.append((depth, str(step.formula), "RAA", None))

        else:
            # FOLStep (flat forward step)
            parts = []
            if step.support1:
                parts.append(str(step.support1))
            if step.support2:
                parts.append(str(step.support2))
            note = step.note or (", ".join(parts) if parts else None)
            rule_label = RULE_LABELS.get(step.rule, step.rule)
            lines.append((depth, str(step.formula), rule_label, note))
