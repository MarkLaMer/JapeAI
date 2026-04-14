"""
logic/fol_prover.py — Backward prover for first-order propositional logic.

Supports all connectives (∧ ∨ → ¬) plus quantifiers (∀ ∃).

Proof rules implemented:
  Intro  : ∧-intro, →-intro, ∀-intro, ∃-intro, ∨-intro L/R, ¬-intro
  Elim   : ∧-elim (via context expansion), →-elim (MP),
           ∀-elim (instantiation), ∃-elim (Skolem constant),
           ∨-elim (case split)
  Classical : RAA (reductio ad absurdum), Ex Falso (from ⊥)
"""
from __future__ import annotations

from typing import Optional, FrozenSet

from parser.ast import (
    Formula, Atom, Not, And, Imp, Or, Var, Predicate, ForAll, Exists
)
from logic.proof_tree import ProofNode

# ---------------------------------------------------------------------------
# Sentinel for "bottom" / falsum
# ---------------------------------------------------------------------------
_FALSE = Atom("⊥")

# ---------------------------------------------------------------------------
# Fresh constant generator
# ---------------------------------------------------------------------------
# Names cycle through i, j, k first (Jape convention), then the rest of the
# alphabet, then i0, j0, k0, i1, … for overflow.
_FRESH_SEQ = ['i', 'j', 'k', 'a', 'b', 'c', 'd', 'e', 'f', 'g',
              'h', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't',
              'u', 'v', 'w', 'x', 'y', 'z']
_counter: list[int] = [0]


def reset_fresh() -> None:
    _counter[0] = 0


def _fresh() -> Var:
    n = _counter[0]
    _counter[0] += 1
    if n < len(_FRESH_SEQ):
        return Var(_FRESH_SEQ[n])
    overflow = n - len(_FRESH_SEQ)
    suffix = overflow // 3
    base   = ['i', 'j', 'k'][overflow % 3]
    return Var(f"{base}{suffix}")


# ---------------------------------------------------------------------------
# Free-variable collection
# ---------------------------------------------------------------------------

def free_vars(f: Formula) -> set[str]:
    """Return names of all free variables in *f*."""
    if isinstance(f, Var):
        return {f.name}
    if isinstance(f, Atom):
        return set()
    if isinstance(f, Predicate):
        out: set[str] = set()
        for a in f.args:
            out |= free_vars(a)
        return out
    if isinstance(f, Not):
        return free_vars(f.child)
    if isinstance(f, (And, Or, Imp)):
        return free_vars(f.left) | free_vars(f.right)
    if isinstance(f, (ForAll, Exists)):
        return free_vars(f.body) - {f.var}
    return set()


def collect_terms(context: set[Formula], extra: Optional[Formula] = None) -> list[Var]:
    """All free variables / Skolem constants appearing in *context* (and *extra*)."""
    names: set[str] = set()
    for f in context:
        names |= free_vars(f)
    if extra is not None:
        names |= free_vars(extra)
    return [Var(n) for n in sorted(names)]


# ---------------------------------------------------------------------------
# Capture-avoiding substitution
# ---------------------------------------------------------------------------

def subst(f: Formula, var: str, term: Formula) -> Formula:
    """Replace every free occurrence of Var(*var*) with *term* in *f*."""
    if isinstance(f, Var):
        return term if f.name == var else f
    if isinstance(f, Atom):
        return f
    if isinstance(f, Predicate):
        new_args = tuple(subst(a, var, term) for a in f.args)
        return Predicate(f.name, new_args) if new_args != f.args else f
    if isinstance(f, Not):
        c = subst(f.child, var, term)
        return Not(c) if c is not f.child else f
    if isinstance(f, And):
        l, r = subst(f.left, var, term), subst(f.right, var, term)
        return And(l, r) if (l is not f.left or r is not f.right) else f
    if isinstance(f, Or):
        l, r = subst(f.left, var, term), subst(f.right, var, term)
        return Or(l, r) if (l is not f.left or r is not f.right) else f
    if isinstance(f, Imp):
        l, r = subst(f.left, var, term), subst(f.right, var, term)
        return Imp(l, r) if (l is not f.left or r is not f.right) else f
    if isinstance(f, ForAll):
        if f.var == var:
            return f           # bound variable shadows substitution
        return ForAll(f.var, subst(f.body, var, term))
    if isinstance(f, Exists):
        if f.var == var:
            return f
        return Exists(f.var, subst(f.body, var, term))
    return f


# ---------------------------------------------------------------------------
# Context expansion helpers
# ---------------------------------------------------------------------------

def _expand_conj_mp(context: set[Formula]) -> set[Formula]:
    """Saturate context with ∧-elim and forward MP (fixed point)."""
    expanded = set(context)
    changed = True
    while changed:
        changed = False
        additions: set[Formula] = set()
        for f in list(expanded):
            if isinstance(f, And):
                for part in (f.left, f.right):
                    if part not in expanded:
                        additions.add(part)
            elif isinstance(f, Imp):
                if f.left in expanded and f.right not in expanded:
                    additions.add(f.right)
        if additions:
            expanded |= additions
            changed = True
    return expanded


def _expand_with_witnesses(context: set[Formula]) -> set[Formula]:
    """
    Like _expand_conj_mp, but also adds ∃x.P(x) when:
      - there is an implication  ∃x.P(x) → B  in context, AND
      - some instantiation P(t) is already known.
    This lets the prover fire such implications without a separate sub-proof.
    """
    expanded = _expand_conj_mp(context)
    changed = True
    while changed:
        changed = False
        terms = {n for f in expanded for n in free_vars(f)}
        additions: set[Formula] = set()
        for f in list(expanded):
            if isinstance(f, Imp) and isinstance(f.left, Exists):
                ex = f.left
                for name in terms:
                    witness = subst(ex.body, ex.var, Var(name))
                    if witness in expanded and ex not in expanded:
                        additions.add(ex)
                        break
        if additions:
            expanded |= additions
            expanded = _expand_conj_mp(expanded)
            changed = True
    return expanded


def _contradiction(ctx: set[Formula]) -> Optional[tuple[Formula, Formula]]:
    """Return (pos, neg) if both A and ¬A appear in *ctx*, else None."""
    for f in ctx:
        if isinstance(f, Not) and f.child in ctx:
            return (f.child, f)
        if not isinstance(f, Not) and Not(f) in ctx:
            return (f, Not(f))
    return None


# ---------------------------------------------------------------------------
# Main FOL prover
# ---------------------------------------------------------------------------

MAX_DEPTH = 16          # maximum recursion depth
_Keys = FrozenSet[tuple]  # type alias for the seen-set


def fol_prove(
    goal: Formula,
    context: set[Formula],
    depth: int = 0,
    _keys: _Keys = frozenset(),
) -> Optional[ProofNode]:
    """
    Backward FOL prover.

    *_keys* tracks (rule-tag, formula-strings) pairs to prevent the same
    elimination from being applied twice on the same proof path, avoiding
    infinite loops.
    """
    if depth > MAX_DEPTH:
        return None

    expanded = _expand_conj_mp(context)

    # ── Contradiction / Ex Falso ─────────────────────────────────────────────
    contra = _contradiction(expanded)
    if contra:
        pos, neg = contra
        return ProofNode(goal, "ExFalso",
                         [ProofNode(pos, "Given"), ProofNode(neg, "Given")])

    # ── Assumption ───────────────────────────────────────────────────────────
    if goal in expanded:
        return ProofNode(goal, "Assumption")

    def _sub(g: Formula, ctx: set[Formula] = expanded,
             d: Optional[int] = None, k: _Keys = _keys) -> Optional[ProofNode]:
        return fol_prove(g, ctx, depth + 1 if d is None else d, k)

    # ════════════════════════════════════════════════════════════════════════
    # INTRO rules  (goal-directed)
    # ════════════════════════════════════════════════════════════════════════

    # ∧-intro
    if isinstance(goal, And):
        l = _sub(goal.left)
        if l:
            r = _sub(goal.right)
            if r:
                return ProofNode(goal, "AndIntro", [l, r])

    # →-intro
    if isinstance(goal, Imp):
        child = _sub(goal.right, expanded | {goal.left})
        if child:
            return ProofNode(goal, "ImpIntro", [child],
                             note=f"assume {goal.left}")

    # ∀-intro  (introduce a fresh Skolem constant for the bound variable)
    if isinstance(goal, ForAll):
        c = _fresh()
        subgoal = subst(goal.body, goal.var, c)
        child = _sub(subgoal)
        if child:
            return ProofNode(goal, "ForAllIntro", [child],
                             note=f"{goal.var}↦{c}")

    # ∃-intro  (try every available ground term as witness)
    if isinstance(goal, Exists):
        for term in collect_terms(expanded, goal):
            subgoal = subst(goal.body, goal.var, term)
            if subgoal == goal:
                continue
            key = ("∃I", str(goal), str(term))
            if key in _keys:
                continue
            child = _sub(subgoal, k=_keys | {key})
            if child:
                return ProofNode(goal, "ExistsIntro", [child],
                                 note=f"{goal.var}↦{term}")

    # ∨-intro  (try left branch, then right branch)
    if isinstance(goal, Or):
        child = _sub(goal.left)
        if child:
            return ProofNode(goal, "OrIntroL", [child])
        child = _sub(goal.right)
        if child:
            return ProofNode(goal, "OrIntroR", [child])

    # ¬-intro  (assume the positive form, derive ⊥)
    if isinstance(goal, Not):
        new_ctx = expanded | {goal.child}
        contra_pf = _find_contradiction(new_ctx, depth + 1, _keys)
        if contra_pf:
            return ProofNode(goal, "NotIntro", [contra_pf])

    # ════════════════════════════════════════════════════════════════════════
    # ELIM rules  (context-directed)
    # ════════════════════════════════════════════════════════════════════════

    terms = collect_terms(expanded, goal)

    # →-elim  (Modus Ponens: find A→goal in context, prove A)
    for f in expanded:
        if isinstance(f, Imp) and f.right == goal:
            prem = _sub(f.left)
            if prem:
                return ProofNode(goal, "MP",
                                 [prem, ProofNode(f, "Given")])

    # ∀-elim  (instantiate universals with available ground terms)
    for f in list(expanded):
        if not isinstance(f, ForAll):
            continue
        for term in terms:
            key = ("∀E", str(f), str(term))
            if key in _keys:
                continue
            instance = subst(f.body, f.var, term)
            if instance in expanded:
                continue
            new_keys = _keys | {key}
            result = fol_prove(goal, expanded | {instance},
                               depth + 1, new_keys)
            if result:
                return ProofNode(goal, "ForAllElim", [result],
                                 note=f"{f.var}↦{term}")

    # ∃-elim  (introduce a fresh Skolem constant for each existential)
    for f in list(expanded):
        if not isinstance(f, Exists):
            continue
        key = ("∃E", str(f))
        if key in _keys:
            continue
        c = _fresh()
        instance = subst(f.body, f.var, c)
        new_keys = _keys | {key}
        result = fol_prove(goal, expanded | {instance},
                           depth + 1, new_keys)
        if result:
            return ProofNode(goal, "ExistsElim", [result],
                             note=f"{f.var}→{c}")

    # ∨-elim  (case split: prove goal from each disjunct separately)
    for f in list(expanded):
        if not isinstance(f, Or):
            continue
        key = ("∨E", str(f))
        if key in _keys:
            continue
        new_keys = _keys | {key}
        l_pf = fol_prove(goal, expanded | {f.left},  depth + 1, new_keys)
        if l_pf:
            r_pf = fol_prove(goal, expanded | {f.right}, depth + 1, new_keys)
            if r_pf:
                return ProofNode(goal, "OrElim", [l_pf, r_pf],
                                 note=f"cases on {f}")

    # ════════════════════════════════════════════════════════════════════════
    # Classical rule: RAA
    # Assume ¬goal, derive ⊥ — then conclude goal.
    # (Not goals are already handled by NotIntro above.)
    # ════════════════════════════════════════════════════════════════════════
    if not isinstance(goal, Not) and goal != _FALSE:
        neg = Not(goal)
        if neg not in expanded:
            contra_pf = _find_contradiction(expanded | {neg}, depth + 1, _keys)
            if contra_pf:
                return ProofNode(goal, "RAA", [contra_pf])

    return None


# ---------------------------------------------------------------------------
# Contradiction finder  (prove ⊥ from context)
# ---------------------------------------------------------------------------

def _find_contradiction(
    context: set[Formula],
    depth: int,
    _keys: _Keys,
) -> Optional[ProofNode]:
    """
    Try to derive ⊥ (a contradiction) from *context*.

    Strategies applied in order:
      1. Direct contradiction A ∧ ¬A after aggressive forward closure.
      2. Prove the positive part of each ¬F in context using fol_prove.
      3. ∀-elim: instantiate universals with available terms.
      4. ∃-elim: introduce fresh constants for existentials.
      5. ∨-elim: case-split on disjunctions.
    """
    if depth > MAX_DEPTH:
        return None

    # Step 1 — aggressive expansion (includes ∃-witness for implications)
    expanded = _expand_with_witnesses(context)

    contra = _contradiction(expanded)
    if contra:
        pos, neg = contra
        return ProofNode(_FALSE, "Contradiction",
                         [ProofNode(pos, "Given"), ProofNode(neg, "Given")])

    # Step 2 — prove positive part of each negation in context
    for f in list(expanded):
        if isinstance(f, Not):
            # Try to prove f.child using the full prover (minus the negation itself)
            proof = fol_prove(f.child, expanded - {f}, depth + 1, _keys)
            if proof:
                return ProofNode(_FALSE, "Contradiction",
                                 [proof, ProofNode(f, "Given")])

    terms = collect_terms(expanded)

    # Step 3 — ∀-elim
    for f in list(expanded):
        if not isinstance(f, ForAll):
            continue
        for term in terms:
            key = ("∀E⊥", str(f), str(term))
            if key in _keys:
                continue
            instance = subst(f.body, f.var, term)
            if instance in expanded:
                continue
            new_keys = _keys | {key}
            result = _find_contradiction(expanded | {instance},
                                         depth + 1, new_keys)
            if result:
                return result

    # Step 4 — ∃-elim
    for f in list(expanded):
        if not isinstance(f, Exists):
            continue
        key = ("∃E⊥", str(f))
        if key in _keys:
            continue
        c = _fresh()
        instance = subst(f.body, f.var, c)
        new_keys = _keys | {key}
        result = _find_contradiction(expanded | {instance},
                                     depth + 1, new_keys)
        if result:
            return result

    # Step 5 — ∨-elim (case split)
    for f in list(expanded):
        if not isinstance(f, Or):
            continue
        key = ("∨E⊥", str(f))
        if key in _keys:
            continue
        new_keys = _keys | {key}
        l = _find_contradiction(expanded | {f.left},  depth + 1, new_keys)
        if l:
            r = _find_contradiction(expanded | {f.right}, depth + 1, new_keys)
            if r:
                return ProofNode(_FALSE, "OrElim⊥", [l, r],
                                 note=f"cases on {f}")

    return None


# ---------------------------------------------------------------------------
# Public entry point
# ---------------------------------------------------------------------------

def prove_fol(
    goal: Formula,
    assumptions: list[Formula],
) -> Optional[ProofNode]:
    """Prove *goal* from *assumptions* using FOL backward search."""
    reset_fresh()
    return fol_prove(goal, set(assumptions))


# ---------------------------------------------------------------------------
# Flat rendering helper (for GUI)
# ---------------------------------------------------------------------------

def render_fol_proof(node: ProofNode, lines: list, depth: int = 0) -> None:
    """
    Flatten a FOL ProofNode tree into a list of display tuples
    (depth, formula_str, rule_str, note_str | None).
    Children (premises) are rendered before their conclusion.
    """
    RULE_LABELS = {
        "Assumption":  "assumption",
        "ExFalso":     "ex falso",
        "Contradiction": "⊥",
        "AndIntro":    "∧ intro",
        "ImpIntro":    "→ intro",
        "ForAllIntro": "∀ intro",
        "ExistsIntro": "∃ intro",
        "OrIntroL":    "∨ intro L",
        "OrIntroR":    "∨ intro R",
        "NotIntro":    "¬ intro",
        "MP":          "→ elim",
        "ForAllElim":  "∀ elim",
        "ExistsElim":  "∃ elim",
        "OrElim":      "∨ elim",
        "OrElim⊥":     "∨ elim",
        "RAA":         "RAA",
        "Given":       "given",
    }

    # Skip internal "Given" leaf nodes — they appear as notes on parent steps
    if node.rule == "Given":
        return

    for child in node.children:
        render_fol_proof(child, lines, depth)

    rule_label = RULE_LABELS.get(node.rule, node.rule)
    lines.append((depth, str(node.conclusion), rule_label, node.note))
