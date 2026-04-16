from parser.parser import parse_formula
from csp.skeleton_csp import (
    solve_bounded_csp,
    solve_csp,
    CSPImpIntroStep,
    print_csp_proof,
)
from csp.fol_csp import solve_fol_csp


def print_result(name, assumptions, goal, result):
    """
    Helper to print experiment results so we can
    easily copy them into the report tables.
    """

    print("\n----------------------------------")
    print("Problem:", name)
    print("Assumptions:", assumptions)
    print("Goal:", goal)

    if result is None:
        print("Result: failure")
        return

    print("Result: success")
    print("Steps found:", len(result))
    print_csp_proof(result)


# ────────────────────────────────────────────────
# Original forward-rule tests (unchanged semantics)
# ────────────────────────────────────────────────

def test_csp_and_intro():
    assumptions = [parse_formula("P"), parse_formula("Q")]
    goal = parse_formula("P & Q")

    result = solve_bounded_csp(assumptions, goal, max_steps=2)

    print_result("prove_p_and_q_from_p_q", ["P", "Q"], "P & Q", result)
    assert result is not None


def test_csp_and_elim():
    assumptions = [parse_formula("P & Q")]
    goal = parse_formula("P")

    result = solve_bounded_csp(assumptions, goal, max_steps=2)

    print_result("prove_p_from_p_and_q", ["P & Q"], "P", result)
    assert result is not None


def test_csp_modus_ponens():
    assumptions = [parse_formula("P"), parse_formula("P -> Q")]
    goal = parse_formula("Q")

    result = solve_bounded_csp(assumptions, goal, max_steps=2)

    print_result("prove_q_from_p_imp_q", ["P", "P -> Q"], "Q", result)
    assert result is not None


def test_csp_two_step_chain():
    assumptions = [
        parse_formula("P"),
        parse_formula("P -> Q"),
        parse_formula("Q -> R"),
    ]
    goal = parse_formula("R")

    result = solve_bounded_csp(assumptions, goal, max_steps=3)

    print_result(
        "prove_r_from_p_imp_q_q_imp_r",
        ["P", "P -> Q", "Q -> R"],
        "R",
        result,
    )
    assert result is not None


def test_csp_failure():
    assumptions = [parse_formula("P")]
    goal = parse_formula("Q")

    result = solve_bounded_csp(assumptions, goal, max_steps=3)

    print_result("unprovable_example", ["P"], "Q", result)
    assert result is None


# ────────────────────────────────────────────────
# Implication Introduction tests
# ────────────────────────────────────────────────

def test_csp_imp_intro_reflexive():
    """Prove P -> P from no assumptions (identity tautology)."""
    assumptions: list = []
    goal = parse_formula("P -> P")

    result = solve_csp(assumptions, goal)

    print_result("prove_p_imp_p", [], "P -> P", result)
    assert result is not None
    # Should be a single CSPImpIntroStep
    assert len(result) == 1
    assert isinstance(result[0], CSPImpIntroStep)
    assert result[0].rule == "imp_intro"


def test_csp_imp_intro_weakening():
    """Prove P -> (Q -> P) from no assumptions (K tautology)."""
    assumptions: list = []
    goal = parse_formula("P -> (Q -> P)")

    result = solve_csp(assumptions, goal)

    print_result("prove_p_imp_q_imp_p", [], "P -> (Q -> P)", result)
    assert result is not None


def test_csp_imp_intro_with_context():
    """Prove Q -> (P & Q) given P is already known."""
    assumptions = [parse_formula("P")]
    goal = parse_formula("Q -> (P & Q)")

    result = solve_csp(assumptions, goal)

    print_result("prove_q_imp_p_and_q_from_p", ["P"], "Q -> (P & Q)", result)
    assert result is not None


def test_csp_imp_intro_and_commute():
    """Prove (P & Q) -> (Q & P) from no assumptions."""
    assumptions: list = []
    goal = parse_formula("(P & Q) -> (Q & P)")

    result = solve_csp(assumptions, goal)

    print_result("prove_and_commute", [], "(P & Q) -> (Q & P)", result)
    assert result is not None


def test_csp_chain_from_imp_intro():
    """Prove P -> R given (P -> Q) -> R is an assumption and P -> Q is provable."""
    # From P->Q (assumption) and (P->Q)->R (assumption), prove P->R.
    assumptions = [
        parse_formula("P -> Q"),
        parse_formula("(P -> Q) -> R"),
    ]
    goal = parse_formula("P -> R")

    result = solve_csp(assumptions, goal)

    print_result("prove_p_imp_r_via_chain", ["P -> Q", "(P -> Q) -> R"], "P -> R", result)
    assert result is not None


# ────────────────────────────────────────────────
# Longer chain tests
# ────────────────────────────────────────────────

def test_csp_three_step_chain():
    """Prove S from a four-link MP chain."""
    assumptions = [
        parse_formula("P"),
        parse_formula("P -> Q"),
        parse_formula("Q -> R"),
        parse_formula("R -> S"),
    ]
    goal = parse_formula("S")

    result = solve_csp(assumptions, goal)

    print_result("prove_s_four_link_chain", ["P", "P->Q", "Q->R", "R->S"], "S", result)
    assert result is not None


def test_csp_five_step_chain():
    """Prove U from a six-link MP chain."""
    assumptions = [
        parse_formula("P"),
        parse_formula("P -> Q"),
        parse_formula("Q -> R"),
        parse_formula("R -> S"),
        parse_formula("S -> U"),
    ]
    goal = parse_formula("U")

    result = solve_csp(assumptions, goal)

    print_result("prove_u_six_link_chain", ["P", "P->Q", "Q->R", "R->S", "S->U"], "U", result)
    assert result is not None


def test_csp_iterative_deepening_finds_shortest():
    """solve_csp should find the 1-step proof, not a longer redundant one."""
    assumptions = [parse_formula("P"), parse_formula("Q")]
    goal = parse_formula("P & Q")

    result = solve_csp(assumptions, goal)

    print_result("prove_p_and_q_shortest", ["P", "Q"], "P & Q", result)
    assert result is not None
    # Shortest proof is 1 step (AND-INTRO)
    assert len(result) == 1


# ────────────────────────────────────────────────
# Internal PDDL planner tests
# ────────────────────────────────────────────────

def test_internal_planner_mp():
    from planning.internal_planner import plan_forward
    assumptions = [parse_formula("P"), parse_formula("P -> Q")]
    goal = parse_formula("Q")

    result = plan_forward(assumptions, goal)
    assert result is not None
    print("\n[internal planner] MP plan:", result)


def test_internal_planner_chain():
    from planning.internal_planner import plan_forward
    assumptions = [
        parse_formula("P"),
        parse_formula("P -> Q"),
        parse_formula("Q -> R"),
    ]
    goal = parse_formula("R")

    result = plan_forward(assumptions, goal)
    assert result is not None
    print("\n[internal planner] chain plan:", result)


def test_internal_planner_imp_intro():
    from planning.internal_planner import plan_forward
    assumptions: list = []
    goal = parse_formula("P -> P")

    result = plan_forward(assumptions, goal)
    assert result is not None
    print("\n[internal planner] P->P plan:", result)


def test_internal_planner_failure():
    from planning.internal_planner import plan_forward
    assumptions = [parse_formula("P")]
    goal = parse_formula("Q")

    result = plan_forward(assumptions, goal, max_depth=5)
    assert result is None
    print("\n[internal planner] correctly returned None for unprovable P |- Q")


# ────────────────────────────────────────────────
# FOL CSP solver tests
# ────────────────────────────────────────────────

def _pf(s: str):
    return parse_formula(s)


def _fol_rules(result) -> list[str]:
    """Flatten all rule names from a FOLProofStep tree."""
    from csp.fol_csp import FOLStep
    rules = []
    for s in result:
        if hasattr(s, "rule"):
            rules.append(s.rule)
        if hasattr(s, "sub_steps"):
            rules.extend(_fol_rules(list(s.sub_steps)))
        for attr in ("left_steps", "right_steps", "contra_steps"):
            if hasattr(s, attr):
                rules.extend(_fol_rules(list(getattr(s, attr))))
    return rules


def _fol_conclusions(result) -> list[str]:
    out = []
    for s in result:
        if hasattr(s, "formula"):
            out.append(str(s.formula))
        if hasattr(s, "sub_steps"):
            out.extend(_fol_conclusions(list(s.sub_steps)))
        for attr in ("left_steps", "right_steps", "contra_steps"):
            if hasattr(s, attr):
                out.extend(_fol_conclusions(list(getattr(s, attr))))
    return out


# --- Propositional (FOL solver handles propositional as a special case) ---

def test_fol_csp_modus_ponens():
    result = solve_fol_csp([_pf("P"), _pf("P -> Q")], _pf("Q"))
    assert result is not None
    assert "mp" in _fol_rules(result)


def test_fol_csp_and_intro():
    result = solve_fol_csp([_pf("P"), _pf("Q")], _pf("P & Q"))
    assert result is not None
    assert "and_intro" in _fol_rules(result)


def test_fol_csp_imp_intro_tautology():
    result = solve_fol_csp([], _pf("P -> P"))
    assert result is not None
    assert "imp_intro" in _fol_rules(result)


def test_fol_csp_and_commutativity():
    result = solve_fol_csp([], _pf("(P & Q) -> (Q & P)"))
    assert result is not None


def test_fol_csp_unprovable():
    result = solve_fol_csp([_pf("P")], _pf("Q"))
    assert result is None


# --- FOL Warm-up ---

def test_fol_csp_warmup_forall_mp():
    """forall y.(T(y)->Q(y)), forall y.T(y) |- forall y.Q(y)"""
    result = solve_fol_csp(
        [_pf("forall y.(T(y) -> Q(y))"), _pf("forall y.T(y)")],
        _pf("forall y.Q(y)"),
    )
    assert result is not None


# --- FOL Level 1 ---

def test_fol_csp_level1_forall_exists():
    """forall y.(T(y)->Q(y)/\R(y)) |- forall y.(T(y)->exists z.Q(z))"""
    result = solve_fol_csp(
        [_pf("forall y.(T(y) -> (Q(y) & R(y)))")],
        _pf("forall y.(T(y) -> exists z.Q(z))"),
    )
    assert result is not None


def test_fol_csp_level1_disjunction():
    """exists y.Q(y) \/ exists z.S(z) |- exists x.(S(x) \/ Q(x))"""
    result = solve_fol_csp(
        [_pf("exists y.Q(y) | exists z.S(z)")],
        _pf("exists x.(S(x) | Q(x))"),
    )
    assert result is not None


def test_fol_csp_level1_exists_forall():
    """exists y.T(y), forall y.(T(y)->R(y)) |- exists y.R(y)"""
    result = solve_fol_csp(
        [_pf("exists y.T(y)"), _pf("forall y.(T(y) -> R(y))")],
        _pf("exists y.R(y)"),
    )
    assert result is not None


# --- FOL Level 2 ---

def test_fol_csp_level2_neg_push():
    """forall x.forall z.(~Q(z)/\S(x)) |- ~exists x.forall z.(S(x)->Q(z))"""
    result = solve_fol_csp(
        [_pf("forall x.forall z.(~Q(z) & S(x))")],
        _pf("~exists x.forall z.(S(x) -> Q(z))"),
    )
    assert result is not None


def test_fol_csp_level2_case_split():
    """exists x.~Q(x), forall x.R(x)\/forall x.Q(x), forall x.(R(x)->T(x)) |- forall x.T(x)"""
    result = solve_fol_csp(
        [
            _pf("exists x.~Q(x)"),
            _pf("forall x.R(x) | forall x.Q(x)"),
            _pf("forall x.(R(x) -> T(x))"),
        ],
        _pf("forall x.T(x)"),
    )
    assert result is not None


def test_fol_csp_level2_or_elim():
    """forall y.T(y)\/forall y.S(y), exists y.~T(y), forall y.(S(y)->P(y)) |- forall y.P(y)"""
    result = solve_fol_csp(
        [
            _pf("forall y.T(y) | forall y.S(y)"),
            _pf("exists y.~T(y)"),
            _pf("forall y.(S(y) -> P(y))"),
        ],
        _pf("forall y.P(y)"),
    )
    assert result is not None


# --- PDDL FOL tests ---

def test_pddl_warmup_forall_mp():
    from planning.internal_planner import plan_forward
    result = plan_forward(
        [_pf("forall y.(T(y) -> Q(y))"), _pf("forall y.T(y)")],
        _pf("forall y.Q(y)"),
    )
    assert result is not None


def test_pddl_level1_exists_forall():
    from planning.internal_planner import plan_forward
    result = plan_forward(
        [_pf("exists y.T(y)"), _pf("forall y.(T(y) -> R(y))")],
        _pf("exists y.R(y)"),
    )
    assert result is not None


def test_pddl_level1_disjunction():
    from planning.internal_planner import plan_forward
    result = plan_forward(
        [_pf("exists y.Q(y) | exists z.S(z)")],
        _pf("exists x.(S(x) | Q(x))"),
    )
    assert result is not None
