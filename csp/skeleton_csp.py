from __future__ import annotations

from dataclasses import dataclass
from typing import Optional

from parser.ast import Formula, Atom, And, Imp, Not


# For now I am keeping the CSP rule set small and aligned
# with the same fragment used in the PDDL model.
# That way the three approaches are easier to compare fairly.
RULES = (
    "modus_ponens",
    "and_intro",
    "and_elim_left",
    "and_elim_right",
)


@dataclass(frozen=True)
class CSPStep:
    """
    One proof step in the CSP model.

    Fields:
    - formula: the formula derived at this step
    - rule: the inference rule used
    - support1 / support2: formulas used to justify the step

    Example:
    If I derive Q from P and (P -> Q), then:
    - formula = Q
    - rule = "modus_ponens"
    - support1 = P
    - support2 = (P -> Q)
    """
    formula: Formula
    rule: str
    support1: Optional[Formula] = None
    support2: Optional[Formula] = None


def formula_complexity(formula: Formula) -> int:
    """
    Return a small structural complexity score for a formula.

    Idea:
    - atoms are simplest
    - compound formulas are more complex
    - this helps the solver try "simpler-looking" candidates first

    I am not trying to make this mathematically deep.
    It is mainly just a tie-breaker / search-order helper.
    """
    if isinstance(formula, Atom):
        # Base case: atomic formulas are the simplest possible formulas.
        return 1

    if isinstance(formula, Not):
        # Negation adds one layer on top of its child formula.
        return 1 + formula_complexity(formula.child)

    if isinstance(formula, And):
        # Conjunction adds one node plus the size of both parts.
        return 1 + formula_complexity(formula.left) + formula_complexity(formula.right)

    if isinstance(formula, Imp):
        # Implication also adds one node plus the size of both parts.
        return 1 + formula_complexity(formula.left) + formula_complexity(formula.right)

    # Fallback in case Formula grows later.
    return 1


def collect_formulas(formula: Formula, out: set[Formula]) -> None:
    """
    Recursively collect a formula and all of its subformulas.

    Why this matters:
    the CSP needs a finite domain of formulas to work over.
    So instead of inventing arbitrary new formulas during search,
    I restrict the domain to:
    - assumptions
    - goal
    - all subformulas appearing inside them
    """
    # If this formula is already in the set, stop.
    # This avoids duplicate work and infinite recursion.
    if formula in out:
        return

    # Add the current formula itself.
    out.add(formula)

    # If the formula has two children, collect both recursively.
    if isinstance(formula, And) or isinstance(formula, Imp):
        collect_formulas(formula.left, out)
        collect_formulas(formula.right, out)

    # If the formula has one child, collect that child.
    elif isinstance(formula, Not):
        collect_formulas(formula.child, out)


def candidate_formula_domain(assumptions: list[Formula], goal: Formula) -> list[Formula]:
    """
    Build the bounded set of formulas the CSP is allowed to use.

    Current choice:
    domain = assumptions + goal + all their subformulas

    This keeps the search space manageable and makes the CSP finite.
    """
    # Use a set first so duplicates get removed automatically.
    formulas: set[Formula] = set()

    # Add everything that appears in the assumptions.
    for assumption in assumptions:
        collect_formulas(assumption, formulas)

    # Add everything that appears in the goal.
    collect_formulas(goal, formulas)

    # Sort to make the solver deterministic and easier to debug.
    # Simpler formulas first, then string order as a stable tie-breaker.
    return sorted(formulas, key=lambda f: (formula_complexity(f), str(f)))


def available_formulas(assumptions: list[Formula], steps: list[CSPStep]) -> list[Formula]:
    """
    Return all formulas currently available at this point in the proof.

    Available formulas include:
    - original assumptions
    - formulas derived by previous CSP steps

    I return a list instead of a set because I want stable order
    when debugging / printing / iterating.
    """
    seen: list[Formula] = []

    # Start with all assumptions.
    for formula in assumptions:
        if formula not in seen:
            seen.append(formula)

    # Add each derived formula in proof order.
    for step in steps:
        if step.formula not in seen:
            seen.append(step.formula)

    return seen


def can_apply_modus_ponens(result: Formula, support1: Formula, support2: Formula) -> bool:
    """
    Check whether a candidate step is a valid modus ponens application.

    MP can work in either order:
    - support1 = (A -> B), support2 = A
    - support1 = A,        support2 = (A -> B)

    In both cases the result should be B.
    """
    # Case 1: support1 is the implication and support2 is the premise.
    if isinstance(support1, Imp) and support1.left == support2 and support1.right == result:
        return True

    # Case 2: support2 is the implication and support1 is the premise.
    if isinstance(support2, Imp) and support2.left == support1 and support2.right == result:
        return True

    # If neither pattern matches, MP is not valid here.
    return False


def can_apply_and_intro(result: Formula, support1: Formula, support2: Formula) -> bool:
    """
    Check whether a candidate step is a valid conjunction introduction.

    For now I am using exact structural matching:
    result must literally be (support1 & support2)

    Note:
    I am not treating conjunction as commutative yet.
    So (P & Q) is different from (Q & P) in this implementation.
    """
    # The result must be an And formula, otherwise conjunction intro makes no sense.
    if not isinstance(result, And):
        return False

    # Exact structural match.
    return result.left == support1 and result.right == support2


def can_apply_and_elim_left(result: Formula, support1: Formula) -> bool:
    """
    Check whether a candidate step is a valid left conjunction elimination.

    If support1 is (A & B), then left elimination derives A.
    """
    return isinstance(support1, And) and support1.left == result


def can_apply_and_elim_right(result: Formula, support1: Formula) -> bool:
    """
    Check whether a candidate step is a valid right conjunction elimination.

    If support1 is (A & B), then right elimination derives B.
    """
    return isinstance(support1, And) and support1.right == result


def step_is_locally_valid(step: CSPStep, assumptions: list[Formula], prior_steps: list[CSPStep]) -> bool:
    """
    Check whether one candidate proof step is locally legal.

    "Locally legal" means:
    - its supports are available already
    - the rule matches the formulas structurally
    - it derives something genuinely new

    This function is one of the main CSP constraint checks.
    """
    # Compute everything currently available before this step.
    available = available_formulas(assumptions, prior_steps)

    # If the formula is already available, there is no point deriving it again.
    # This acts as a small but useful pruning rule.
    if step.formula in available:
        return False

    # Check MP constraints.
    if step.rule == "modus_ponens":
        # MP needs two supports.
        if step.support1 is None or step.support2 is None:
            return False

        # Both supports must already be available.
        if step.support1 not in available or step.support2 not in available:
            return False

        # Final structural check for MP.
        return can_apply_modus_ponens(step.formula, step.support1, step.support2)

    # Check conjunction introduction constraints.
    if step.rule == "and_intro":
        # And-intro also needs two supports.
        if step.support1 is None or step.support2 is None:
            return False

        # Both supports must be available.
        if step.support1 not in available or step.support2 not in available:
            return False

        # Final structural check for and-intro.
        return can_apply_and_intro(step.formula, step.support1, step.support2)

    # Check left conjunction elimination constraints.
    if step.rule == "and_elim_left":
        # This rule only needs one support.
        if step.support1 is None:
            return False

        # The support formula must already exist.
        if step.support1 not in available:
            return False

        # Final structural check.
        return can_apply_and_elim_left(step.formula, step.support1)

    # Check right conjunction elimination constraints.
    if step.rule == "and_elim_right":
        # This rule only needs one support.
        if step.support1 is None:
            return False

        # The support formula must already exist.
        if step.support1 not in available:
            return False

        # Final structural check.
        return can_apply_and_elim_right(step.formula, step.support1)

    # Unknown rule names are automatically invalid.
    return False


def generate_candidate_steps(
    assumptions: list[Formula],
    goal: Formula,
    prior_steps: list[CSPStep],
    formula_domain: list[Formula],
) -> list[CSPStep]:
    """
    Generate all locally valid next proof steps.

    This is where the CSP domains and constraints come together:
    - formula_domain gives the possible formulas
    - available formulas give possible supports
    - step_is_locally_valid filters candidates by rule constraints
    """
    # Figure out what formulas are usable right now.
    available = available_formulas(assumptions, prior_steps)

    # Store all locally valid candidates here before sorting/deduping.
    candidates: list[CSPStep] = []

    # Try every possible result formula against every pair of available supports
    # for the 2-support rules.
    for result in formula_domain:
        for support1 in available:
            for support2 in available:
                # Candidate MP step
                mp_step = CSPStep(
                    formula=result,
                    rule="modus_ponens",
                    support1=support1,
                    support2=support2,
                )
                if step_is_locally_valid(mp_step, assumptions, prior_steps):
                    candidates.append(mp_step)

                # Candidate conjunction introduction step
                intro_step = CSPStep(
                    formula=result,
                    rule="and_intro",
                    support1=support1,
                    support2=support2,
                )
                if step_is_locally_valid(intro_step, assumptions, prior_steps):
                    candidates.append(intro_step)

    # Try the 1-support conjunction elimination rules.
    for result in formula_domain:
        for support1 in available:
            left_step = CSPStep(
                formula=result,
                rule="and_elim_left",
                support1=support1,
            )
            if step_is_locally_valid(left_step, assumptions, prior_steps):
                candidates.append(left_step)

            right_step = CSPStep(
                formula=result,
                rule="and_elim_right",
                support1=support1,
            )
            if step_is_locally_valid(right_step, assumptions, prior_steps):
                candidates.append(right_step)

    # Sort candidates to make the solver more predictable.
    # Heuristic:
    # - prefer steps that derive the goal
    # - then prefer simpler formulas
    # - then use string/rule tie-breakers for stability
    candidates.sort(
        key=lambda step: (
            step.formula != goal,
            formula_complexity(step.formula),
            str(step.formula),
            step.rule,
        )
    )

    # Remove duplicates while preserving order.
    # This avoids trying the same exact step many times.
    unique: list[CSPStep] = []
    seen: set[CSPStep] = set()

    for step in candidates:
        if step not in seen:
            seen.add(step)
            unique.append(step)

    return unique


def solve_bounded_csp(
    assumptions: list[Formula],
    goal: Formula,
    max_steps: int = 4,
) -> Optional[list[CSPStep]]:
    """
    Solve the proof task as a bounded CSP / backtracking search problem.

    Interpretation:
    - each proof step position is like a CSP variable
    - each variable can take values from the candidate step domain
    - local rule checks act like constraints
    - max_steps bounds the proof length

    Returns:
    - a list of CSPStep objects if a proof skeleton is found
    - None if no proof is found within the bound
    """
    # Trivial case: if the goal is already assumed, no derived steps are needed.
    if goal in assumptions:
        return []

    # Build the finite domain of formulas the solver is allowed to reason about.
    formula_domain = candidate_formula_domain(assumptions, goal)

    def backtrack(partial_steps: list[CSPStep]) -> Optional[list[CSPStep]]:
        """
        Recursive backtracking search over partial proof skeletons.

        At each call:
        - check if the goal is already available
        - stop if we reached the step bound
        - generate all valid next steps
        - recursively try extending the proof
        """
        # Current knowledge = assumptions + formulas derived so far.
        current_available = available_formulas(assumptions, partial_steps)

        # Success condition: goal has been derived.
        if goal in current_available:
            return partial_steps

        # Fail if we already used up the allowed number of proof steps.
        if len(partial_steps) >= max_steps:
            return None

        # Generate all possible next steps that satisfy the local constraints.
        candidates = generate_candidate_steps(
            assumptions=assumptions,
            goal=goal,
            prior_steps=partial_steps,
            formula_domain=formula_domain,
        )

        # Try each candidate step in turn.
        for candidate in candidates:
            # Extra pruning:
            # if a candidate does not add a genuinely new formula, skip it.
            # This keeps the branching factor smaller.
            if candidate.formula in current_available:
                continue

            # Recurse with the candidate appended to the partial proof.
            result = backtrack(partial_steps + [candidate])

            # If a recursive branch succeeds, return that proof immediately.
            if result is not None:
                return result

        # If none of the candidates worked, backtrack.
        return None

    # Start the recursive search from an empty proof skeleton.
    return backtrack([])