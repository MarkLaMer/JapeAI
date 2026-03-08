


# Repurpose it as:

# - internal prototype for understanding search behavior
# - comparison baseline in the report
# - maybe support for the Bayesian/CSP sides




from __future__ import annotations

from collections import deque
import heapq # Instead of exploring in FIFO order like BFS, it explores the most promising state first

from dataclasses import dataclass
from itertools import count
from typing import Optional

from parser.ast import Formula, Atom, Not, And, Imp
from search.state import SearchState
from logic.matcher import expand_context

@dataclass
class PlannerResult:
    success: bool
    visited_count: int
    final_state: Optional[SearchState] = None

def formula_complexity(formula: Formula) -> int:
    """
    gives the heuristic some structural sense
    """
    if isinstance(formula, Atom):
        return 1
    if isinstance(formula, Not):
        return 1 + formula_complexity(formula.child)
    if isinstance(formula, And):
        return 1 + formula_complexity(formula.left) + formula_complexity(formula.right)
    if isinstance(formula, Imp):
        return 1 + formula_complexity(formula.left) + formula_complexity(formula.right)
    return 1

def heuristic(state: SearchState) -> int:
    """
    Estimate remaining work
    COmbines:
    - num of remaining goals
    - structural complexity of goals
    """
    num_goals = len(state.goals)
    total_complexity = sum(formula_complexity(goal) for goal in state.goals)
    return num_goals + total_complexity

def successors(state: SearchState) -> list[SearchState]:
    if state.is_goal():
        return []

    expanded = expand_context(set(state.context))
    goal = state.current_goal()
    rest_goals = state.goals[1:]

    next_states: list[SearchState] = []

    # Rule 1: Assumption
    if goal in expanded:
        next_states.append(
            SearchState(
                goals=rest_goals,
                context=frozenset(expanded),
                depth=state.depth + 1,
            )
        )

    # Rule 2: And Introduction
    if isinstance(goal, And):
        next_states.append(
            SearchState(
                goals=(goal.left, goal.right) + rest_goals,
                context=frozenset(expanded),
                depth=state.depth + 1,
            )
        )

    # Rule 3: Implication Introduction
    if isinstance(goal, Imp):
        new_context = set(expanded)
        new_context.add(goal.left)
        next_states.append(
            SearchState(
                goals=(goal.right,) + rest_goals,
                context=frozenset(new_context),
                depth=state.depth + 1,
            )
        )

    # Rule 4: Modus Ponens
    for formula in expanded:
        if isinstance(formula, Imp) and formula.right == goal:
            next_states.append(
                SearchState(
                    goals=(formula.left,) + rest_goals,
                    context=frozenset(expanded),
                    depth=state.depth + 1,
                )
            )

    return next_states

def astar_plan(initial_state: SearchState, max_depth: int = 20) -> PlannerResult:
    """
    A* search over proof states.
    Priority = g + h, where:
    - g = depth
    - h = heuristic estimate of remaining work
    """
    frontier: list[tuple[int, int, SearchState]] = []
    tie_breaker = count()

    initial_f = initial_state.depth + heuristic(initial_state)
    heapq.heappush(frontier, (initial_f, next(tie_breaker), initial_state))

    visited_count = 0
    best_g: dict[SearchState, int] = {initial_state: initial_state.depth}

    while frontier:
        _, _, state = heapq.heappop(frontier)
        visited_count += 1

        if state.is_goal():
            return PlannerResult(
                success=True,
                visited_count=visited_count,
                final_state=state,
            )

        if state.depth >= max_depth:
            continue

        for nxt in successors(state):
            g = nxt.depth

            # Only keep this path if it's the best known cost to that state
            if nxt not in best_g or g < best_g[nxt]:
                best_g[nxt] = g
                f = g + heuristic(nxt)
                heapq.heappush(frontier, (f, next(tie_breaker), nxt))

    return PlannerResult(
        success=False,
        visited_count=visited_count,
        final_state=None,
    )

def bfs_plan(initial_state: SearchState, max_depth: int = 20) -> PlannerResult:
    queue = deque([initial_state])
    visited: set[SearchState] = set()

    while queue:
        state = queue.popleft()

        if state in visited:
            continue
        visited.add(state)

        if state.is_goal():
            return PlannerResult(
                success=True,
                visited_count=len(visited),
                final_state=state,
            )

        if state.depth >= max_depth:
            continue

        for nxt in successors(state):
            if nxt not in visited:
                queue.append(nxt)

    return PlannerResult(
        success=False,
        visited_count=len(visited),
        final_state=None,
    )

