from __future__ import annotations

from collections import deque
from dataclasses import dataclass
from typing import Optional

from parser.ast import Formula, And, Imp
from search.state import SearchState
from logic.matcher import expand_context

# Make it full proper A* search :)


@dataclass
class PlannerResult:
    success: bool
    visited_count: int
    final_state: Optional[SearchState] = None


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