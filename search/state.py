from __future__ import annotations

from dataclasses import dataclass, field
from parser.ast import Formula

# The search algorithm explores states like this:
# Initial State
#    |
#    | apply rule
#    v
# State A
#    |
#    v
# State B
#    |
#    v
# Goal State

@dataclass(frozen=True)
class SearchState:
    goals: tuple[Formula, ...]  # This represents the list of goals we still need to prove. Because the state is frozen, we must use immutable structures.
    context: frozenset[Formula] # This represents everything we already know to be true.
    depth: int = 0              # This tracks how deep we are in the search tree. depth = 0 (root state) depth = 1 (one inference step) depth = 2 (deeper inference)

    def is_goal(self) -> bool:
        """
        This checks whether all goals have been solved.
        If there are no remaining goals, the proof is complete.
        """
        return len(self.goals) == 0

    def current_goal(self) -> Formula | None:
        """
        This returns the next goal to work on.
        Search algorithms usually prove one goal at a time.
        """
        if not self.goals:
            return None  # nothing left to prove to my gf
        return self.goals[0]