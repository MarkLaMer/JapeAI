from parser.parser import parse_formula
from search.state import SearchState
from search.planner import bfs_plan


def make_state(ctx_strings, goal_string):
    context = frozenset(parse_formula(s) for s in ctx_strings)
    goal = parse_formula(goal_string)
    return SearchState(goals=(goal,), context=context, depth=0)


def test_search_assumption():
    result = bfs_plan(make_state(["P"], "P"))
    assert result.success


def test_search_mp():
    result = bfs_plan(make_state(["P", "P -> Q"], "Q"))
    assert result.success


def test_search_imp_intro():
    result = bfs_plan(make_state([], "P -> P"))
    assert result.success


def test_search_and_intro():
    result = bfs_plan(make_state(["P", "Q"], "P & Q"))
    assert result.success


def test_search_failure():
    result = bfs_plan(make_state(["P"], "Q"))
    assert not result.success
