from parser.parser import parse_formula
from planning.internal_planner import plan_forward


def test_plan_forward_basic_imp_intro():
    result = plan_forward([], parse_formula("P -> P"))
    assert result is not None
    assert len(result) > 0


def test_plan_forward_raa_needed():
    assumptions = [parse_formula("P -> Q"), parse_formula("~Q")]
    result = plan_forward(assumptions, parse_formula("~P"))
    assert result is not None
    assert any("raa" in action or "not-intro" in action or "contradiction" in action for action in result)
