![CI Tests](https://github.com/MarkLaMer/JapeAI/actions/workflows/ci.yml/badge.svg)
[![codecov](https://codecov.io/gh/MarkLaMer/JapeAI/branch/main/graph/badge.svg)](https://codecov.io/gh/MarkLaMer/JapeAI)

# JapeAI

JapeAI is an experimental theorem-proving project that models propositional proof construction using multiple AI approaches.

The current approaches are:
1. Constraint Satisfaction (CSP) for bounded proof skeleton search
2. Classical Planning (PDDL) for modeling proofs as plans
3. Bayesian guidance (planned but not implemented yet)

At the moment the approaches are implemented in initial form.

---

# Logic Supported
The current implementation supports a small fragment of propositional logic.

Formula types:
- atoms: P, Q, R
- conjunction: A & B
- implication: A -> B
- negation: ~A

Inference rules currently implemented:
- assumption
- modus ponens
- and introduction
- and elimination (left)
- and elimination (right)

This restricted fragment is intentional to keep the CSP and planning approaches manageable.

# Setup

1. Clone the repository

```
git clone <repo-url>
cd japeai
```

2. Create a virtual environment

Windows:
```
python -m venv .venv
.venv\Scripts\Activate.ps1
```

Mac/Linux
```
python3 -m venv .venv
source .venv/bin/activate
```

3. Install dependencies
```
pip install -r requirements.txt
```

---

# Approach 1: CSP (Constraint Satisfaction)

The CSP approach models proof construction as a bounded constraint problem.

Idea:
- each proof step is a variable
- each variable chooses a derived formula and rule
- constraints enforce rule correctness
- a bounded search finds a valid proof skeleton

Main file:
`csp/skeleton_csp.py`

The solver:
- builds a finite domain of formulas from assumptions + goal + subformulas
- generates candidate proof steps
- checks rule constraints
- performs bounded backtracking search

### Example problems the CSP solver can handle:

`prove Q from {P, P -> Q}`

`prove P from {P & Q}`

`prove P & Q from {P, Q}`

`prove R from {P, P -> Q, Q -> R}`

### Example usage:
```
from parser.parser import parse_formula
from csp.skeleton_csp import solve_bounded_csp

assumptions = [
    parse_formula("P"),
    parse_formula("P -> Q"),
]

goal = parse_formula("Q")

solution = solve_bounded_csp(assumptions, goal, max_steps=2)

print(solution)
```

# Approach 2: Planning (PDDL)

The planning approach models theorem proving as a classical planning problem.

Conceptual mapping:

state = known formulas
actions = inference rules
goal = target theorem

Files involved:
`planning/domain.pddl`
`planning/encoder.py`
`planning/problems/`

The encoder automatically converts a theorem proving task into a PDDL problem file.

### Example:
`assumptions = [P, P -> Q]`
`goal = Q`

This becomes a planning problem where the planner must derive Q.


### Generating a PDDL Problem

Example Python code:
```
from parser.parser import parse_formula
from planning.encoder import write_problem_file

assumptions = [
    parse_formula("P"),
    parse_formula("P -> Q")
]

goal = parse_formula("Q")

write_problem_file(
    "planning/problems/prove_q_from_p_imp_q.pddl",
    "prove-q-from-p-imp-q",
    assumptions,
    goal
)
```
Then run:

`python main.py`

A problem file will appear in:

`planning/problems/`


### Running the Planning 

You can test the planning model using the online PDDL editor:

https://editor.planning.domains/

Steps:
1. open the editor
2. load planning/domain.pddl
3. load one of the generated problem files
4. choose a planner such as LAMA-first or BFWS
5. run the solver

Example expected plan:

`(modus-ponens f_p f_q f_imp_p_q)`

This corresponds to deriving Q from P and (P -> Q).

### Example PDDL Problems

`planning/problems/prove_q_from_p_imp_q.pddl`

prove Q from {P, P -> Q}

`planning/problems/prove_p_from_p_and_q.pddl`

prove P from {P & Q}

`planning/problems/prove_p_and_q_from_p_q.pddl`

prove P & Q from {P, Q}


# Approach 3: Bayesian Networks

A future extension of the system will use Bayesian scoring to guide proof search.

### Idea
Estimate probability that a rule application will lead to a successful proof.

Possible features:
- rule type
- current goal structure
- context size
- search depth

Current placeholder files:

`bayes/features.py`
`bayes/scorer.py`
`bayes/trainer.py`

This part of the system is not yet implemented.

---

# Running Tests
Run all tests with `pytest`.

Tests currently cover:
- AST correctness
- formula parsing
- rule matching
- search behavior

Additional tests will be added for CSP and planning.

---

# Project Goal
The goal of this project is to explore different AI methods for automated theorem proving.

Instead of relying on a single proof engine, JapeAI experiments with multiple perspectives:

logic -> constraint satisfaction
logic -> planning
logic -> probabilistic reasoning

This allows comparison of different AI paradigms on the same logical reasoning task.