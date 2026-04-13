![CI Tests](https://github.com/MarkLaMer/JapeAI/actions/workflows/ci.yml/badge.svg)
[![codecov](https://codecov.io/gh/MarkLaMer/JapeAI/branch/main/graph/badge.svg)](https://codecov.io/gh/MarkLaMer/JapeAI)

# JapeAI

JapeAI is an experimental theorem-proving project that models propositional proof construction using three distinct AI approaches, run side-by-side on the same problems for comparison.

| Approach | File | Method |
|---|---|---|
| CSP | `csp/skeleton_csp.py` | Forward search with backtracking + Bayesian guidance |
| Planning | `planning/` | PDDL encoding + internal forward BFS planner |
| Backward prover | `logic/rules.py` | Goal-directed recursive backward chaining |

---

## Logic Supported

Formula types:

| Syntax | Meaning |
|---|---|
| `P`, `Q`, `R` | Atomic propositions (uppercase) |
| `A & B` | Conjunction |
| `A -> B` | Implication |
| `~A` | Negation |

Inference rules:

- Assumption
- Modus Ponens
- And Introduction
- And Elimination (left / right)
- **Implication Introduction** — assume antecedent, derive consequent, discharge hypothesis

---

## Setup

**Windows (PowerShell):**
```powershell
git clone <repo-url>
cd JapeAI
python -m venv .venv
.venv\Scripts\Activate.ps1
pip install -r requirements.txt
```

**Mac / Linux:**
```bash
git clone <repo-url>
cd JapeAI
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
```

---

## Running the CLI

### Interactive mode (default)
```
python main.py
```
You are prompted for assumptions and a goal. All three solvers run and print their proofs side-by-side.

```
Assumptions (comma-separated, or blank): P, P -> Q, Q -> R
Goal: R
Write PDDL file? [y/N]: n

============================================================
Assumptions : ['P', '(P -> Q)', '(Q -> R)']
Goal        : R
============================================================

[CSP solver]
  Proof (2 top-level step(s)):
    Step 0: Q  by modus_ponens, P, (P -> Q)
    Step 1: R  by modus_ponens, (Q -> R), Q

[Internal PDDL planner]
  Plan (2 steps):
    1. modus-ponens(P, Q, (P -> Q))
    2. modus-ponens(Q, R, (Q -> R))

[Backward logic prover]
  Proof tree:
  R         by MP
   Q         by MP
    P         by Assumption
    (P -> Q)         by Given
   (Q -> R)         by Given
```

### Demo mode
```
python main.py --demo
```
Runs 8 built-in problems covering all rule types including ImpIntro, long chains, and unprovable cases.

---

## Formula Syntax Reference

```
Atoms       P  Q  R  ABC           uppercase identifiers
Negation    ~P
Conjunction P & Q
Implication P -> Q                 right-associative
Grouping    (P & Q) -> R
```

Examples of valid goals:
```
P -> P
(P & Q) -> (Q & P)
P -> (Q -> P)
R
```

---

## Approach 1: CSP (Constraint Satisfaction)

**File:** `csp/skeleton_csp.py`

Models proof construction as a bounded constraint problem:
- each proof step is a variable that can take values from a finite formula domain
- constraints enforce rule correctness at each step
- backtracking search finds a valid proof skeleton

**Key features:**
- `solve_csp()` — iterative deepening wrapper; automatically finds the shortest proof without needing to guess a step bound
- `solve_bounded_csp()` — fixed-depth version for when you know the bound
- **Implication Introduction** — handled as a recursive sub-proof: to prove `A → B`, the solver assumes `A` and proves `B` in a nested scope, then discharges the hypothesis
- Bayesian guidance — optional reordering and pruning of candidates using Naive Bayes scores (formula usefulness, rule success, partial proof success probability)

**Example problems:**

| Problem | Assumptions | Goal |
|---|---|---|
| Modus Ponens | `P`, `P -> Q` | `Q` |
| AND elimination | `P & Q` | `P` |
| Chain | `P`, `P->Q`, `Q->R`, `R->S` | `S` |
| ImpIntro (tautology) | _(none)_ | `P -> P` |
| AND commutativity | _(none)_ | `(P & Q) -> (Q & P)` |
| K tautology | _(none)_ | `P -> (Q -> P)` |

**Programmatic usage:**
```python
from parser.parser import parse_formula
from csp.skeleton_csp import solve_csp, print_csp_proof

assumptions = [parse_formula("P"), parse_formula("P -> Q")]
goal = parse_formula("Q")

result = solve_csp(assumptions, goal)
print_csp_proof(result)
```

---

## Approach 2: Planning (PDDL)

**Files:** `planning/domain.pddl`, `planning/encoder.py`, `planning/internal_planner.py`

Models theorem proving as a classical planning problem:

```
state   = set of known formulas
actions = inference rules
goal    = target theorem is known
```

### Internal planner

`planning/internal_planner.py` implements a forward BFS planner that works directly on `Formula` objects — no external tool needed.

```python
from parser.parser import parse_formula
from planning.internal_planner import plan_and_print

plan_and_print(
    [parse_formula("P"), parse_formula("P -> Q")],
    parse_formula("Q"),
)
```

### External PDDL planner

Generate a `.pddl` problem file and load it into any STRIPS planner:

```python
from parser.parser import parse_formula
from planning.encoder import write_problem_file

write_problem_file(
    "planning/problems/my_problem.pddl",
    "my-problem",
    [parse_formula("P"), parse_formula("P -> Q")],
    parse_formula("Q"),
)
```

Then open [editor.planning.domains](https://editor.planning.domains/), load `planning/domain.pddl` and your problem file, and run BFWS.

**PDDL domain actions:** `modus-ponens`, `and-elim-left`, `and-elim-right`, `and-intro`, `imp-intro-weaken`

---

## Approach 3: Backward Logic Prover

**File:** `logic/rules.py`

Goal-directed recursive backward chaining. Supports all five rules including full Implication Introduction (scoped hypothetical reasoning).

```python
from parser.parser import parse_formula
from logic.rules import prove
from logic.proof_tree import print_proof

result = prove(parse_formula("(P & Q) -> (Q & P)"), set())
print_proof(result)
```

---

## Bayesian Guidance

**Files:** `bayes/features.py`, `bayes/scorer.py`, `bayes/trainer.py`

A Naive Bayes scoring layer integrated into the CSP solver. Four configurable scorers guide the search:

| Toggle | Effect |
|---|---|
| `BN_FORMULA_REORDER` | Reorder the formula domain by predicted usefulness |
| `BN_RULE_REORDER` | Try rules in order of predicted success probability |
| `BN_STEP_REORDER` | Rank candidate steps by predicted success |
| `BN_PARTIAL_CUTOFF` | Prune branches with very low success probability |

These are on by default and can be toggled at the top of `csp/skeleton_csp.py`.

---

## Running Tests

```
pytest
```

48 tests covering parser, AST, logic rules, CSP (forward rules + ImpIntro + iterative deepening + longer chains), search (A* and BFS), and the internal PDDL planner.

```
pytest -v              # verbose output
pytest tests/test_csp.py   # CSP tests only
```

---

## Project Structure

```
parser/         formula parser and AST
logic/          backward prover, matcher, proof tree
csp/            CSP solver with Bayesian guidance
planning/       PDDL domain, encoder, internal planner
search/         A* and BFS search over proof states
bayes/          Naive Bayes feature extraction and scoring
tests/          pytest test suite
main.py         interactive CLI and demo runner
```

---

## Project Goal

Explore and compare three AI paradigms applied to the same logical reasoning task:

> logic → constraint satisfaction  
> logic → classical planning  
> logic → probabilistic guidance
