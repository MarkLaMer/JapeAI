![CI Tests](https://github.com/MarkLaMer/JapeAI/actions/workflows/ci.yml/badge.svg)
[![codecov](https://codecov.io/gh/MarkLaMer/JapeAI/branch/main/graph/badge.svg)](https://codecov.io/gh/MarkLaMer/JapeAI)

# JapeAI

JapeAI is an experimental theorem-proving project that applies three independent AI approaches to first-order logic (FOL) proof construction, run side-by-side on the same problems for comparison.

| Approach | File | Strategy |
|---|---|---|
| CSP | `csp/fol_csp.py` | Iterative-deepening depth-first search with backtracking |
| PDDL planner | `planning/internal_planner.py` | Uniform breadth-first BFS |
| Bayes | `cbn/logic_causal.py` | CBN/SCM-guided factor propagation with recursive structural proof rules |
| Backward prover | `logic/fol_prover.py` | Goal-directed recursive backward chaining (used by CLI) |

---

## Logic Supported

### Formula syntax

| Syntax | Meaning | Notes |
|---|---|---|
| `P`, `Q`, `R` | Atomic propositions | Uppercase identifiers |
| `P(x)`, `T(x,y)` | Predicates | Lowercase arguments |
| `forall x.P(x)` | Universal quantifier | Also accepts `forall x.(...)` |
| `exists x.P(x)` | Existential quantifier | Also accepts `exists x.(...)` |
| `A & B` | Conjunction | Also `/\` |
| `A \| B` | Disjunction | Also `\/` |
| `A -> B` | Implication | Right-associative |
| `~A` | Negation | |
| `(A -> B)` | Grouping | |

### Inference rules

All four solvers handle:

- Assumption / Given
- Modus Ponens (-> elim)
- And Introduction / Elimination
- Implication Introduction (assume antecedent, prove consequent, discharge)
- ForAll Introduction / Elimination (instantiation)
- Exists Introduction / Elimination (Skolem constants)
- Or Introduction / Elimination (case split)
- Not Introduction (assume positive, derive contradiction)
- RAA -- Reductio ad Absurdum (classical fallback)
- Ex Falso (from contradiction, prove anything)

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

tkinter is bundled with Python on Windows and macOS. On Linux install it separately:
```bash
sudo apt install python3-tk
```

---

## Running the GUI

```
python viz/gui.py
```

Opens a graphical proof assistant with:
- Assumptions and Goal entry fields with live Unicode substitution
- Prove / Clear / Copy buttons
- Solver selector (CSP / PDDL / Bayes radio buttons)
- Proof pane showing numbered steps with rule labels and scope bars
- Given pane showing loaded assumptions as clickable buttons
- File / Proof / Examples menu bar

**On macOS:** the menu bar (File, Proof, Examples) appears at the top of the screen, not the window -- this is standard macOS behaviour.

### Keyboard shortcuts

| Keys | Action |
|---|---|
| Ctrl+Return | Prove |
| Ctrl+L | Clear |
| Ctrl+C | Copy proof |
| Ctrl+Q | Quit |

### Symbol shortcuts (type in any entry field)

| Type | Gets |
|---|---|
| `->` | -> (implication arrow) |
| `forall` | forall |
| `exists` | exists |
| `/\` | /\ (conjunction) |
| `\/` | \/ (disjunction) |
| `~` | ~ (negation) |
| `\|-` | |- (turnstile) |

---

## Running the CLI

### Interactive mode
```
python main.py
```
Prompts for assumptions and a goal. Runs CSP, the internal PDDL planner, and the backward prover. The Bayes / CBN solver also has its own CLI modes.

```
Assumptions (comma-separated, or blank): P, P -> Q, Q -> R
Goal: R

============================================================
Assumptions : ['P', '(P -> Q)', '(Q -> R)']
Goal        : R
============================================================

[CSP solver]
  Step 0: Q  by mp
  Step 1: R  by mp

[PDDL planner]
  Step 0: mp(P, (P -> Q)) => Q
  Step 1: mp(Q, (Q -> R)) => R

[Backward prover]
  Q   by -> elim
  P   by assumption
  R   by -> elim
```

### Flags

| Flag | Effect |
|---|---|
| `--demo` | Run all built-in example problems |
| `--pddl` | Also write a .pddl problem file |
| `--causal` | Run interactive Bayes / CBN / SCM mode only |
| `--causal-prove` | Run one Bayes / CBN / SCM proof from flags |
| `--causal-demo` | Run Bayes / CBN / SCM demo problems |

---

## Formula Syntax Reference

```
Atoms           P  Q  R  ABC        uppercase identifiers
Predicates      T(x)  R(x,y)        uppercase name, lowercase args
Variables       x  y  z             lowercase (used inside quantifiers)
Negation        ~P
Conjunction     P & Q
Disjunction     P | Q
Implication     P -> Q              right-associative
ForAll          forall x.P(x)
Exists          exists x.P(x)
Grouping        (P & Q) -> R
```

---

## Approach 1: CSP (Constraint Satisfaction)

**Files:** `csp/fol_csp.py`, `csp/skeleton_csp.py`

Models proof construction as a bounded constraint problem. Each proof step is a variable that takes a value from a finite formula domain; constraints enforce rule correctness.

**Key features:**
- `solve_fol_csp()` -- FOL solver with iterative deepening; tries direct proofs first, then classical RAA
- `solve_csp()` -- propositional solver (legacy, still tested)
- Two-pass strategy: direct proofs always preferred over RAA proofs of the same length
- Optional Bayesian guidance utilities are available elsewhere in the repo, but the FOL CSP solver itself is an iterative-deepening proof search over explicit forward steps and structural sub-proofs

**Programmatic usage:**
```python
from parser.parser import parse_formula
from csp.fol_csp import solve_fol_csp, render_fol_csp_steps

assumptions = [parse_formula("forall y.(T(y) -> Q(y))"), parse_formula("forall y.T(y)")]
goal = parse_formula("forall y.Q(y)")

result = solve_fol_csp(assumptions, goal)
lines = []
render_fol_csp_steps(result, lines)
for depth, formula, rule, note in lines:
    print("  " * depth + formula + "   by " + rule)
```

---

## Approach 2: PDDL Planner

**Files:** `planning/domain.pddl`, `planning/encoder.py`, `planning/internal_planner.py`

Models theorem proving as a classical planning problem:

```
state   = set of known formulas
actions = inference rules
goal    = target theorem is in the known set
```

`planning/internal_planner.py` implements a forward BFS planner that works directly on Formula objects -- no external tool needed. Two-pass: direct proofs first, then RAA.

```python
from parser.parser import parse_formula
from planning.internal_planner import plan_forward

result = plan_forward(
    [parse_formula("exists y.T(y)"), parse_formula("forall y.(T(y) -> R(y))")],
    parse_formula("exists y.R(y)"),
)
```

### External PDDL planner

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

Load `planning/domain.pddl` and the generated file into any STRIPS planner (e.g. editor.planning.domains).

---

## Approach 3: Bayes Solver (Bayesian Network / CBN / SCM)

**Files:** `cbn/logic_causal.py`, `cbn/factor_bp.py`, `cbn/graph.py`, `cbn/scm.py`

The Bayes solver is now an independent CBN / SCM-backed proof engine.

It works in four layers:

1. **Parse formulas into ASTs** using `parser/parser.py`.
2. **Build a causal graph** in `cbn/logic_causal.py` by turning implication structure into a DAG over atomic sub-formulas.
3. **Build an SCM** in `cbn/scm.py` where given atoms are point-mass true, derivable consequents are controlled by structural equations, and unknown atoms default to false.
4. **Run the factor-style proof engine** in `cbn/factor_bp.py`, which saturates the current context by deterministic propagation and then recursively applies structural natural-deduction rules.

The Bayes / CBN solver does not delegate proof search to CSP or PDDL. The CBN / SCM layer supplies:

- dependency structure via `CausalGraph`
- topological ordering for propagation
- deterministic reachability hints via `SCM.sample()`
- compatibility with d-separation and other causal queries

The proof engine on top handles:

- forward propagation rules such as `∀ elim`, `∧ elim`, `→ elim`, and target-driven `∧/∨/∃` intro
- structural rules such as `→ intro`, `∀ intro`, `∃ elim`, `∨ elim`, `¬ intro`, and `RAA`

In deterministic logical problems, the SCM behaves like a hard Bayes net and the solver's fixed-point propagation acts like message passing over that structure.

```python
from parser.parser import parse_formula
from cbn.logic_causal import solve_logic_causal, render_logic_causal_steps

result = solve_logic_causal(
    [parse_formula("forall x.(P(x) -> T(x))")],
    parse_formula("exists x.P(x) -> exists x.T(x)"),
)
lines = []
render_logic_causal_steps(result, lines)
for depth, formula, rule, note in lines:
    print("  " * depth + formula + "   by " + rule)
```

---

## Approach 4: Backward Logic Prover

**File:** `logic/fol_prover.py`

Goal-directed recursive backward chaining. Used by the CLI to provide a fourth independent view of the proof.

```python
from parser.parser import parse_formula
from logic.fol_prover import prove_fol, render_fol_proof

result = prove_fol(
    parse_formula("(P & Q) -> (Q & P)"),
    [],
)
lines = []
render_fol_proof(result, lines)
for depth, formula, rule, note in lines:
    print("  " * depth + formula + "   by " + rule)
```

---

## Bayesian Guidance

**Files:** `bayes/features.py`, `bayes/scorer.py`, `bayes/trainer.py`

A Naive Bayes scoring layer used for experimental ranking utilities elsewhere in the repo. It is distinct from the current independent CBN / SCM solver in `cbn/`.

| Toggle | Effect |
|---|---|
| `BN_FORMULA_REORDER` | Reorder formula domain by predicted usefulness |
| `BN_RULE_REORDER` | Try rules in order of predicted success probability |
| `BN_STEP_REORDER` | Rank candidate steps by predicted success |
| `BN_PARTIAL_CUTOFF` | Prune branches with very low success probability |

---

## Running Tests

```
pytest
```

260 tests covering parser, AST, FOL prover, CSP (propositional + FOL), PDDL planner (propositional + FOL), Bayes solver (propositional + FOL Levels 1-3), causal graph, d-separation, SCM, A* and BFS search.

```
pytest -v                          # verbose output
pytest tests/test_csp.py           # CSP tests only
pytest tests/test_bayes_solver.py  # Bayes solver tests only
pytest tests/test_fol_prover.py    # backward prover tests only
pytest --cov=. --cov-report=term   # coverage report
```

---

## Project Structure

```
parser/         formula parser and AST
logic/          FOL backward prover, matcher, proof tree
csp/            CSP solver (propositional + FOL)
planning/       PDDL domain, encoder, internal BFS planner
cbn/            Bayes / CBN / SCM solver, causal graph, d-separation, SCM
bayes/          Naive Bayes feature extraction and scoring utilities
search/         A* and BFS search over proof states
viz/            GUI (tkinter)
tests/          pytest test suite
main.py         interactive CLI and demo runner
```

---

## Project Goal

Explore and compare four AI paradigms applied to the same logical reasoning task:

- logic -> constraint satisfaction (iterative deepening DFS)
- logic -> classical planning (BFS)
- logic -> causal Bayes net guidance + SCM-backed factor propagation
- logic -> backward chaining (goal-directed recursion)
