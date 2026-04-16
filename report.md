# JapeAI: An Automated Natural Deduction Proof Assistant

## Abstract

JapeAI is a proof assistant that automatically solves propositional and first-order logic (FOL) problems using natural deduction rules. It is built to replicate the output style of Jape, a well-known interactive proof tool developed at Oxford and QMU and a familiar tool for all Computer Science students who have taken CISC 204. Unlike Jape, which requires the user to apply rules manually, JapeAI finds the proof on its own and displays it in a format that closely matches what Jape produces. The system uses three independent solving strategies: a Constraint Satisfaction Problem (CSP) solver that uses iterative-deepening depth-first search, a PDDL-style forward planner that uses breadth-first search, and a Bayesian Network solver that uses best-first probabilistic search guided by a causal graph. All solvers produce human-readable, step-by-step proofs through a tkinter graphical interface or a command-line interface.

---

## 1. Introduction

Natural deduction is a method of formal proof that works the way human reasoning naturally works. Instead of starting from a set of axioms, the user builds proofs by applying small, intuitive rules to formulas. Rules like modus ponens ("if P implies Q, and P is true, then Q is true") are combined step by step until the desired conclusion is reached. Tools like Jape exist to help students work through these problems interactively. The goal of JapeAI is to automate this process entirely. Given a set of assumptions and a goal formula, JapeAI finds a valid proof and presents every step of that proof in a structured, readable format. Three entirely independent solvers run on every problem, each using a different AI strategy, so their outputs can be compared side by side.


---

## 2. Background

### 2.1 Natural Deduction Rules

Natural deduction proofs are built from a fixed set of introduction and elimination rules, one for each logical connective. The most commonly used rules are:

- **And-introduction**: if you can prove A and you can prove B, you can conclude A and B.
- **And-elimination**: if you have A and B, you can extract A alone or B alone.
- **Implication-introduction**: if you assume A and prove B from it, you can conclude that A implies B.
- **Implication-elimination (Modus Ponens)**: if you have A, and you have A implies B, you can conclude B.
- **Negation-introduction**: if assuming A leads to a contradiction, you can conclude not-A.
- **Universal-introduction**: if you prove P(c) for an arbitrary constant c that appears nowhere else, you can conclude "for all x, P(x)".
- **Universal-elimination**: if you have "for all x, P(x)", you can substitute any specific term t to get P(t).
- **Existential-introduction**: if you have P(t) for some term t, you can conclude "there exists x such that P(x)".
- **Existential-elimination**: if you have "there exists x such that P(x)", you can introduce a fresh constant i and add P(i) to your assumptions for the duration of a sub-proof.
- **Reductio ad Absurdum (RAA)**: a classical rule that says if assuming not-A leads to a contradiction, you can conclude A.

In FOL proofs, universal-intro and existential-elim require careful handling of fresh constants. A fresh constant is a placeholder name (like i, j, or k) that stands in for an arbitrary object. It must not appear anywhere outside the scope in which it was introduced.

### 2.2 The Jape Proof Format

Jape displays proofs as a numbered list of lines. Each line shows the formula derived and the rule used to derive it. Scoped sub-proofs (such as those inside an assumption block or an existential-elimination block) are visually indented. A typical Jape proof for a problem with existential-elimination looks like this:

```
1: forall x. forall z. (~Q(z) & S(x))    premise
2: exists x. forall z. (S(x) -> Q(z))    assumption
3: actual i, forall z. (S(i) -> Q(z))    assumptions
4: S(i) -> Q(i)                          forall elim
5: forall z. (~Q(z) & S(i))              forall elim
6: ~Q(i) & S(i)                          forall elim
7: ~Q(i)                                 and elim
8: S(i)                                  and elim
9: Q(i)                                  -> elim
10: False                                 not elim
11: False                                 exists elim
12: ~(exists x. forall z. (S(x) -> Q(z))) not intro
```

Line 3 marks the opening of the existential-elimination scope. Lines 4 through 10 are inside that scope. Line 11 closes the scope by recording that a contradiction was derived. Line 12 concludes the negation-introduction that started at line 2. The indentation and scoping are what make Jape proofs easy to follow. Replicating this exact structure, including the "actual i" label and the nested scope behaviour, was one of the core design goals of JapeAI.

---

## 3. System Architecture

JapeAI is written in Python and a small amount of PDDL. The codebase is split into five main components:

1. **Parser** (`parser/`): A Lark-based grammar that parses formula strings into an abstract syntax tree (AST). It supports all standard connectives and quantifiers, with both symbolic Unicode input (like -> for implication) and keyboard-friendly ASCII equivalents.

2. **Logic layer** (`logic/`): Utility functions shared across all solvers, including capture-avoiding substitution, free variable collection, term collection, fresh constant generation, and contradiction detection.

3. **Solvers** (`csp/`, `planning/`, `cbn/`): Three independent proof search engines. All three take a list of assumption formulas and a goal formula and return a structured proof or action sequence. Each uses a fundamentally different search strategy.

4. **Bayesian guidance** (`bayes/`): A Naive Bayes scoring layer used by the CSP solver and the Bayes solver to rank candidate proof steps by predicted success probability.

5. **GUI** (`viz/`): A tkinter-based graphical interface that lets the user type assumptions and a goal, choose a solver, run the proof, and view the result in a formatted proof pane. It includes an examples menu, a symbol palette, copy-to-clipboard support, and a Given pane that mirrors the Jape interface.


---

## 4. The CSP Solver

### 4.1 Overview

The CSP solver is the primary solving engine. It is modelled as a constraint satisfaction problem where the "constraint" is that the proof tree must be valid under natural deduction rules. The solver works by goal-directed recursive decomposition for structural rules, and forward chaining for elimination and introduction rules.

The high-level strategy is iterative deepening: the solver first tries to find a proof using zero forward steps, then one, then two, and so on up to a configurable bound. This guarantees that the shortest proof is found first. The solver also runs in two passes: the first pass disallows RAA, so that direct (constructive) proofs are always preferred when they exist. The second pass enables RAA for problems that genuinely require classical reasoning.

![CSP solver output](images/CSP_solver_output.png)

### 4.2 Forward Rules

Forward rules are rules that consume known formulas and produce new ones. They are:

- **Universal-elimination**: instantiate a universally quantified formula with a known term.
- **And-elimination**: extract the left or right side of a conjunction.
- **Modus Ponens**: if A and A -> B are both known, derive B.
- **Existential-introduction**: if P(t) is known and the goal involves "there exists x. P(x)", derive the existential.
- **Or-introduction**: if A is known and A or B is a relevant goal, derive A or B.
- **And-introduction**: if both A and B are known, derive A and B.

Each forward rule costs one step from the budget. The solver tries all valid one-step derivations, sorts them by relevance to the goal, and recurses with a reduced budget.

### 4.3 Structural Rules

Structural rules deal with the shape of the goal itself. They are applied for free (no step cost) because they are directed by the goal and do not require search. They are: universal-introduction (introduce a fresh constant and prove the body), implication-introduction (add the antecedent to assumptions and prove the consequent), negation-introduction (add the positive form and derive a contradiction), existential-introduction (try each known term as a witness), or-introduction (try either disjunct), and-introduction (prove both conjuncts), existential-elimination (introduce a fresh constant for each existential in the assumptions), and or-elimination (case split on each disjunction in the assumptions).

### 4.4 Contradiction Search

When the solver needs to derive a contradiction (for negation-introduction or RAA), it calls a dedicated sub-routine called `_fol_solve_contra`. This function works in two phases. Phase 1 is eager saturation: apply and-elimination, modus ponens, and existential-introduction for implication antecedents eagerly to a fixed point. Every step derived in this phase is recorded as an explicit proof step. This phase is fast because it runs iteratively without recursion. Phase 2 is recursive search: if saturation did not find a contradiction, the solver tries structural rules that require branching -- existential-elimination, universal-elimination, or-elimination, and the "prove the positive" strategy for each negation in context. The separation into two phases is important for correctness and performance. Phase 1 handles all the deterministic steps efficiently, while phase 2 handles the branching cases that require actual search.

### 4.5 Fresh Constants

Fresh constants are generated from a fixed sequence: i, j, k, a, b, c, and so on. This matches the naming convention used by Jape. The counter is reset before each iterative-deepening attempt so that different depth levels do not pollute each other with stale constant names.

### 4.6 Proof Representation

The CSP solver returns a tree of typed proof step objects rather than a flat list of strings. The types are: `FOLStep` for flat forward derivations; `FOLForAllIntroStep`, `FOLImpIntroStep`, `FOLNotIntroStep`, `FOLExistsElimStep`, `FOLOrElimStep`, and `FOLRAAStep` for scoped sub-proofs, each carrying a nested tuple of child steps. This tree structure is flattened into display tuples by the renderer, which assigns depth levels to each line for visual indentation in the GUI.

---

## 5. The PDDL-Style Forward Planner

### 5.1 Overview

The second solver is inspired by PDDL (Planning Domain Definition Language), a formalism used in classical AI planning. In PDDL, a planning problem consists of an initial state, a set of actions with preconditions and effects, and a goal state. The planner searches for a sequence of actions that transforms the initial state into the goal state. In JapeAI, the "state" is the set of formulas currently known, the "actions" are forward proof rules, and the "goal" is the target formula.

![PDDL solver output](images/PDDL_solver_output.png)

### 5.2 Algorithm

The planner uses a hybrid approach that matches the CSP solver's two-phase design but with a different search strategy for forward rules. Structural rules (universal-intro, implication-intro, negation-intro, existential-elim, or-elim) are handled by goal-directed recursive decomposition, identical in structure to the CSP solver. Forward rules (universal-elim, and-elim, modus ponens, existential-intro, or-intro, and-intro) are explored via breadth-first search (BFS) over the known formula state. BFS guarantees that the shortest sequence of forward steps is found first. This is the key algorithmic difference from the CSP solver, which uses depth-first iterative deepening. The planner also runs in two passes -- direct proofs first, then classical -- and resets the fresh constant counter before each attempt.

### 5.3 Differences from CSP

The main difference between the two solvers is not the rules they implement but how they explore the space of forward derivations. The CSP solver is depth-first: it commits to a forward step and recurses immediately. The PDDL planner is breadth-first: it generates all possible one-step derivations, checks each one, and only recurses after confirming that the structural rules cannot close the proof at the current state. This makes the planner more systematic but also more memory-intensive for large problems. Both solvers find correct proofs on all test problems; the step ordering in the output may differ slightly between the two.

---

## 6. The Bayes Solver

### 6.1 Overview

The third solver is built around a Structural Causal Model (SCM) / Bayesian Network approach. Its purpose is to be genuinely independent of the other two solvers -- not just a wrapper around the same search algorithm with different parameters, but a different algorithmic approach at every level. The three mechanisms that distinguish it are: a causal graph built from the assumption set with a d-separation filter that prunes irrelevant formulas before search begins; a best-first priority queue guided by cumulative Naive Bayes step-success probabilities; and the full FOL structural rule set applied as goal-directed decomposition before the forward search.

![Bayes solver output](images/Bayes_solver_output.png)

### 6.2 Step 1 -- Causal Graph and D-Separation Filter

The first thing the Bayes solver does is build a directed acyclic graph (DAG) from the implications in the assumption set. Every atomic sub-formula (P, Q, T(x), etc.) becomes a node. For each implication A -> B in the assumptions, directed edges are drawn from every atom of A to every atom of B. Edges that would create a cycle are dropped to maintain the DAG property.

Once the graph is built, the solver uses the Bayes-ball algorithm to compute d-separation. A formula in the search domain is considered causally irrelevant if all of its atoms are d-separated from all goal atoms given the observed assumption atoms. Such formulas are removed from the domain before search begins. This pruning reduces the number of candidate steps the forward search must consider, which is especially effective on large problems with many irrelevant implications.


### 6.3 Step 2 -- Best-First Probabilistic Search

After pruning, the solver runs a best-first forward search using a priority queue (min-heap). Each state in the queue is a frozenset of known formulas together with the sequence of steps that produced it. The priority of a state is its cumulative negative log-probability under a Naive Bayes step-success model: at each step, the model scores the step by extracting features (rule type, formula complexity, depth, goal proximity) and returning a probability that this step leads to a successful proof. States with high cumulative probability are expanded first.

This strategy differs fundamentally from the other two solvers. The CSP solver always expands the deepest unexplored branch of its iterative-deepening tree (depth-first). The PDDL planner expands all states at depth d before any state at depth d+1 (breadth-first). The Bayes solver always expands the single most promising state regardless of depth, which means it can jump directly to a deep proof if the Naive Bayes model assigns it a high score.

### 6.4 Step 3 -- Full FOL Structural Decomposition

Before the forward search runs, the solver applies the same structural rules as the CSP solver: universal-introduction, implication-introduction, negation-introduction, and-introduction, or-introduction, existential-introduction, existential-elimination, and or-elimination. These rules are applied recursively on the goal and can reduce a complex FOL goal to a simpler sub-goal before any forward search is needed. Only once the structural rules have been exhausted does the forward search take over.

This three-level design -- causal pruning, then structural decomposition, then Bayesian best-first search -- means the Bayes solver solves most problems without needing to run the forward search at all. For the problems where forward search is needed, the pruned domain and the Bayesian priority ordering make it much more efficient than a naive exhaustive search.

### 6.5 Proof Representation

The Bayes solver reuses the same `FOLProofStep` type hierarchy as the CSP solver (`FOLStep`, `FOLImpIntroStep`, `FOLForAllIntroStep`, etc.) and the same `render_fol_csp_steps` renderer. This means the GUI displays Bayes solver proofs in exactly the same visual format as CSP solver proofs, with identical indentation, rule labels, and scope bars. The only difference visible to the user is the solver label in the header.

---

## 7. The Parser and AST

Formulas are parsed using the Lark parsing library with a hand-written LALR(1) grammar. The grammar defines operator precedence from tightest to loosest: atoms and predicates, then negation, then quantifiers, then conjunction, then disjunction, then implication (right-associative). This ordering means that a formula like `forall y. T(y) -> Q(y)` parses as `forall y. (T(y) -> Q(y))`, which matches mathematical convention.

The parser produces an AST using dataclass-based node types: Atom, Var, Predicate, Not, And, Or, Imp, ForAll, and Exists. All node types are frozen (immutable) and implement `__hash__` and `__eq__` so they can be stored in Python sets and used as dictionary keys. This property is essential for the solvers, which track the "known formulas" state as a Python frozenset. Substitution is implemented as a recursive function that performs capture-avoiding replacement: if a bound variable in a quantifier shadows the variable being substituted, the substitution does not descend into that quantifier's body. This prevents incorrect proofs from being generated when fresh constants happen to match bound variable names.

---

## 8. The GUI

The graphical interface is built with tkinter and runs on Windows and macOS. It uses a three-row toolbar design. Row 1 contains the assumptions text box, a turnstile symbol as a static label, and the goal text box. Both boxes use a grid layout with minimum-width constraints so they never disappear when the window is resized. Row 2 contains the Prove, Clear, and Copy buttons, radio buttons for choosing CSP, PDDL, or Bayes, and a status label that shows timing and result information. Row 3 is a symbol palette for inserting Unicode logic symbols into the text boxes.


Below the toolbar, the window is split vertically into a proof pane (top) and a Given pane (bottom). The proof pane scrolls and renders each proof line with colour-coded left accent bars: violet for premises and assumption lines, indigo for rule labels. Each line shows the step number, the formula, and the rule label. The Given pane shows the assumption formulas as clickable buttons, similar to how Jape displays the hypothesis panel.


The interface also supports keyboard shortcuts for inserting Unicode symbols. Typing `->` automatically converts to the arrow symbol, `forall` converts to the upside-down A, `exists` converts to the backwards E, and so on. An Examples menu in the menu bar provides pre-loaded problems at three difficulty levels.

![Examples dropdown menu](images/Examples_dropdown_menu.png)

On macOS the menu bar (File, Proof, Examples) appears at the top of the screen rather than at the top of the application window, which is standard macOS behaviour. The GUI uses platform-aware font and widget settings so buttons and text boxes render correctly with both the Windows and macOS native themes.

---

## 9. Results

### 9.1 Test Problems

The system was tested against a set of twelve FOL problems taken from a course problem sheet, organised into three difficulty levels. All twelve problems were solved correctly by all three solvers (CSP, PDDL, and Bayes).


**Level 1 problems** involve basic combinations of universal and existential quantifiers:

- `forall y. (T(y) -> Q(y) & R(y))  |-  forall y. (T(y) -> exists z. Q(z))`
- `exists y. Q(y) | exists z. S(z)  |-  exists x. (S(x) | Q(x))`
- `exists y. T(y), forall y. (T(y) -> R(y))  |-  exists y. R(y)`

**Level 2 problems** require more complex combinations of negation, disjunction, and quantifier interaction:

- `forall x. forall z. (~Q(z) & S(x))  |-  ~exists x. forall z. (S(x) -> Q(z))`
- `exists x. ~Q(x), forall x. R(x) | forall x. Q(x), forall x. (R(x) -> T(x))  |-  forall x. T(x)`
- `forall y. T(y) | forall y. S(y), exists y. ~T(y), forall y. (S(y) -> P(y))  |-  forall y. P(y)`

**Level 3 problems** require RAA or multi-level scope nesting that cannot be proved constructively:

- `forall y. forall z. (exists x. ~R(x) -> (P(z) -> ~Q(y)))  |-  forall y. forall z. forall x. ((P(z) & Q(x)) -> R(z))`
- and five further problems of similar depth.

![Level 3 proof comparison](images/Level_3_Jape_comparison.png)

### 9.2 Solve Times

Eleven of the twelve problems solve in under 200 milliseconds across all three solvers. The one exception is the hardest Level 3 problem for the CSP solver, which requires three nested universal-introductions followed by a RAA sub-proof and takes approximately 34 seconds. The PDDL planner and Bayes solver both solve this problem in under 2 seconds, because their search strategies (BFS and best-first respectively) explore the proof space in a different order than the CSP solver's iterative deepening. Profiling shows that the CSP bottleneck is in the forward-step generation phase, which is called over 200,000 times during the iterative-deepening search. The Bayes solver's causal pruning and best-first ordering significantly reduce the number of states explored.

### 9.3 Comparison to Jape Output

The following table compares the JapeAI CSP output to the expected Jape output for the Level 2 problem `forall x. forall z. (~Q(z) & S(x))  |-  ~exists x. forall z. (S(x) -> Q(z))`:

**Jape output:**
```
1:  forall x. forall z. (~Q(z) & S(x))    premise
2:  exists x. forall z. (S(x) -> Q(z))    assumption
3:  actual i, forall z. (S(i) -> Q(z))    assumptions
4:  S(i) -> Q(i)                          forall elim
5:  forall z. (~Q(z) & S(i))              forall elim
6:  ~Q(i) & S(i)                          forall elim
7:  ~Q(i)                                 and elim
8:  S(i)                                  and elim
9:  Q(i)                                  -> elim
10: False                                  not elim
11: False                                  exists elim
12: ~(exists x. forall z. (S(x) -> Q(z))) not intro
```

**JapeAI CSP output:**
```
1:  forall x. forall z. (~Q(z) & S(x))    premise
2:  exists x. forall z. (S(x) -> Q(z))    assumption
3:  [ actual i, forall z. (S(i) -> Q(z)) ] assumptions
4:  S(i) -> Q(i)                          forall elim
5:  forall z. (~Q(z) & S(i))              forall elim
6:  ~Q(i) & S(i)                          forall elim
7:  ~Q(i)                                 and elim L
8:  S(i)                                  and elim R
9:  Q(i)                                  -> elim
10: False                                  not elim
11: False                                  exists elim
12: ~(exists x. forall z. (S(x) -> Q(z))) not intro
```

The two outputs match closely. The structural layout, the fresh constant naming (i), the "assumptions" label on the existential-elimination scope line, and the rule names are all consistent with Jape. The minor differences are: JapeAI wraps the existential-elimination scope header in brackets; JapeAI labels and-elimination as "and elim L" and "and elim R" to distinguish the two sides; and the order of and-elimination steps is swapped because the CSP solver tries the left conjunct before the right. These differences are cosmetic and do not affect the correctness or readability of the proof.

![Level 1 Jape comparison](images/Level_1_Jape_comparison.png)

![Level 2 Jape comparison](images/Level_2_Jape_comparison.png)

---

## 10. Limitations and Future Work

### 10.1 Performance on Deep Problems

As noted above, problems that require many nested structural rules combined with iterative-deepening forward search can be slow for the CSP solver. Possible improvements include memoizing failed sub-problems so the same state is not re-explored across multiple depth iterations; pruning forward step candidates more aggressively by checking whether they contribute to the goal; and replacing iterative deepening with A* search guided by a heuristic that estimates distance to the goal. The Bayes solver's best-first approach already partially addresses this by prioritising promising states, but its Naive Bayes model is trained on simple examples and may not generalise well to very deep proofs.

### 10.2 PDDL Proof Display

The PDDL planner currently outputs a flat list of action strings. These do not carry the scoping information needed to display a nested proof like the CSP solver produces. Restructuring the planner to return a typed proof tree (using the same `FOLProofStep` hierarchy) would allow its output to be rendered in the same Jape-style format with indentation and scope bars.

### 10.3 Equality and Function Symbols

The current parser and solvers do not support function symbols or equality. Many interesting FOL problems require reasoning about `f(x) = g(y)` or similar. Adding a simple congruence closure algorithm for equality reasoning would significantly expand the range of problems JapeAI can handle.

### 10.4 Proof Checking

JapeAI currently trusts its own output. A separate proof-checking pass that independently verifies each step in the returned proof tree would add robustness and catch any bugs in the solver logic.

---

## 11. Conclusion

JapeAI demonstrates that a compact Python implementation using standard search algorithms can automatically produce natural deduction proofs that closely match the output of a dedicated proof assistant like Jape. Three independent solvers -- iterative-deepening CSP, breadth-first PDDL planning, and Bayesian best-first search with causal graph pruning -- each find correct proofs for all test problems using fundamentally different algorithms. The CSP solver's hybrid structural-decomposition and forward-search design produces output that matches Jape's proof format in all essential respects. The PDDL planner provides an independent verification pathway. The Bayes solver introduces a probabilistic approach that is faster than CSP on the hardest problems thanks to its causal pruning step and best-first expansion order.

The project shows that the gap between "automated theorem prover" and "proof assistant with human-readable output" can be bridged without deep mathematical machinery. The key insight is that natural deduction's own rule structure -- with its clear division between introduction rules (which decompose the goal) and elimination rules (which derive new facts from what is known) -- provides a natural decomposition for both the search algorithm and the proof renderer. All three solvers exploit this same structure, which is why their outputs are visually compatible despite using entirely different search strategies.
