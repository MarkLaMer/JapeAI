"""
cbn/scm.py — Structural Causal Model (SCM) layer.

Sits on top of CausalGraph (cbn/graph.py).  Each variable in the graph is
equipped with:
  • a structural equation  f_i(PA_i, U_i) → value
  • an exogenous noise variable  U_i  (discrete or functional)

This lets the model answer three rungs of Pearl's causal ladder:
  Rung 1 — Association    : P(Y | X=x)           — observe
  Rung 2 — Intervention   : P(Y | do(X=x))        — intervene
  Rung 3 — Counterfactual : P(Y_x | X=x', Y=y')   — abduct → intervene → predict

Key classes
-----------
NoiseVar        — discrete exogenous variable with a probability table
SCMVariable     — name + equation + noise attached to one node
SCM             — the full structural causal model; owns the CausalGraph

Key methods on SCM
------------------
sample(interventions)       — Rung-1/2 forward sampling
abduction(observations)     — Rung-3 step 1: infer consistent noise realizations
predict(noise, interventions) — Rung-3 step 2: replay with fixed noise
counterfactual(obs, do)     — convenience wrapper for all three abduction steps
"""
from __future__ import annotations

import itertools
from dataclasses import dataclass, field
from typing import Any, Callable, Iterable

from cbn.graph import CausalGraph


# ---------------------------------------------------------------------------
# Noise variables
# ---------------------------------------------------------------------------

@dataclass
class NoiseVar:
    """
    A discrete exogenous (noise) variable.

    name   : symbolic label, e.g. "U_Rain"
    domain : ordered list of possible values, e.g. [0, 1] or ["low","high"]
    probs  : probability for each domain value (must sum to ~1.0)
    """
    name: str
    domain: list[Any]
    probs: list[float]

    def __post_init__(self) -> None:
        if len(self.domain) != len(self.probs):
            raise ValueError(f"NoiseVar '{self.name}': domain and probs must have same length")
        total = sum(self.probs)
        if abs(total - 1.0) > 1e-6:
            raise ValueError(f"NoiseVar '{self.name}': probs must sum to 1.0, got {total}")

    def sample(self) -> Any:
        """Draw one sample from the distribution (uses Python random)."""
        import random
        r = random.random()
        cumulative = 0.0
        for val, p in zip(self.domain, self.probs):
            cumulative += p
            if r <= cumulative:
                return val
        return self.domain[-1]

    def most_likely(self) -> Any:
        """Return the mode of the distribution."""
        return self.domain[self.probs.index(max(self.probs))]


def binary_noise(name: str, p_true: float = 0.5) -> NoiseVar:
    """Convenience: a Bernoulli(p_true) noise variable over {0, 1}."""
    return NoiseVar(name, [0, 1], [1 - p_true, p_true])


def uniform_noise(name: str, domain: list[Any]) -> NoiseVar:
    """Convenience: a uniform noise variable over *domain*."""
    n = len(domain)
    return NoiseVar(name, domain, [1.0 / n] * n)


# ---------------------------------------------------------------------------
# SCM variable
# ---------------------------------------------------------------------------

@dataclass
class SCMVariable:
    """
    One endogenous variable in the SCM.

    name        : matches the node name in the CausalGraph
    parents     : ordered list of parent node names (determines arg order to equation)
    equation    : f(parent_values: dict[str, Any], noise: Any) -> Any
                  Must be a pure function (no side effects, deterministic given inputs).
    noise       : the exogenous NoiseVar for this variable
    domain      : all possible output values (used for abduction enumeration)
    """
    name: str
    parents: list[str]
    equation: Callable[[dict[str, Any], Any], Any]
    noise: NoiseVar
    domain: list[Any] = field(default_factory=lambda: [0, 1])


# ---------------------------------------------------------------------------
# Reasoning steps for the abduction trace
# ---------------------------------------------------------------------------

@dataclass
class SCMStep:
    """One step in an SCM reasoning trace."""
    kind: str      # "sample", "intervene", "abduct", "predict", "counterfactual"
    node: str
    detail: str    # human-readable sentence
    value: Any = None


# ---------------------------------------------------------------------------
# SCM
# ---------------------------------------------------------------------------

class SCM:
    """
    Structural Causal Model.

    Parameters
    ----------
    graph     : CausalGraph shared with the CBN layer
    variables : dict mapping node name → SCMVariable
    """

    def __init__(
        self,
        graph: CausalGraph,
        variables: dict[str, SCMVariable],
    ) -> None:
        self.graph = graph
        self.variables = variables

        # Validate that every graph node has a variable and vice-versa
        missing = graph.nodes - set(variables)
        extra   = set(variables) - graph.nodes
        if missing:
            raise ValueError(f"SCM missing variables for nodes: {sorted(missing)}")
        if extra:
            raise ValueError(f"SCM has variables not in graph: {sorted(extra)}")

    def _validate_keys(self, keys: Iterable[str], context: str) -> None:
        invalid = set(keys) - set(self.variables)
        if invalid:
            raise ValueError(f"{context} contains unknown variables: {sorted(invalid)}")

    # ------------------------------------------------------------------ #
    # Rung 1 / 2 — Sample (with optional do-interventions)
    # ------------------------------------------------------------------ #

    def sample(
        self,
        interventions: dict[str, Any] | None = None,
        *,
        noise_override: dict[str, Any] | None = None,
        trace: bool = False,
    ) -> dict[str, Any] | tuple[dict[str, Any], list[SCMStep]]:
        """
        Forward-sample all variables in topological order.

        interventions   : {node_name: forced_value} — do-operator
        noise_override  : {node_name: noise_value}  — fix exogenous noise (Rung 3)
        trace           : if True, return (values, steps) instead of just values

        Returns dict[node → sampled value], or (dict, list[SCMStep]) if trace=True.
        """
        do = interventions or {}
        noise_fix = noise_override or {}
        self._validate_keys(do, "interventions")
        self._validate_keys(noise_fix, "noise_override")
        values: dict[str, Any] = {}
        steps: list[SCMStep] = []

        for node in self.graph.topological_sort():
            var = self.variables[node]

            if node in do:
                values[node] = do[node]
                if trace:
                    steps.append(SCMStep(
                        kind="intervene", node=node,
                        detail=f"do({node} = {do[node]}) — intervention overrides equation",
                        value=do[node],
                    ))
                continue

            # Sample or retrieve noise
            u_val = noise_fix[node] if node in noise_fix else var.noise.sample()

            # Evaluate structural equation
            parent_vals = {p: values[p] for p in var.parents}
            result = var.equation(parent_vals, u_val)
            values[node] = result

            if trace:
                parent_str = ", ".join(f"{p}={values[p]}" for p in var.parents)
                steps.append(SCMStep(
                    kind="sample", node=node,
                    detail=(f"{node} = f({parent_str or '∅'}, U={u_val}) = {result}  "
                            f"[structural equation]"),
                    value=result,
                ))

        return (values, steps) if trace else values

    # ------------------------------------------------------------------ #
    # Rung 3 step 1 — Abduction
    # ------------------------------------------------------------------ #

    def abduction(
        self,
        observations: dict[str, Any],
    ) -> list[tuple[dict[str, Any], list[SCMStep]]]:
        """
        Infer all noise assignments consistent with *observations*.

        This implements Rung-3 abduction by exhaustive enumeration over the
        Cartesian product of all noise domains.  Works correctly for small
        discrete models; large models should use variational / MCMC methods.

        Returns a list of (noise_dict, trace_steps) for every consistent
        noise assignment.  Returns an empty list if observations are
        inconsistent with the model.
        """
        topo = self.graph.topological_sort()
        self._validate_keys(observations, "observations")
        noise_vars = [self.variables[n].noise for n in topo]

        consistent: list[tuple[dict[str, Any], list[SCMStep]]] = []

        # Enumerate all combinations of noise values
        for noise_combo in itertools.product(*[v.domain for v in noise_vars]):
            noise_dict = {topo[i]: noise_combo[i] for i in range(len(topo))}

            # Forward-evaluate with this noise assignment
            values: dict[str, Any] = {}
            abduct_steps: list[SCMStep] = []
            contradiction = False

            for node in topo:
                var = self.variables[node]
                u_val = noise_dict[node]
                parent_vals = {p: values[p] for p in var.parents}
                result = var.equation(parent_vals, u_val)
                values[node] = result

                # If this node is observed, check consistency
                if node in observations and values[node] != observations[node]:
                    contradiction = True
                    break

                parent_str = ", ".join(f"{p}={values[p]}" for p in var.parents)
                abduct_steps.append(SCMStep(
                    kind="abduct", node=node,
                    detail=(f"U_{node}={u_val}: {node} = f({parent_str or '∅'}, {u_val}) "
                            f"= {result}"
                            + (f"  ✓ matches obs" if node in observations else "")),
                    value=result,
                ))

            if not contradiction:
                consistent.append((noise_dict, abduct_steps))

        return consistent

    # ------------------------------------------------------------------ #
    # Rung 3 step 2 — Predict under intervention with fixed noise
    # ------------------------------------------------------------------ #

    def predict(
        self,
        noise: dict[str, Any],
        interventions: dict[str, Any] | None = None,
    ) -> tuple[dict[str, Any], list[SCMStep]]:
        """
        Replay the model with a fixed noise assignment and optional interventions.

        Used as Rung-3 step 2 after abduction has fixed the noise.
        Returns (values, steps).
        """
        self._validate_keys(noise, "noise")
        self._validate_keys(interventions or {}, "interventions")
        values, steps = self.sample(
            interventions=interventions,
            noise_override=noise,
            trace=True,
        )
        # Re-label steps for clarity
        for step in steps:
            if step.kind == "sample":
                step.kind = "predict"
        return values, steps

    # ------------------------------------------------------------------ #
    # Rung 3 full — Counterfactual
    # ------------------------------------------------------------------ #

    def counterfactual(
        self,
        observations: dict[str, Any],
        interventions: dict[str, Any],
        query_vars: list[str] | None = None,
    ) -> list[tuple[dict[str, Any], dict[str, Any], list[SCMStep]]]:
        """
        Twin-network counterfactual: "Given obs, what would query_vars be if do(interventions)?"

        Algorithm (Pearl's three-step):
          1. Abduction  : find all noise vectors U consistent with *observations*
          2. Intervention: apply do(*interventions*) to the model
          3. Prediction : forward-sample the intervened model with each U from step 1

        Returns a list of (noise, counterfactual_values, combined_steps) for each
        consistent noise assignment.  If all consistent assignments agree on the
        queried variable values, the counterfactual is identifiable.
        """
        results = []
        abducted = self.abduction(observations)

        for noise, abduct_steps in abducted:
            cf_values, predict_steps = self.predict(noise, interventions=interventions)
            all_steps = abduct_steps + [
                SCMStep(
                    kind="counterfactual",
                    node="—",
                    detail=f"Apply do({interventions}) with abducted noise",
                )
            ] + predict_steps
            results.append((noise, cf_values, all_steps))

        return results

    # ------------------------------------------------------------------ #
    # Probability / marginal helpers (Rung 1 — enumeration)
    # ------------------------------------------------------------------ #

    def marginal(
        self,
        query_node: str,
        interventions: dict[str, Any] | None = None,
    ) -> dict[Any, float]:
        """
        Exact marginal P(query_node) or P(query_node | do(interventions)) by
        enumerating all noise combinations.  Only feasible for small domains.
        """
        if query_node not in self.variables:
            raise ValueError(f"Unknown query node: {query_node}")
        do = interventions or {}
        self._validate_keys(do, "interventions")
        topo = self.graph.topological_sort()
        noise_vars = [self.variables[n].noise for n in topo]

        counts: dict[Any, float] = {}

        for noise_combo in itertools.product(*[v.domain for v in noise_vars]):
            # Compute joint probability of this noise assignment
            prob = 1.0
            for i, u_val in enumerate(noise_combo):
                nv = noise_vars[i]
                prob *= nv.probs[nv.domain.index(u_val)]

            noise_dict = {topo[i]: noise_combo[i] for i in range(len(topo))}
            values = self.sample(interventions=do, noise_override=noise_dict)
            q = values[query_node]
            counts[q] = counts.get(q, 0.0) + prob

        return counts

    def __repr__(self) -> str:
        return f"SCM(nodes={sorted(self.graph.nodes)})"


# ---------------------------------------------------------------------------
# Built-in demo model — Classic "Wet Grass" (Sprinkler / Rain)
# ---------------------------------------------------------------------------
#
#  Season ──→ Rain ──→ WetGrass
#     └──────→ Sprinkler ──→ WetGrass
#
# Season  ∈ {0=summer, 1=winter}   P(winter) = 0.4
# Rain    = 1  iff  (Season=winter AND U_Rain=1) OR U_Rain=2 (strong noise)
# Sprinkler = 1  iff  Season=summer AND U_Spr=0
# WetGrass  = Rain OR Sprinkler
# ---------------------------------------------------------------------------

def make_wet_grass_scm() -> SCM:
    """Build the classic Rain/Sprinkler/WetGrass SCM for demos."""

    # --- graph ---
    from cbn.graph import CausalGraph
    graph = CausalGraph(
        nodes=["Season", "Rain", "Sprinkler", "WetGrass"],
        edges=[
            ("Season", "Rain"),
            ("Season", "Sprinkler"),
            ("Rain",   "WetGrass"),
            ("Sprinkler", "WetGrass"),
        ],
    )

    # --- variables ---

    # Season: 0=summer, 1=winter.  Exogenous — equation is identity on noise.
    def eq_season(_, u): return u
    noise_season = NoiseVar("U_Season", [0, 1], [0.6, 0.4])  # 60% summer

    # Rain: more likely in winter.
    # Structural: Rain = 1 if (Season=1 and U_Rain≥0.7) or (U_Rain≥0.95)
    # Represented discretely: U_Rain ∈ {0,1}; P(U=1|winter)=0.8, P(U=1|summer)=0.2
    # We encode as U_Rain being the actual outcome given parents via a lookup.
    # Simpler: use a 2-value noise where the equation table is:
    #   Rain = (Season == 1 and U==1) or (Season == 0 and U==1 and ... )
    # For a clean deterministic SCM demo we use:
    #   U_Rain ∈ {0,1},  P(U=1) = 0.5 (fair coin)
    #   Rain = Season AND U_Rain  (rains in winter only if coin says 1)
    #       OR (not Season AND U_Rain AND noise >= 0.9)  → simplify:
    #   Rain = 1 if (Season=1 and U_Rain=1) else 0
    def eq_rain(parents, u):
        return 1 if (parents["Season"] == 1 and u == 1) else 0
    noise_rain = NoiseVar("U_Rain", [0, 1], [0.2, 0.8])  # biased: usually 1 (so rain in winter)

    # Sprinkler: on in summer only, controlled by U_Sprinkler.
    #   Sprinkler = 1 if (Season=0 and U_Spr=1) else 0
    def eq_sprinkler(parents, u):
        return 1 if (parents["Season"] == 0 and u == 1) else 0
    noise_spr = NoiseVar("U_Spr", [0, 1], [0.3, 0.7])  # usually on

    # WetGrass: deterministic OR of Rain and Sprinkler.
    #   WetGrass = Rain OR Sprinkler  (noise has no effect — always 0)
    def eq_wet(parents, u):
        return 1 if (parents["Rain"] == 1 or parents["Sprinkler"] == 1) else 0
    noise_wet = NoiseVar("U_WetGrass", [0], [1.0])  # point mass — deterministic

    variables = {
        "Season":    SCMVariable("Season",    [],                      eq_season,    noise_season,    [0, 1]),
        "Rain":      SCMVariable("Rain",      ["Season"],              eq_rain,      noise_rain,      [0, 1]),
        "Sprinkler": SCMVariable("Sprinkler", ["Season"],              eq_sprinkler, noise_spr,       [0, 1]),
        "WetGrass":  SCMVariable("WetGrass",  ["Rain", "Sprinkler"],   eq_wet,       noise_wet,       [0, 1]),
    }

    return SCM(graph, variables)
