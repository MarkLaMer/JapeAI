"""
Naive Bayes scorer for the standalone Bayesian proof solver.

Only the step model is kept here — the formula-domain scorer, rule scorer,
and partial-state scorer that used to live here were solely for the CSP's
Bayes reordering layer, which has been removed in favour of a standalone
Bayesian solver (bayes/solver.py).
"""

from __future__ import annotations

from dataclasses import dataclass
from math import exp, log
from typing import Iterable, Mapping


Label = str


# ──────────────────────────────────────────────────────────────────────────────
# Core Naive Bayes machinery
# ──────────────────────────────────────────────────────────────────────────────

@dataclass(frozen=True)
class NaiveBayesModel:
    prior: dict[Label, float]
    cond:  dict[str, dict[str, dict[Label, float]]]


class NaiveBayesScorer:
    def __init__(
        self,
        model: NaiveBayesModel,
        labels: Iterable[Label],
        alpha: float = 1.0,
    ) -> None:
        self.model  = model
        self.labels = tuple(labels)
        self.alpha  = float(alpha)

    def _prior_prob(self, label: Label) -> float:
        return self.model.prior.get(label, 1.0)

    def _cond_prob(self, feature: str, value: str, label: Label) -> float:
        feature_table = self.model.cond.get(feature, {})
        value_table   = feature_table.get(value)
        if value_table is not None and label in value_table:
            return value_table[label]
        # Unseen value: Laplace smoothing toward observed mean.
        label_mass = 0.0
        num_values = max(1, len(feature_table))
        for observed in feature_table.values():
            if label in observed:
                label_mass += observed[label]
        return (label_mass + self.alpha) / (num_values + self.alpha * num_values)

    def score(
        self, features: Mapping[str, str], positive_label: Label
    ) -> float:
        """Return P(positive_label | features) via log-space softmax."""
        log_probs: dict[Label, float] = {}
        for label in self.labels:
            log_p = log(max(self._prior_prob(label), 1e-9))
            for feature, value in features.items():
                log_p += log(max(self._cond_prob(feature, value, label), 1e-9))
            log_probs[label] = log_p

        max_log  = max(log_probs.values())
        exp_sum  = sum(exp(v - max_log) for v in log_probs.values())
        pos_log  = log_probs.get(positive_label, -1e9)
        return exp(pos_log - max_log) / max(exp_sum, 1e-9)


# ──────────────────────────────────────────────────────────────────────────────
# Helpers
# ──────────────────────────────────────────────────────────────────────────────

def _normalize_counts(counts: dict[Label, float]) -> dict[Label, float]:
    total = sum(counts.values())
    if total <= 0:
        return {label: 1.0 for label in counts}
    return {label: v / total for label, v in counts.items()}


def _normalize_cond(
    cond_counts: dict[str, dict[str, dict[Label, float]]]
) -> dict[str, dict[str, dict[Label, float]]]:
    return {
        feature: {
            value: _normalize_counts(label_counts)
            for value, label_counts in values.items()
        }
        for feature, values in cond_counts.items()
    }


# ──────────────────────────────────────────────────────────────────────────────
# Step model — the only model used by bayes/solver.py
# ──────────────────────────────────────────────────────────────────────────────

def _default_step_model() -> NaiveBayesModel:
    prior = _normalize_counts({"success": 1.0, "failure": 1.0})

    cond_counts: dict[str, dict[str, dict[str, float]]] = {
        # ── rule ─────────────────────────────────────────────────────────
        "rule": {
            # MP is the workhorse of implication chains.
            "modus_ponens":             {"success": 7.0, "failure": 3.0},
            "and_intro":                {"success": 4.0, "failure": 6.0},
            "and_elim_left":            {"success": 5.0, "failure": 5.0},
            "and_elim_right":           {"success": 5.0, "failure": 5.0},
            # Universal instantiation: when applicable, almost certainly on-path.
            "universal_instantiation":  {"success": 8.0, "failure": 2.0},
            # Existential intro: usually a late/final step.
            "existential_intro":        {"success": 6.0, "failure": 4.0},
        },

        # ── does this step derive the goal? ───────────────────────────────
        "result_is_goal": {
            "True":  {"success": 18.0, "failure": 2.0},
            "False": {"success": 2.0,  "failure": 8.0},
        },

        # ── structural type of the derived formula ────────────────────────
        "result_type": {
            "Atom":      {"success": 6.0, "failure": 4.0},
            "And":       {"success": 5.0, "failure": 5.0},
            "Imp":       {"success": 6.0, "failure": 4.0},
            "Not":       {"success": 4.0, "failure": 6.0},
            "Predicate": {"success": 6.0, "failure": 4.0},
            "ForAll":    {"success": 5.0, "failure": 5.0},
            "Exists":    {"success": 5.0, "failure": 5.0},
            "Other":     {"success": 5.0, "failure": 5.0},
        },

        "result_complexity": {
            "simple":  {"success": 6.0, "failure": 4.0},
            "medium":  {"success": 5.0, "failure": 5.0},
            "complex": {"success": 3.0, "failure": 7.0},
        },

        # ── support types ─────────────────────────────────────────────────
        "support1_type": {
            "Atom":      {"success": 6.0, "failure": 4.0},
            "And":       {"success": 5.0, "failure": 5.0},
            "Imp":       {"success": 8.0, "failure": 2.0},
            "Not":       {"success": 4.0, "failure": 6.0},
            "Predicate": {"success": 6.0, "failure": 4.0},
            "ForAll":    {"success": 8.0, "failure": 2.0},  # UI fires from ForAll
            "Exists":    {"success": 5.0, "failure": 5.0},
            "None":      {"success": 1.0, "failure": 9.0},
        },
        "support2_type": {
            "Atom":      {"success": 6.0, "failure": 4.0},
            "And":       {"success": 5.0, "failure": 5.0},
            "Imp":       {"success": 8.0, "failure": 2.0},
            "Not":       {"success": 4.0, "failure": 6.0},
            "Predicate": {"success": 6.0, "failure": 4.0},
            "ForAll":    {"success": 5.0, "failure": 5.0},
            "Exists":    {"success": 5.0, "failure": 5.0},
            "None":      {"success": 5.0, "failure": 5.0},  # single-support rules fine
        },

        "available_count": {
            "small":  {"success": 6.0, "failure": 4.0},
            "medium": {"success": 5.0, "failure": 5.0},
            "large":  {"success": 4.0, "failure": 6.0},
        },
        "depth": {
            "shallow": {"success": 6.0, "failure": 4.0},
            "mid":     {"success": 5.0, "failure": 5.0},
            "deep":    {"success": 3.0, "failure": 7.0},
        },

        # ── goal-directed structural features ────────────────────────────
        "subformula_overlap": {
            "full":    {"success": 18.0, "failure": 2.0},
            "partial": {"success": 7.0,  "failure": 3.0},
            "none":    {"success": 2.0,  "failure": 8.0},
        },
        "is_subformula_of_goal": {
            "True":  {"success": 8.0, "failure": 2.0},
            "False": {"success": 4.0, "failure": 6.0},
        },
        "leads_to_goal": {
            "direct":  {"success": 16.0, "failure": 4.0},
            "one_hop": {"success": 8.0,  "failure": 2.0},
            "False":   {"success": 3.0,  "failure": 7.0},
        },

        # ── quantifier-awareness features ─────────────────────────────────
        # When both result and goal involve quantifiers the step is likely
        # on the right path (UI / EI are targeted moves).
        "result_has_quantifier": {
            "True":  {"success": 5.0, "failure": 5.0},
            "False": {"success": 5.0, "failure": 5.0},
        },
        "goal_has_quantifier": {
            # If goal involves a quantifier, EI steps are important.
            "True":  {"success": 6.0, "failure": 4.0},
            "False": {"success": 5.0, "failure": 5.0},
        },
    }

    return NaiveBayesModel(prior=prior, cond=_normalize_cond(cond_counts))


def default_step_scorer() -> NaiveBayesScorer:
    return NaiveBayesScorer(_default_step_model(), labels=("success", "failure"))
