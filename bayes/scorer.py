from __future__ import annotations

from dataclasses import dataclass
from math import exp, log
from typing import Iterable, Mapping


Label = str


@dataclass(frozen=True)
class NaiveBayesModel:
    prior: dict[Label, float]
    cond: dict[str, dict[str, dict[Label, float]]]


class NaiveBayesScorer:
    def __init__(self, model: NaiveBayesModel, labels: Iterable[Label], alpha: float = 1.0) -> None:
        self.model = model
        self.labels = tuple(labels)
        self.alpha = float(alpha)

    def _prior_prob(self, label: Label) -> float:
        return self.model.prior.get(label, 1.0)

    def _cond_prob(self, feature: str, value: str, label: Label) -> float:
        feature_table = self.model.cond.get(feature, {})
        value_table = feature_table.get(value)
        if value_table is not None and label in value_table:
            return value_table[label]

        # Unseen value or missing feature: apply smoothing toward uniform
        # across observed values for this feature.
        label_mass = 0.0
        num_values = max(1, len(feature_table))
        for observed in feature_table.values():
            if label in observed:
                label_mass += observed[label]
        return (label_mass + self.alpha) / (num_values + self.alpha * num_values)

    def score(self, features: Mapping[str, str], positive_label: Label) -> float:
        log_probs: dict[Label, float] = {}
        for label in self.labels:
            prior = max(self._prior_prob(label), 1e-9)
            log_p = log(prior)
            for feature, value in features.items():
                prob = max(self._cond_prob(feature, value, label), 1e-9)
                log_p += log(prob)
            log_probs[label] = log_p

        # Softmax normalization
        max_log = max(log_probs.values())
        exp_sum = 0.0
        for value in log_probs.values():
            exp_sum += exp(value - max_log)
        positive_log = log_probs.get(positive_label, -1e9)
        return exp(positive_log - max_log) / max(exp_sum, 1e-9)


def _normalize_counts(counts: dict[Label, float]) -> dict[Label, float]:
    total = sum(counts.values())
    if total <= 0:
        return {label: 1.0 for label in counts}
    return {label: value / total for label, value in counts.items()}


def _normalize_cond(
    cond_counts: dict[str, dict[str, dict[Label, float]]]
) -> dict[str, dict[str, dict[Label, float]]]:
    normalized: dict[str, dict[str, dict[Label, float]]] = {}
    for feature, values in cond_counts.items():
        normalized[feature] = {}
        for value, label_counts in values.items():
            normalized[feature][value] = _normalize_counts(label_counts)
    return normalized


def _default_step_model() -> NaiveBayesModel:
    prior = _normalize_counts({"success": 1.0, "failure": 1.0})

    cond_counts = {
        "rule": {
            "modus_ponens": {"success": 6.0, "failure": 4.0},
            "and_intro": {"success": 4.0, "failure": 6.0},
            "and_elim_left": {"success": 5.0, "failure": 5.0},
            "and_elim_right": {"success": 5.0, "failure": 5.0},
        },
        "result_is_goal": {
            "True": {"success": 9.0, "failure": 1.0},
            "False": {"success": 2.0, "failure": 8.0},
        },
        "result_complexity": {
            "simple": {"success": 6.0, "failure": 4.0},
            "medium": {"success": 5.0, "failure": 5.0},
            "complex": {"success": 3.0, "failure": 7.0},
        },
        "result_type": {
            "Atom": {"success": 6.0, "failure": 4.0},
            "And": {"success": 5.0, "failure": 5.0},
            "Imp": {"success": 6.0, "failure": 4.0},
            "Not": {"success": 4.0, "failure": 6.0},
            "Other": {"success": 5.0, "failure": 5.0},
        },
        "support1_type": {
            "Atom": {"success": 6.0, "failure": 4.0},
            "And": {"success": 5.0, "failure": 5.0},
            "Imp": {"success": 7.0, "failure": 3.0},
            "Not": {"success": 4.0, "failure": 6.0},
            "None": {"success": 1.0, "failure": 9.0},
        },
        "support2_type": {
            "Atom": {"success": 6.0, "failure": 4.0},
            "And": {"success": 5.0, "failure": 5.0},
            "Imp": {"success": 7.0, "failure": 3.0},
            "Not": {"success": 4.0, "failure": 6.0},
            "None": {"success": 1.0, "failure": 9.0},
        },
        "available_count": {
            "small": {"success": 6.0, "failure": 4.0},
            "medium": {"success": 5.0, "failure": 5.0},
            "large": {"success": 4.0, "failure": 6.0},
        },
        "depth": {
            "shallow": {"success": 6.0, "failure": 4.0},
            "mid": {"success": 5.0, "failure": 5.0},
            "deep": {"success": 3.0, "failure": 7.0},
        },
    }
    return NaiveBayesModel(prior=prior, cond=_normalize_cond(cond_counts))


def _default_rule_model() -> NaiveBayesModel:
    prior = _normalize_counts({"success": 1.0, "failure": 1.0})
    cond_counts = {
        "rule": {
            "modus_ponens": {"success": 6.0, "failure": 4.0},
            "and_intro": {"success": 4.0, "failure": 6.0},
            "and_elim_left": {"success": 5.0, "failure": 5.0},
            "and_elim_right": {"success": 5.0, "failure": 5.0},
        },
        "goal_type": {
            "Atom": {"success": 6.0, "failure": 4.0},
            "And": {"success": 5.0, "failure": 5.0},
            "Imp": {"success": 5.0, "failure": 5.0},
            "Not": {"success": 4.0, "failure": 6.0},
            "Other": {"success": 5.0, "failure": 5.0},
        },
        "available_count": {
            "small": {"success": 5.0, "failure": 5.0},
            "medium": {"success": 5.0, "failure": 5.0},
            "large": {"success": 4.0, "failure": 6.0},
        },
        "depth": {
            "shallow": {"success": 6.0, "failure": 4.0},
            "mid": {"success": 5.0, "failure": 5.0},
            "deep": {"success": 4.0, "failure": 6.0},
        },
    }
    return NaiveBayesModel(prior=prior, cond=_normalize_cond(cond_counts))


def _default_formula_model() -> NaiveBayesModel:
    prior = _normalize_counts({"useful": 1.0, "not_useful": 1.0})
    cond_counts = {
        "formula_type": {
            "Atom": {"useful": 6.0, "not_useful": 4.0},
            "And": {"useful": 5.0, "not_useful": 5.0},
            "Imp": {"useful": 6.0, "not_useful": 4.0},
            "Not": {"useful": 4.0, "not_useful": 6.0},
            "Other": {"useful": 5.0, "not_useful": 5.0},
        },
        "complexity_bucket": {
            "simple": {"useful": 6.0, "not_useful": 4.0},
            "medium": {"useful": 5.0, "not_useful": 5.0},
            "complex": {"useful": 3.0, "not_useful": 7.0},
        },
        "is_goal": {
            "True": {"useful": 9.0, "not_useful": 1.0},
            "False": {"useful": 4.0, "not_useful": 6.0},
        },
        "is_assumption": {
            "True": {"useful": 8.0, "not_useful": 2.0},
            "False": {"useful": 4.0, "not_useful": 6.0},
        },
    }
    return NaiveBayesModel(prior=prior, cond=_normalize_cond(cond_counts))


def _default_partial_model() -> NaiveBayesModel:
    prior = _normalize_counts({"success": 1.0, "failure": 1.0})
    cond_counts = {
        "goal_type": {
            "Atom": {"success": 6.0, "failure": 4.0},
            "And": {"success": 5.0, "failure": 5.0},
            "Imp": {"success": 5.0, "failure": 5.0},
            "Not": {"success": 4.0, "failure": 6.0},
            "Other": {"success": 5.0, "failure": 5.0},
        },
        "available_count": {
            "small": {"success": 6.0, "failure": 4.0},
            "medium": {"success": 5.0, "failure": 5.0},
            "large": {"success": 4.0, "failure": 6.0},
        },
        "depth": {
            "shallow": {"success": 6.0, "failure": 4.0},
            "mid": {"success": 5.0, "failure": 5.0},
            "deep": {"success": 3.0, "failure": 7.0},
        },
        "remaining_steps": {
            "low": {"success": 4.0, "failure": 6.0},
            "medium": {"success": 5.0, "failure": 5.0},
            "high": {"success": 6.0, "failure": 4.0},
        },
        "goal_in_available": {
            "True": {"success": 9.0, "failure": 1.0},
            "False": {"success": 3.0, "failure": 7.0},
        },
    }
    return NaiveBayesModel(prior=prior, cond=_normalize_cond(cond_counts))


def default_step_scorer() -> NaiveBayesScorer:
    model = _default_step_model()
    return NaiveBayesScorer(model, labels=("success", "failure"))


def default_rule_scorer() -> NaiveBayesScorer:
    model = _default_rule_model()
    return NaiveBayesScorer(model, labels=("success", "failure"))


def default_formula_scorer() -> NaiveBayesScorer:
    model = _default_formula_model()
    return NaiveBayesScorer(model, labels=("useful", "not_useful"))


def default_partial_scorer() -> NaiveBayesScorer:
    model = _default_partial_model()
    return NaiveBayesScorer(model, labels=("success", "failure"))
