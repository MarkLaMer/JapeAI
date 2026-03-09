from __future__ import annotations

from collections import defaultdict
from typing import Iterable, Mapping, Sequence

from bayes.scorer import NaiveBayesModel, _normalize_cond, _normalize_counts


Example = tuple[Mapping[str, str], str]


def train_naive_bayes(
    examples: Sequence[Example],
    *,
    labels: Iterable[str],
) -> NaiveBayesModel:
    """
    Train a naive Bayes model from (features, label) examples.

    This is intentionally lightweight so CSP runs can emit traces
    and update the model without external dependencies.
    """
    label_set = set(labels)
    prior_counts: dict[str, float] = {label: 0.0 for label in label_set}
    cond_counts: dict[str, dict[str, dict[str, float]]] = defaultdict(
        lambda: defaultdict(lambda: {label: 0.0 for label in label_set})
    )

    for features, label in examples:
        if label not in label_set:
            continue
        prior_counts[label] += 1.0
        for feature, value in features.items():
            cond_counts[feature][value][label] += 1.0

    prior = _normalize_counts(prior_counts)
    cond = _normalize_cond(cond_counts)
    return NaiveBayesModel(prior=prior, cond=cond)
