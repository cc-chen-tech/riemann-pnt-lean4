#!/usr/bin/env python3
"""Deterministic diagnostics for the VK-edge finite-spectrum gap.

Every reported norm is a sampled lower estimate for the true global sup norm.
The program is a falsification and conjecture-generation tool, not a proof.
"""

from __future__ import annotations

import argparse
import cmath
import json
import math
import random
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable, Sequence, Tuple


ComplexTuple = Tuple[complex, ...]
RealTuple = Tuple[float, ...]


@dataclass(frozen=True)
class Spectrum:
    """Positive-frequency representation of a real exponential polynomial."""

    frequencies: RealTuple
    coefficients: ComplexTuple

    def __post_init__(self) -> None:
        if len(self.frequencies) != len(self.coefficients):
            raise ValueError("frequencies and coefficients must have equal length")
        if not self.frequencies:
            raise ValueError("a spectrum must contain at least one frequency")
        if any(not math.isfinite(frequency) or frequency <= 0.0
               for frequency in self.frequencies):
            raise ValueError("frequencies must be finite and positive")
        if any(not math.isfinite(coefficient.real)
               or not math.isfinite(coefficient.imag)
               for coefficient in self.coefficients):
            raise ValueError("coefficients must be finite")

    def combined(self) -> "Spectrum":
        """Combine exactly equal frequencies and remove zero coefficients."""

        totals: dict[float, complex] = {}
        for frequency, coefficient in zip(self.frequencies, self.coefficients):
            totals[frequency] = totals.get(frequency, 0.0j) + coefficient
        nonzero = [
            (frequency, coefficient)
            for frequency, coefficient in sorted(totals.items())
            if coefficient != 0.0j
        ]
        if not nonzero:
            raise ValueError("combining equal frequencies removed every term")
        return Spectrum(
            tuple(frequency for frequency, _ in nonzero),
            tuple(coefficient for _, coefficient in nonzero),
        )

    def value(self, y: float) -> float:
        total = sum(
            coefficient * cmath.exp(1.0j * frequency * y)
            for frequency, coefficient in zip(
                self.frequencies, self.coefficients
            )
        )
        return 2.0 * total.real


@dataclass(frozen=True)
class SupNormEstimate:
    value: float
    location: float
    interval_start: float
    interval_end: float
    samples: int
    mesh_width: float


@dataclass(frozen=True)
class SearchResult:
    spectrum: Spectrum
    estimate: SupNormEstimate
    seed: int
    trials: int
    max_terms: int


def finite_spectrum_kappa_lower_bound(max_terms: int) -> float:
    """Explicit strict lower bound obtained from a missing odd harmonic.

    For a spectrum with at most `M` positive characters, one of
    `chi, chi^3, ..., chi^(2M+1)` is absent. The corresponding coefficient of
    `sign(Re chi)` has magnitude at least `2 / (pi (2M+1))`. Splitting the
    equality defect for the classical coefficient inequality at
    `|Re chi| = sin(1 / (4(2M+1)))` gives the returned bound.
    """

    if max_terms < 1:
        raise ValueError("max_terms must be positive")
    odd_harmonic_bound = 2.0 * max_terms + 1.0
    missing_coefficient = 2.0 / (math.pi * odd_harmonic_bound)
    defect = (
        missing_coefficient
        * math.sin(1.0 / (4.0 * odd_harmonic_bound))
        / 2.0
    )
    return 1.0 / (2.0 / math.pi - defect)


def normalized_spectrum(
    spectrum: Spectrum,
    distinguished_frequency: float,
) -> tuple[Spectrum, float, float]:
    """Normalize the distinguished frequency and coefficient to one.

    Returns `(normalized, shift, scale)`, where

    `normalized.value(z) = spectrum.value(z / distinguished_frequency + shift)
      / scale`.
    """

    combined = spectrum.combined()
    try:
        distinguished_index = combined.frequencies.index(distinguished_frequency)
    except ValueError as error:
        if distinguished_frequency in spectrum.frequencies:
            raise ValueError(
                "combined distinguished coefficient must be nonzero"
            ) from error
        raise ValueError("distinguished frequency is absent") from error
    distinguished = combined.coefficients[distinguished_index]
    if distinguished == 0.0j:
        raise ValueError("distinguished coefficient must be nonzero")

    scale = abs(distinguished)
    shift = -cmath.phase(distinguished) / distinguished_frequency
    normalized_terms = []
    for frequency, coefficient in zip(
        combined.frequencies, combined.coefficients
    ):
        normalized_terms.append(
            (
                frequency / distinguished_frequency,
                coefficient
                * cmath.exp(1.0j * frequency * shift)
                / scale,
            )
        )

    distinguished_term = normalized_terms.pop(distinguished_index)
    normalized_terms.sort(key=lambda term: term[0])
    ordered = [distinguished_term] + normalized_terms
    normalized = Spectrum(
        tuple(frequency for frequency, _ in ordered),
        tuple(coefficient for _, coefficient in ordered),
    )
    return normalized, shift, scale


def estimate_sup_norm(
    spectrum: Spectrum,
    *,
    interval_start: float,
    interval_end: float,
    samples: int,
) -> SupNormEstimate:
    """Return the largest sampled absolute value on a closed interval."""

    if not interval_start < interval_end:
        raise ValueError("interval_start must be smaller than interval_end")
    if samples < 2:
        raise ValueError("samples must be at least two")
    mesh_width = (interval_end - interval_start) / (samples - 1)
    best_value = -1.0
    best_location = interval_start
    for index in range(samples):
        location = interval_start + index * mesh_width
        value = abs(spectrum.value(location))
        if value > best_value:
            best_value = value
            best_location = location
    return SupNormEstimate(
        value=best_value,
        location=best_location,
        interval_start=interval_start,
        interval_end=interval_end,
        samples=samples,
        mesh_width=mesh_width,
    )


def sign_cos_truncation(positive_terms: int) -> Spectrum:
    """Truncate `(pi / 2) sign(cos y)` at positive odd frequencies."""

    if positive_terms < 1:
        raise ValueError("positive_terms must be at least one")
    return Spectrum(
        tuple(float(2 * index + 1) for index in range(positive_terms)),
        tuple(
            complex(((-1.0) ** index) / (2 * index + 1), 0.0)
            for index in range(positive_terms)
        ),
    )


def fejer_sign_cos_normalized(positive_terms: int) -> Spectrum:
    """Normalized Fejer mean showing that no gap is uniform in term count."""

    if positive_terms < 1:
        raise ValueError("positive_terms must be at least one")
    denominator = 2 * positive_terms - 1
    frequencies = tuple(
        float(2 * index + 1) for index in range(positive_terms)
    )
    coefficients = []
    for index, frequency in enumerate(range(1, 2 * positive_terms, 2)):
        coefficient = (
            ((-1.0) ** index)
            * (2 * positive_terms - frequency)
            / (denominator * frequency)
        )
        coefficients.append(complex(coefficient, 0.0))
    return Spectrum(frequencies, tuple(coefficients))


def _random_spectrum(rng: random.Random, terms: int) -> Spectrum:
    frequencies = [1.0]
    while len(frequencies) < terms:
        candidate = rng.uniform(1.25, 9.0)
        if all(abs(candidate - existing) >= 0.05 for existing in frequencies):
            frequencies.append(candidate)
    coefficients = [1.0 + 0.0j]
    for _ in range(1, terms):
        magnitude = rng.uniform(0.0, 1.25)
        phase = rng.uniform(-math.pi, math.pi)
        coefficients.append(magnitude * cmath.exp(1.0j * phase))
    return Spectrum(tuple(frequencies), tuple(coefficients))


def deterministic_search(
    *,
    max_terms: int,
    trials: int,
    seed: int,
    interval_end: float,
    samples: int,
) -> SearchResult:
    """Search deterministic candidate families for a small sampled norm."""

    if max_terms < 1:
        raise ValueError("max_terms must be at least one")
    if trials < 0:
        raise ValueError("trials must be nonnegative")
    rng = random.Random(seed)
    candidates = []
    for terms in range(1, max_terms + 1):
        candidates.append(sign_cos_truncation(terms))
        candidates.append(fejer_sign_cos_normalized(terms))
    for _ in range(trials):
        terms = rng.randint(1, max_terms)
        candidates.append(_random_spectrum(rng, terms))

    best_spectrum = candidates[0]
    best_estimate = estimate_sup_norm(
        best_spectrum,
        interval_start=0.0,
        interval_end=interval_end,
        samples=samples,
    )
    for spectrum in candidates[1:]:
        estimate = estimate_sup_norm(
            spectrum,
            interval_start=0.0,
            interval_end=interval_end,
            samples=samples,
        )
        if estimate.value < best_estimate.value:
            best_spectrum = spectrum
            best_estimate = estimate
    return SearchResult(
        spectrum=best_spectrum,
        estimate=best_estimate,
        seed=seed,
        trials=trials,
        max_terms=max_terms,
    )


def _complex_pairs(values: Iterable[complex]) -> list[list[float]]:
    return [[value.real, value.imag] for value in values]


def result_as_json(result: SearchResult) -> dict[str, object]:
    return {
        "warning": (
            "sampled finite-interval lower estimate; not a global norm "
            "certificate or mathematical proof"
        ),
        "baseline_pi_over_two": math.pi / 2.0,
        "analytic_kappa_lower_bound": finite_spectrum_kappa_lower_bound(
            result.max_terms
        ),
        "sampled_gap": result.estimate.value - math.pi / 2.0,
        "frequencies": list(result.spectrum.frequencies),
        "coefficients": _complex_pairs(result.spectrum.coefficients),
        "estimate": asdict(result.estimate),
        "seed": result.seed,
        "trials": result.trials,
        "max_terms": result.max_terms,
    }


def write_json_report(result: SearchResult, output: Path) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(
        json.dumps(result_as_json(result), indent=2, sort_keys=True) + "\n",
        encoding="ascii",
    )


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-terms", type=int, default=6)
    parser.add_argument("--trials", type=int, default=256)
    parser.add_argument("--seed", type=int, default=20260724)
    parser.add_argument("--interval-end", type=float, default=512.0)
    parser.add_argument("--samples", type=int, default=131073)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("experiments/pnt/output/vk_edge_pi_over_two_search.json"),
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    result = deterministic_search(
        max_terms=args.max_terms,
        trials=args.trials,
        seed=args.seed,
        interval_end=args.interval_end,
        samples=args.samples,
    )
    write_json_report(result, args.output)
    print(json.dumps(result_as_json(result), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
