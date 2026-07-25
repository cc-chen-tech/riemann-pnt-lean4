#!/usr/bin/env python3
"""Periodic rational-frequency diagnostics for the finite-spectrum gap.

Requires NumPy. The floating-point output is diagnostic, not a proof.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from fractions import Fraction
from pathlib import Path
from typing import Sequence

import numpy as np

if __package__:
    from experiments.pnt.vk_edge_pi_over_two_search import (
        Spectrum,
        estimate_sup_norm,
    )
else:
    from vk_edge_pi_over_two_search import Spectrum, estimate_sup_norm


@dataclass(frozen=True)
class NormEnclosure:
    """A floating-point mesh enclosure, not an interval-arithmetic proof."""

    lower: float
    upper: float
    location: float
    period: float
    samples: int
    mesh_width: float
    derivative_bound: float


@dataclass(frozen=True)
class TwoTermCandidate:
    frequency: Fraction
    coefficient: complex
    enclosure: NormEnclosure


def _lcm(first: int, second: int) -> int:
    return abs(first * second) // math.gcd(first, second)


def rational_period(frequencies: Sequence[Fraction]) -> float:
    """Return a common period for positive rational frequencies."""

    if not frequencies:
        raise ValueError("at least one frequency is required")
    denominator_lcm = 1
    for frequency in frequencies:
        if frequency <= 0:
            raise ValueError("frequencies must be positive")
        denominator_lcm = _lcm(denominator_lcm, frequency.denominator)
    return 2.0 * math.pi * denominator_lcm


def derivative_bound(spectrum: Spectrum) -> float:
    """Triangle bound for the absolute derivative of `spectrum.value`."""

    return 2.0 * sum(
        frequency * abs(coefficient)
        for frequency, coefficient in zip(
            spectrum.frequencies, spectrum.coefficients
        )
    )


def mesh_enclosure(
    spectrum: Spectrum,
    *,
    period: float,
    samples: int,
) -> NormEnclosure:
    """Enclose the sup norm using a uniform mesh and a derivative bound.

    The upper endpoint uses

    `sup |F| <= sampled_max |F| + ||F'||_infinity * mesh_width / 2`.

    Floating-point evaluation means the returned object is diagnostic rather
    than a formal interval-arithmetic certificate.
    """

    estimate = estimate_sup_norm(
        spectrum,
        interval_start=0.0,
        interval_end=period,
        samples=samples,
    )
    bound = derivative_bound(spectrum)
    return NormEnclosure(
        lower=estimate.value,
        upper=estimate.value + bound * estimate.mesh_width / 2.0,
        location=estimate.location,
        period=period,
        samples=samples,
        mesh_width=estimate.mesh_width,
        derivative_bound=bound,
    )


def optimize_two_term_rational(
    frequency: Fraction,
    *,
    coefficient_radius: float,
    grid_steps: int,
    refinements: int,
    samples: int,
) -> TwoTermCandidate:
    """Coordinate-grid search for `2 Re(e^iy + a e^(i lambda y))`."""

    if frequency <= 0 or frequency == 1:
        raise ValueError("the second frequency must be positive and not one")
    if coefficient_radius <= 0.0:
        raise ValueError("coefficient_radius must be positive")
    if grid_steps < 3 or grid_steps % 2 == 0:
        raise ValueError("grid_steps must be an odd integer at least three")
    if refinements < 1:
        raise ValueError("refinements must be positive")
    if samples < 2:
        raise ValueError("samples must be at least two")

    period = rational_period((Fraction(1), frequency))
    y_values = np.linspace(0.0, period, samples, dtype=np.float64)
    base = 2.0 * np.cos(y_values)
    angle = float(frequency) * y_values
    real_direction = 2.0 * np.cos(angle)
    imag_direction = -2.0 * np.sin(angle)

    center = 0.0 + 0.0j
    radius = coefficient_radius
    best_norm = math.inf
    for _ in range(refinements):
        real_values = np.linspace(
            center.real - radius,
            center.real + radius,
            grid_steps,
            dtype=np.float64,
        )
        imag_values = np.linspace(
            center.imag - radius,
            center.imag + radius,
            grid_steps,
            dtype=np.float64,
        )
        for real_part in real_values:
            values = (
                base[np.newaxis, :]
                + real_part * real_direction[np.newaxis, :]
                + imag_values[:, np.newaxis] * imag_direction[np.newaxis, :]
            )
            norms = np.max(np.abs(values), axis=1)
            index = int(np.argmin(norms))
            candidate_norm = float(norms[index])
            if candidate_norm < best_norm:
                best_norm = candidate_norm
                center = complex(float(real_part), float(imag_values[index]))
        radius *= 2.0 / (grid_steps - 1)

    spectrum = Spectrum(
        (1.0, float(frequency)),
        (1.0 + 0.0j, center),
    )
    enclosure = mesh_enclosure(
        spectrum,
        period=period,
        samples=samples,
    )
    return TwoTermCandidate(
        frequency=frequency,
        coefficient=center,
        enclosure=enclosure,
    )


def _candidate_as_dict(candidate: TwoTermCandidate) -> dict[str, object]:
    return {
        "warning": (
            "floating-point mesh enclosure; not an interval-arithmetic proof"
        ),
        "frequency": {
            "numerator": candidate.frequency.numerator,
            "denominator": candidate.frequency.denominator,
        },
        "coefficient": [
            candidate.coefficient.real,
            candidate.coefficient.imag,
        ],
        "enclosure": asdict(candidate.enclosure),
        "baseline_pi_over_two": math.pi / 2.0,
        "sampled_gap": candidate.enclosure.lower - math.pi / 2.0,
    }


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--numerator", type=int, default=3)
    parser.add_argument("--denominator", type=int, default=1)
    parser.add_argument("--coefficient-radius", type=float, default=1.0)
    parser.add_argument("--grid-steps", type=int, default=33)
    parser.add_argument("--refinements", type=int, default=5)
    parser.add_argument("--samples", type=int, default=32769)
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(
            "experiments/pnt/output/vk_edge_pi_over_two_rational_scan.json"
        ),
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    candidate = optimize_two_term_rational(
        Fraction(args.numerator, args.denominator),
        coefficient_radius=args.coefficient_radius,
        grid_steps=args.grid_steps,
        refinements=args.refinements,
        samples=args.samples,
    )
    payload = _candidate_as_dict(candidate)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="ascii",
    )
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
