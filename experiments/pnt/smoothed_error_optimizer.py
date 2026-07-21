from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from decimal import (
    Decimal,
    Context,
    InvalidOperation,
    ROUND_CEILING,
    ROUND_FLOOR,
    localcontext,
)
from fractions import Fraction
from typing import Iterable, Sequence


DEFAULT_PRECISION = 80
SUPPORTED_MODELS = {"finite_height", "rh", "classical_zero_free"}


def _context(precision: int, rounding: str) -> Context:
    if precision < 20:
        raise ValueError("precision must be at least 20 decimal digits")
    return Context(prec=precision, rounding=rounding, Emin=-999999, Emax=999999)


@dataclass(frozen=True)
class Interval:
    lower: Decimal
    upper: Decimal

    def __post_init__(self) -> None:
        if not self.lower.is_finite() or not self.upper.is_finite():
            raise ValueError("interval endpoints must be finite")
        if self.upper < self.lower:
            raise ValueError("interval endpoints are reversed")

    def as_dict(self) -> dict[str, str]:
        return {"lower": str(self.lower), "upper": str(self.upper)}


@dataclass(frozen=True)
class ApproximationDifference:
    h: int
    interval: Interval

    def __post_init__(self) -> None:
        if self.h <= 0:
            raise ValueError("approximation-difference h values must be positive")

    def as_dict(self) -> dict[str, object]:
        return {"h": self.h, **self.interval.as_dict()}


@dataclass(frozen=True)
class ApproximationDifferences:
    mode: str
    differences: tuple[ApproximationDifference, ...] = ()

    def __post_init__(self) -> None:
        if self.mode not in {"identity", "certified_intervals"}:
            raise ValueError(f"unsupported approximation mode: {self.mode}")
        if self.mode == "identity" and self.differences:
            raise ValueError("identity approximation does not accept interval overrides")
        if self.mode == "certified_intervals" and not self.differences:
            raise ValueError("certified approximation requires at least one interval")

    @classmethod
    def identity(cls) -> ApproximationDifferences:
        return cls(mode="identity")

    @classmethod
    def certified(
        cls,
        differences: Iterable[
            ApproximationDifference | tuple[int, Interval]
        ],
    ) -> ApproximationDifferences:
        normalized = []
        seen = set()
        for item in differences:
            difference = (
                item
                if isinstance(item, ApproximationDifference)
                else ApproximationDifference(*item)
            )
            if difference.h in seen:
                raise ValueError(f"duplicate h value: {difference.h}")
            seen.add(difference.h)
            normalized.append(difference)
        normalized.sort(key=lambda item: item.h)
        return cls(mode="certified_intervals", differences=tuple(normalized))

    def validate_h_values(self, h_values: Iterable[int]) -> None:
        if self.mode == "identity":
            return
        requested = set(h_values)
        available = {item.h for item in self.differences}
        missing = sorted(requested - available)
        unused = sorted(available - requested)
        if missing:
            raise ValueError(
                "certified approximation is missing h values: "
                + ", ".join(str(h) for h in missing)
            )
        if unused:
            raise ValueError(
                "certified approximation has unused h values: "
                + ", ".join(str(h) for h in unused)
            )

    def interval_for(self, h: int) -> Interval:
        if self.mode == "identity":
            value = Decimal(h)
            return Interval(value, value)
        for item in self.differences:
            if item.h == h:
                return item.interval
        raise ValueError(f"certified approximation is missing h value: {h}")

    def as_dict(self, h_values: Iterable[int]) -> dict[str, object]:
        values = tuple(h_values)
        self.validate_h_values(values)
        return {
            "mode": self.mode,
            "quantity": "Re(A_T(x+h)-A_T(x))",
            "real_difference_intervals": [
                {"h": h, **self.interval_for(h).as_dict()} for h in values
            ],
        }


def _fraction_interval(value: Fraction, precision: int) -> Interval:
    numerator = Decimal(value.numerator)
    denominator = Decimal(value.denominator)
    with localcontext(_context(precision, ROUND_FLOOR)):
        lower = numerator / denominator
    with localcontext(_context(precision, ROUND_CEILING)):
        upper = numerator / denominator
    return Interval(lower, upper)


def _add(left: Interval, right: Interval, precision: int) -> Interval:
    with localcontext(_context(precision, ROUND_FLOOR)):
        lower = left.lower + right.lower
    with localcontext(_context(precision, ROUND_CEILING)):
        upper = left.upper + right.upper
    return Interval(lower, upper)


def _multiply(left: Interval, right: Interval, precision: int) -> Interval:
    with localcontext(_context(precision, ROUND_FLOOR)):
        lower = min(
            left.lower * right.lower,
            left.lower * right.upper,
            left.upper * right.lower,
            left.upper * right.upper,
        )
    with localcontext(_context(precision, ROUND_CEILING)):
        upper = max(
            left.lower * right.lower,
            left.lower * right.upper,
            left.upper * right.lower,
            left.upper * right.upper,
        )
    return Interval(lower, upper)


def _multiply_nonnegative(left: Interval, right: Interval, precision: int) -> Interval:
    if left.lower < 0 or right.lower < 0:
        raise ValueError("nonnegative interval multiplication received a negative endpoint")
    return _multiply(left, right, precision)


def _divide_by_positive(left: Interval, right: Interval, precision: int) -> Interval:
    if right.lower <= 0:
        raise ValueError("interval division requires a positive denominator")
    with localcontext(_context(precision, ROUND_FLOOR)):
        reciprocal_lower = Decimal(1) / right.upper
    with localcontext(_context(precision, ROUND_CEILING)):
        reciprocal_upper = Decimal(1) / right.lower
    return _multiply(
        left, Interval(reciprocal_lower, reciprocal_upper), precision
    )


def _log_positive(value: Interval, precision: int) -> Interval:
    if value.lower <= 0:
        raise ValueError("logarithm input must be positive")
    with localcontext(_context(precision, ROUND_FLOOR)) as context:
        lower = context.next_minus(value.lower.ln())
    with localcontext(_context(precision, ROUND_CEILING)) as context:
        upper = context.next_plus(value.upper.ln())
    return Interval(lower, upper)


def _sqrt_nonnegative(value: Interval, precision: int) -> Interval:
    if value.lower < 0:
        raise ValueError("square-root input must be nonnegative")
    with localcontext(_context(precision, ROUND_FLOOR)) as context:
        lower = context.next_minus(value.lower.sqrt())
    with localcontext(_context(precision, ROUND_CEILING)) as context:
        upper = context.next_plus(value.upper.sqrt())
    return Interval(lower, upper)


def _exp(value: Interval, precision: int) -> Interval:
    with localcontext(_context(precision, ROUND_FLOOR)) as context:
        lower = context.next_minus(value.lower.exp())
    with localcontext(_context(precision, ROUND_CEILING)) as context:
        upper = context.next_plus(value.upper.exp())
    return Interval(lower, upper)


def certified_log1p(ratio: Fraction, precision: int = DEFAULT_PRECISION) -> Interval:
    if ratio <= 0:
        raise ValueError("ratio must be positive")
    return _log_positive(_fraction_interval(1 + ratio, precision), precision)


@dataclass(frozen=True)
class Candidate:
    name: str
    model: str
    constant: Fraction
    decay: Fraction | None = None

    def __post_init__(self) -> None:
        if not self.name:
            raise ValueError("candidate name must be nonempty")
        if self.model not in SUPPORTED_MODELS:
            raise ValueError(f"unsupported model: {self.model}")
        if self.constant < 0:
            raise ValueError("candidate constant must be nonnegative")
        if self.model == "classical_zero_free":
            if self.decay is None or self.decay <= 0:
                raise ValueError("classical zero-free model requires positive decay")
        elif self.decay is not None:
            raise ValueError("decay is only valid for the classical zero-free model")

    def smoothed_error(
        self, x: int, height: int, precision: int = DEFAULT_PRECISION
    ) -> Interval:
        if x < 2:
            raise ValueError("x must be at least 2")
        if height <= 0:
            raise ValueError("height must be positive")

        if self.model == "finite_height":
            return _fraction_interval(self.constant * x * x / height, precision)

        constant = _fraction_interval(self.constant, precision)
        x_interval = _fraction_interval(Fraction(x), precision)
        log_x = _log_positive(x_interval, precision)
        sqrt_x = _sqrt_nonnegative(x_interval, precision)

        if self.model == "rh":
            log_x_squared = _multiply_nonnegative(log_x, log_x, precision)
            return _multiply_nonnegative(
                _multiply_nonnegative(constant, sqrt_x, precision),
                log_x_squared,
                precision,
            )

        assert self.decay is not None
        decay = _fraction_interval(self.decay, precision)
        sqrt_log_x = _sqrt_nonnegative(log_x, precision)
        exponent_magnitude = _multiply_nonnegative(decay, sqrt_log_x, precision)
        exponent = Interval(
            exponent_magnitude.upper.copy_negate(),
            exponent_magnitude.lower.copy_negate(),
        )
        return _multiply_nonnegative(
            _multiply_nonnegative(constant, x_interval, precision),
            _exp(exponent, precision),
            precision,
        )

    def as_dict(self) -> dict[str, str]:
        result = {
            "name": self.name,
            "model": self.model,
            "constant": str(self.constant),
        }
        if self.decay is not None:
            result["decay"] = str(self.decay)
        return result


@dataclass(frozen=True)
class Evaluation:
    h: int
    upper_bound: Decimal
    approximation_difference: Interval
    approximation_bias_upper: Decimal
    propagated_error_upper: Decimal

    def as_dict(self) -> dict[str, object]:
        return {
            "h": self.h,
            "upper_bound": str(self.upper_bound),
            "approximation_difference": self.approximation_difference.as_dict(),
            "approximation_bias_upper": str(self.approximation_bias_upper),
            "propagated_error_upper": str(self.propagated_error_upper),
        }


@dataclass(frozen=True)
class OptimizationResult:
    candidate: Candidate
    selected: Evaluation
    evaluations: tuple[Evaluation, ...]

    def as_dict(self) -> dict[str, object]:
        return {
            "candidate": self.candidate.as_dict(),
            "selected_h": self.selected.h,
            "selected_upper_bound": str(self.selected.upper_bound),
            "evaluations": [item.as_dict() for item in self.evaluations],
        }


@dataclass(frozen=True)
class ComparisonReport:
    schema: str
    x: int
    height: int
    precision: int
    h_values: tuple[int, ...]
    approximation: ApproximationDifferences
    winner: str
    results: tuple[OptimizationResult, ...]

    def to_json(self) -> str:
        payload = {
            "schema": self.schema,
            "arithmetic": {
                "decimal_precision": self.precision,
                "rounding": "outward",
                "transcendentals": "decimal-directed-intervals",
            },
            "domain": {
                "x": self.x,
                "height": self.height,
                "h_values": list(self.h_values),
            },
            "approximation": self.approximation.as_dict(self.h_values),
            "winner": self.winner,
            "results": [result.as_dict() for result in self.results],
        }
        return json.dumps(payload, indent=2, sort_keys=True)


def _evaluate(
    candidate: Candidate,
    x: int,
    height: int,
    h: int,
    approximation_difference: Interval,
    precision: int,
) -> Evaluation:
    if h <= 0:
        raise ValueError("h values must be positive")
    y = x + h
    logarithm = certified_log1p(Fraction(h, x), precision)
    quotient = _divide_by_positive(approximation_difference, logarithm, precision)

    with localcontext(_context(precision, ROUND_CEILING)):
        approximation_bias_upper = max(
            quotient.upper - Decimal(x), Decimal(y) - quotient.lower
        )

    error_sum = _add(
        candidate.smoothed_error(x, height, precision),
        candidate.smoothed_error(y, height, precision),
        precision,
    )
    propagated_error_upper = _divide_by_positive(
        error_sum, logarithm, precision
    ).upper
    with localcontext(_context(precision, ROUND_CEILING)):
        upper_bound = approximation_bias_upper + propagated_error_upper
    return Evaluation(
        h,
        upper_bound,
        approximation_difference,
        approximation_bias_upper,
        propagated_error_upper,
    )


def optimize_candidate(
    candidate: Candidate,
    x: int,
    height: int,
    h_values: Iterable[int],
    approximation: ApproximationDifferences,
    precision: int = DEFAULT_PRECISION,
) -> OptimizationResult:
    values = tuple(sorted(set(h_values)))
    if not values:
        raise ValueError("at least one h value is required")
    approximation.validate_h_values(values)
    evaluations = tuple(
        _evaluate(
            candidate,
            x,
            height,
            h,
            approximation.interval_for(h),
            precision,
        )
        for h in values
    )
    selected = min(evaluations, key=lambda item: (item.upper_bound, item.h))
    return OptimizationResult(candidate, selected, evaluations)


def compare_candidates(
    candidates: Sequence[Candidate],
    x: int,
    height: int,
    h_values: Iterable[int],
    approximation: ApproximationDifferences,
    precision: int = DEFAULT_PRECISION,
) -> ComparisonReport:
    if not candidates:
        raise ValueError("at least one candidate is required")
    values = tuple(sorted(set(h_values)))
    approximation.validate_h_values(values)
    results = tuple(
        optimize_candidate(candidate, x, height, values, approximation, precision)
        for candidate in candidates
    )
    winner = min(results, key=lambda item: (item.selected.upper_bound, item.candidate.name))
    return ComparisonReport(
        schema="smoothed-error-comparison-v2",
        x=x,
        height=height,
        precision=precision,
        h_values=values,
        approximation=approximation,
        winner=winner.candidate.name,
        results=results,
    )


def _parse_fraction(text: str) -> Fraction:
    try:
        return Fraction(text)
    except (ValueError, ZeroDivisionError) as error:
        raise argparse.ArgumentTypeError(str(error)) from error


def _parse_candidate(text: str) -> Candidate:
    fields = text.split(":")
    if len(fields) not in {3, 4}:
        raise argparse.ArgumentTypeError(
            "candidate must be NAME:MODEL:CONSTANT[:DECAY]"
        )
    name, model, constant_text, *decay_text = fields
    decay = _parse_fraction(decay_text[0]) if decay_text else None
    try:
        return Candidate(name, model, _parse_fraction(constant_text), decay)
    except ValueError as error:
        raise argparse.ArgumentTypeError(str(error)) from error


def _parse_approximation_difference(
    text: str,
) -> tuple[int, Interval]:
    fields = text.split(":")
    if len(fields) != 3:
        raise argparse.ArgumentTypeError(
            "approximation difference must be H:LOWER:UPPER"
        )
    h_text, lower_text, upper_text = fields
    try:
        h = int(h_text)
        interval = Interval(Decimal(lower_text), Decimal(upper_text))
        return h, interval
    except (InvalidOperation, ValueError) as error:
        raise argparse.ArgumentTypeError(str(error)) from error


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(
        description="Compare preregistered smoothed-error envelopes with interval-safe arithmetic."
    )
    parser.add_argument("--x", type=int, required=True)
    parser.add_argument("--height", type=int, required=True)
    parser.add_argument("--h", type=int, action="append", required=True, dest="h_values")
    parser.add_argument("--candidate", type=_parse_candidate, action="append", required=True)
    parser.add_argument("--precision", type=int, default=DEFAULT_PRECISION)
    approximation_group = parser.add_mutually_exclusive_group(required=True)
    approximation_group.add_argument(
        "--identity-approximation",
        action="store_true",
        help="use the exact identity difference Re((x+h)-x) = h",
    )
    approximation_group.add_argument(
        "--approximation-difference",
        type=_parse_approximation_difference,
        action="append",
        dest="approximation_differences",
        metavar="H:LOWER:UPPER",
        help="certified interval for Re(A_T(x+h)-A_T(x)); repeat for every h",
    )
    args = parser.parse_args(argv)
    try:
        approximation = (
            ApproximationDifferences.identity()
            if args.identity_approximation
            else ApproximationDifferences.certified(args.approximation_differences)
        )
    except ValueError as error:
        parser.error(str(error))
    report = compare_candidates(
        candidates=args.candidate,
        x=args.x,
        height=args.height,
        h_values=args.h_values,
        approximation=approximation,
        precision=args.precision,
    )
    print(report.to_json())


if __name__ == "__main__":
    main()
