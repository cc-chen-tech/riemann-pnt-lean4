from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from decimal import Decimal, Context, ROUND_CEILING, ROUND_FLOOR, localcontext
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


def _multiply_nonnegative(left: Interval, right: Interval, precision: int) -> Interval:
    if left.lower < 0 or right.lower < 0:
        raise ValueError("nonnegative interval multiplication received a negative endpoint")
    with localcontext(_context(precision, ROUND_FLOOR)):
        lower = left.lower * right.lower
    with localcontext(_context(precision, ROUND_CEILING)):
        upper = left.upper * right.upper
    return Interval(lower, upper)


def _divide_positive(left: Interval, right: Interval, precision: int) -> Interval:
    if left.lower < 0 or right.lower <= 0:
        raise ValueError("positive interval division received an invalid endpoint")
    with localcontext(_context(precision, ROUND_FLOOR)):
        lower = left.lower / right.upper
    with localcontext(_context(precision, ROUND_CEILING)):
        upper = left.upper / right.lower
    return Interval(lower, upper)


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
        exponent = Interval(-exponent_magnitude.upper, -exponent_magnitude.lower)
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
    smoothing_bias_upper: Decimal
    propagated_error_upper: Decimal

    def as_dict(self) -> dict[str, object]:
        return {
            "h": self.h,
            "upper_bound": str(self.upper_bound),
            "smoothing_bias_upper": str(self.smoothing_bias_upper),
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
            "winner": self.winner,
            "results": [result.as_dict() for result in self.results],
        }
        return json.dumps(payload, indent=2, sort_keys=True)


def _evaluate(
    candidate: Candidate, x: int, height: int, h: int, precision: int
) -> Evaluation:
    if h <= 0:
        raise ValueError("h values must be positive")
    y = x + h
    logarithm = certified_log1p(Fraction(h, x), precision)
    h_interval = _fraction_interval(Fraction(h), precision)
    quotient = _divide_positive(h_interval, logarithm, precision)

    with localcontext(_context(precision, ROUND_CEILING)):
        smoothing_bias_upper = max(quotient.upper - Decimal(x), Decimal(y) - quotient.lower)

    error_sum = _add(
        candidate.smoothed_error(x, height, precision),
        candidate.smoothed_error(y, height, precision),
        precision,
    )
    propagated_error_upper = _divide_positive(error_sum, logarithm, precision).upper
    with localcontext(_context(precision, ROUND_CEILING)):
        upper_bound = smoothing_bias_upper + propagated_error_upper
    return Evaluation(h, upper_bound, smoothing_bias_upper, propagated_error_upper)


def optimize_candidate(
    candidate: Candidate,
    x: int,
    height: int,
    h_values: Iterable[int],
    precision: int = DEFAULT_PRECISION,
) -> OptimizationResult:
    values = tuple(sorted(set(h_values)))
    if not values:
        raise ValueError("at least one h value is required")
    evaluations = tuple(_evaluate(candidate, x, height, h, precision) for h in values)
    selected = min(evaluations, key=lambda item: (item.upper_bound, item.h))
    return OptimizationResult(candidate, selected, evaluations)


def compare_candidates(
    candidates: Sequence[Candidate],
    x: int,
    height: int,
    h_values: Iterable[int],
    precision: int = DEFAULT_PRECISION,
) -> ComparisonReport:
    if not candidates:
        raise ValueError("at least one candidate is required")
    values = tuple(sorted(set(h_values)))
    results = tuple(
        optimize_candidate(candidate, x, height, values, precision)
        for candidate in candidates
    )
    winner = min(results, key=lambda item: (item.selected.upper_bound, item.candidate.name))
    return ComparisonReport(
        schema="smoothed-error-comparison-v1",
        x=x,
        height=height,
        precision=precision,
        h_values=values,
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


def main(argv: Sequence[str] | None = None) -> None:
    parser = argparse.ArgumentParser(
        description="Compare preregistered smoothed-error envelopes with interval-safe arithmetic."
    )
    parser.add_argument("--x", type=int, required=True)
    parser.add_argument("--height", type=int, required=True)
    parser.add_argument("--h", type=int, action="append", required=True, dest="h_values")
    parser.add_argument("--candidate", type=_parse_candidate, action="append", required=True)
    parser.add_argument("--precision", type=int, default=DEFAULT_PRECISION)
    args = parser.parse_args(argv)
    report = compare_candidates(
        candidates=args.candidate,
        x=args.x,
        height=args.height,
        h_values=args.h_values,
        precision=args.precision,
    )
    print(report.to_json())


if __name__ == "__main__":
    main()
