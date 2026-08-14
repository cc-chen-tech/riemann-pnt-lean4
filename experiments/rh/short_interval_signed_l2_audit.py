"""Finite checks for the signed short-interval L2 research route.

This module verifies algebraic identities and exponent bookkeeping only.  It
does not estimate the signed off-diagonal correlation and therefore does not
prove a zero-free region.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from fractions import Fraction
from numbers import Real
from typing import Dict, Iterable, Mapping, Tuple, Union


Number = Union[int, float, Fraction]
WindowSample = Tuple[float, float, float]


@dataclass(frozen=True)
class ExponentLedger:
    a: Number
    beta: Number
    target: Number
    zero_response: Number
    zero_exclusion_threshold: Number
    contradiction_margin: Number
    diagonal: Number
    floor_remainder: int
    absolute_off_diagonal: Number
    absolute_value_deficit: Number


@dataclass(frozen=True)
class CenteredIdentity:
    window_square: float
    expanded: float
    diagonal: float
    off_diagonal: float


@dataclass(frozen=True)
class PsiWindowDecomposition:
    direct_error: float
    centered_sum: float
    floor_remainder: float
    integer_count: int


@dataclass(frozen=True)
class ZeroDensityExponents:
    sigma: Number
    carlson: Number
    ingham: Number
    guth_maynard: Number
    guth_maynard_uniform: Number
    best_recorded: Number
    linear_eight_thirds: Number
    carlson_derivative: Number
    ingham_derivative: Number
    linear_eight_thirds_derivative: Fraction


def _require_unit_interval(name: str, value: Real) -> None:
    if not 0 < value < 1:
        raise ValueError(f"{name} must lie strictly between 0 and 1")


def exponent_ledger(*, a: Number, beta: Number) -> ExponentLedger:
    """Return exact scale exponents when ``a`` and ``beta`` are Fractions.

    The coarse off-diagonal line is the result of discarding every sign in a
    length-X family of windows of length H=X^a: X H^2 = X^(1+2a).
    """

    _require_unit_interval("a", a)
    _require_unit_interval("beta", beta)
    target = 1 + a
    zero_response = 2 * beta + 2 * a - 1
    absolute_off_diagonal = 1 + 2 * a
    return ExponentLedger(
        a=a,
        beta=beta,
        target=target,
        zero_response=zero_response,
        zero_exclusion_threshold=1 - a / 2,
        contradiction_margin=zero_response - target,
        diagonal=target,
        floor_remainder=1,
        absolute_off_diagonal=absolute_off_diagonal,
        absolute_value_deficit=absolute_off_diagonal - target,
    )


def weighted_centered_identity(
    coefficients: Mapping[int, float], samples: Iterable[WindowSample]
) -> CenteredIdentity:
    """Expand a finite weighted mean square without losing coefficient signs.

    ``coefficients`` represents b(n)=Lambda(n)-1.  Each sample is ``(x,h,q)``
    and contributes q times the square of the sum over x<n<=x+h.
    """

    window_square = 0.0
    expanded = 0.0
    diagonal = 0.0
    off_diagonal = 0.0
    coefficient_items = tuple(coefficients.items())

    for x, h, weight in samples:
        if h < 0:
            raise ValueError("window length h must be nonnegative")
        if weight < 0:
            raise ValueError("sample weight must be nonnegative")
        active = [(n, b_n) for n, b_n in coefficient_items if x < n <= x + h]
        window_sum = sum(b_n for _, b_n in active)
        window_square += weight * window_sum * window_sum
        for n, b_n in active:
            for m, b_m in active:
                term = weight * b_n * b_m
                expanded += term
                if n == m:
                    diagonal += term
                else:
                    off_diagonal += term

    return CenteredIdentity(
        window_square=window_square,
        expanded=expanded,
        diagonal=diagonal,
        off_diagonal=off_diagonal,
    )


def psi_window_decomposition(
    lambda_values: Mapping[int, float], *, x: float, h: float
) -> PsiWindowDecomposition:
    """Check psi(x+h)-psi(x)-h = sum(Lambda(n)-1)+rounding.

    Missing mapping entries are treated as Lambda(n)=0.  The rounding term is
    ``floor(x+h)-floor(x)-h`` and always has absolute value below one.
    """

    if h < 0:
        raise ValueError("window length h must be nonnegative")
    first = math.floor(x) + 1
    last = math.floor(x + h)
    integers = range(first, last + 1) if first <= last else range(0)
    values = [float(lambda_values.get(n, 0.0)) for n in integers]
    integer_count = len(values)
    direct_error = sum(values) - h
    centered_sum = sum(value - 1.0 for value in values)
    floor_remainder = integer_count - h
    return PsiWindowDecomposition(
        direct_error=direct_error,
        centered_sum=centered_sum,
        floor_remainder=floor_remainder,
        integer_count=integer_count,
    )


def zero_density_exponents(sigma: Number) -> ZeroDensityExponents:
    """Exact classical density exponents plus the 8/3 comparison line.

    Ingham's classical exponent is 3(1-sigma)/(2-sigma).  The frequently
    quoted linear curve 8(1-sigma)/3 is recorded separately: it crosses the
    Carlson curve at 2/3 but is not the exact Ingham exponent.
    """

    _require_unit_interval("sigma", sigma)
    carlson = 4 * sigma * (1 - sigma)
    ingham = 3 * (1 - sigma) / (2 - sigma)
    guth_maynard = 15 * (1 - sigma) / (3 + 5 * sigma)
    guth_maynard_uniform = Fraction(30, 13) * (1 - sigma)
    return ZeroDensityExponents(
        sigma=sigma,
        carlson=carlson,
        ingham=ingham,
        guth_maynard=guth_maynard,
        guth_maynard_uniform=guth_maynard_uniform,
        best_recorded=min(
            carlson, ingham, guth_maynard, guth_maynard_uniform
        ),
        linear_eight_thirds=Fraction(8, 3) * (1 - sigma),
        carlson_derivative=4 - 8 * sigma,
        ingham_derivative=-3 / (2 - sigma) ** 2,
        linear_eight_thirds_derivative=Fraction(-8, 3),
    )


def growth_exponent(*, c: float, k: float) -> float:
    """Return log(c)/log(k) for the Carlson packet-growth backup route."""

    if c <= 0:
        raise ValueError("c must be positive")
    if k <= 1:
        raise ValueError("k must be greater than 1")
    return math.log(c) / math.log(k)


def _jsonable(value: object) -> object:
    if isinstance(value, Fraction):
        return {"exact": str(value), "decimal": float(value)}
    if isinstance(value, dict):
        return {key: _jsonable(item) for key, item in value.items()}
    return value


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--a", default="2/3", help="window exponent")
    parser.add_argument("--beta", default="3/4", help="model zero real part")
    args = parser.parse_args()
    ledger = exponent_ledger(a=Fraction(args.a), beta=Fraction(args.beta))
    print(json.dumps(_jsonable(asdict(ledger)), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
