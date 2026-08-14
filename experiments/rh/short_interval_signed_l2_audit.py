"""Finite checks for the signed short-interval L2 research route.

This module verifies algebraic identities and exponent bookkeeping only.  It
does not estimate the signed off-diagonal correlation and therefore does not
prove a zero-free region.
"""

from __future__ import annotations

import argparse
import cmath
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


@dataclass(frozen=True)
class CyclicFourierIdentity:
    direct_energy: float
    double_frequency_energy: float
    diagonal_frequency_energy: float
    frequency_off_diagonal: float
    imaginary_residual: float


@dataclass(frozen=True)
class VaughanComponents:
    short_lambda: float
    type_i_log: float
    type_i_correction: float
    type_ii: float

    @property
    def total(self) -> float:
        return (
            self.short_lambda
            + self.type_i_log
            + self.type_i_correction
            + self.type_ii
        )

    @property
    def centered_total(self) -> float:
        return self.total - 1.0


@dataclass(frozen=True)
class VaughanBudgetEntry:
    name: str
    family: str
    available_exponent: Fraction
    target_exponent: Fraction
    deficit: Fraction
    audited_input: str
    missing_input: str


@dataclass(frozen=True)
class VaughanBudgetAudit:
    target_exponent: Fraction
    entries: Tuple[VaughanBudgetEntry, ...]
    should_stop_vaughan: bool
    guth_maynard_gate_open: bool


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


def von_mangoldt(n: int) -> float:
    """Return the von Mangoldt value using a dependency-free factor check."""

    if n < 2:
        return 0.0
    prime = 2
    while prime * prime <= n and n % prime != 0:
        prime += 1
    if n % prime != 0:
        prime = n
    remaining = n
    while remaining % prime == 0:
        remaining //= prime
    return math.log(prime) if remaining == 1 else 0.0


def mobius(n: int) -> int:
    """Return the Moebius function by trial division."""

    if n < 1:
        raise ValueError("mobius is defined here only for positive integers")
    remaining = n
    prime_factors = 0
    prime = 2
    while prime * prime <= remaining:
        if remaining % prime == 0:
            remaining //= prime
            if remaining % prime == 0:
                return 0
            prime_factors += 1
        while remaining % prime == 0:
            remaining //= prime
        prime += 1
    if remaining > 1:
        prime_factors += 1
    return -1 if prime_factors % 2 else 1


def _divisors(n: int) -> Tuple[int, ...]:
    return tuple(divisor for divisor in range(1, n + 1) if n % divisor == 0)


def vaughan_components(
    n: int, *, u_cutoff: int, v_cutoff: int
) -> VaughanComponents:
    """Evaluate the exact four-term Vaughan identity at one integer.

    The convention is

    ``Lambda = mu_<=U*log - Lambda_<=V*mu_<=U*1
                + 1*mu_>U*Lambda_>V + Lambda_<=V``.
    """

    if n < 1:
        raise ValueError("n must be positive")
    if u_cutoff < 1 or v_cutoff < 1:
        raise ValueError("Vaughan cutoffs must be positive")

    divisors = _divisors(n)
    short_lambda = von_mangoldt(n) if n <= v_cutoff else 0.0
    type_i_log = sum(
        mobius(divisor) * math.log(n // divisor)
        for divisor in divisors
        if divisor <= u_cutoff
    )
    type_i_correction = -sum(
        von_mangoldt(lambda_factor) * mobius(mu_factor)
        for lambda_factor in divisors
        if lambda_factor <= v_cutoff
        for mu_factor in _divisors(n // lambda_factor)
        if mu_factor <= u_cutoff
    )
    type_ii = sum(
        mobius(mu_factor) * von_mangoldt(lambda_factor)
        for lambda_factor in divisors
        if lambda_factor > v_cutoff
        for mu_factor in _divisors(n // lambda_factor)
        if mu_factor > u_cutoff
    )
    return VaughanComponents(
        short_lambda=short_lambda,
        type_i_log=type_i_log,
        type_i_correction=type_i_correction,
        type_ii=type_ii,
    )


def vaughan_two_thirds_budget() -> VaughanBudgetAudit:
    """Record the fixed-power failures under the currently audited inputs.

    The entries are disjoint frequency regimes of the exact weighted Fourier
    identity.  Vaughan's decomposition does not improve their power using only
    the currently available PNT, large-sieve, and mean-value estimates.
    """

    target = Fraction(5, 3)
    available = Fraction(7, 3)
    deficit = available - target
    entries = (
        VaughanBudgetEntry(
            name="very_low_frequency",
            family="grouped Type I plus centering",
            available_exponent=available,
            target_exponent=target,
            deficit=deficit,
            audited_input="classical PNT error on |alpha| <= X^-1",
            missing_input="power-scale centered prime-sum cancellation",
        ),
        VaughanBudgetEntry(
            name="transition_frequency",
            family="nonbalanced Type II",
            available_exponent=available,
            target_exponent=target,
            deficit=deficit,
            audited_input="continuous large sieve on X^-1 < |alpha| < H^-1",
            missing_input="signed spectral non-concentration saving one H",
        ),
        VaughanBudgetEntry(
            name="high_frequency",
            family="balanced Type II",
            available_exponent=available,
            target_exponent=target,
            deficit=deficit,
            audited_input="Montgomery--Vaughan mean value with |alpha|^-2 window",
            missing_input="localized bilinear mean square saving one H",
        ),
    )
    fixed_power_failures = sum(entry.deficit > 0 for entry in entries)
    unique_failure = fixed_power_failures == 1
    return VaughanBudgetAudit(
        target_exponent=target,
        entries=entries,
        should_stop_vaughan=fixed_power_failures >= 2,
        guth_maynard_gate_open=unique_failure,
    )


def _discrete_fourier_transform(values: Iterable[complex]) -> Tuple[complex, ...]:
    entries = tuple(complex(value) for value in values)
    size = len(entries)
    return tuple(
        sum(
            value * cmath.exp(-2j * math.pi * index * frequency / size)
            for index, value in enumerate(entries)
        )
        for frequency in range(size)
    )


def finite_cyclic_weighted_fourier_identity(
    coefficients: Iterable[float], *, window_length: int, weights: Iterable[float]
) -> CyclicFourierIdentity:
    """Check the exact weighted double-frequency identity on a finite cycle.

    With the DFT convention ``f_hat(k)=sum_j f(j)e(-jk/q)``, multiplication
    by a nonconstant position weight couples frequencies through
    ``W_hat(l-k)``.  This finite identity models the two-frequency coupling
    caused by the smooth factor ``w(x/X)`` in the continuous problem.
    """

    coeffs = tuple(float(value) for value in coefficients)
    position_weights = tuple(float(value) for value in weights)
    size = len(coeffs)
    if size == 0:
        raise ValueError("coefficients must be nonempty")
    if len(position_weights) != size:
        raise ValueError("weights must have the same length as coefficients")
    if not 0 <= window_length <= size:
        raise ValueError("window_length must lie between zero and the cycle size")
    if any(weight < 0 for weight in position_weights):
        raise ValueError("weights must be nonnegative")

    window_values = tuple(
        sum(coeffs[(position + offset) % size] for offset in range(1, window_length + 1))
        for position in range(size)
    )
    direct_energy = sum(
        weight * value * value
        for weight, value in zip(position_weights, window_values)
    )

    backward_window = tuple(
        1.0 if size - window_length <= index < size else 0.0
        for index in range(size)
    )
    coefficient_transform = _discrete_fourier_transform(coeffs)
    window_transform = _discrete_fourier_transform(backward_window)
    weighted_window_transform = tuple(
        coefficient_transform[index] * window_transform[index]
        for index in range(size)
    )
    position_weight_transform = _discrete_fourier_transform(position_weights)

    double_frequency = sum(
        weighted_window_transform[left]
        * weighted_window_transform[right].conjugate()
        * position_weight_transform[(right - left) % size]
        for left in range(size)
        for right in range(size)
    ) / (size * size)
    diagonal_frequency = (
        position_weight_transform[0]
        * sum(abs(value) ** 2 for value in weighted_window_transform)
        / (size * size)
    )

    return CyclicFourierIdentity(
        direct_energy=direct_energy,
        double_frequency_energy=double_frequency.real,
        diagonal_frequency_energy=diagonal_frequency.real,
        frequency_off_diagonal=(double_frequency - diagonal_frequency).real,
        imaginary_residual=double_frequency.imag,
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
