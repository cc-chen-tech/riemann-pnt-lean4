#!/usr/bin/env python3
"""Finite Möbius identity and fixed-factor Type-I exponent audit.

This module verifies finite convolution algebra and rational inequalities.
It does not prove the residual averaged Type-II oscillatory estimate.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache

try:
    from scripts.audit_mwkf_ranges import (
        ExponentBox,
        boundary_witnesses,
        is_admissible,
    )
except ModuleNotFoundError:  # Direct invocation.
    from audit_mwkf_ranges import (  # type: ignore[no-redef]
        ExponentBox,
        boundary_witnesses,
        is_admissible,
    )


def divisors(n: int) -> tuple[int, ...]:
    small: list[int] = []
    large: list[int] = []
    d = 1
    while d * d <= n:
        if n % d == 0:
            small.append(d)
            if d * d != n:
                large.append(n // d)
        d += 1
    return tuple(small + list(reversed(large)))


@lru_cache(maxsize=None)
def mobius(n: int) -> int:
    if n < 1:
        raise ValueError("mobius is defined here only for positive integers")
    value = 1
    remaining = n
    prime = 2
    while prime * prime <= remaining:
        if remaining % prime == 0:
            remaining //= prime
            value = -value
            if remaining % prime == 0:
                return 0
            while remaining % prime == 0:
                remaining //= prime
        prime += 1
    if remaining > 1:
        value = -value
    return value


def short_mobius(n: int, cutoff: int) -> int:
    return mobius(n) if n <= cutoff else 0


@lru_cache(maxsize=None)
def c_coefficient(n: int, cutoff: int) -> int:
    """Coefficient of ``1 * mu_{<=U} - delta_1``."""

    if cutoff < 1 or n < 1:
        raise ValueError("n and cutoff must be positive")
    total = sum(mobius(d) for d in divisors(n) if d <= cutoff)
    return total - (1 if n == 1 else 0)


@lru_cache(maxsize=None)
def _c_power(n: int, cutoff: int, power: int) -> int:
    if power < 0:
        raise ValueError("power must be nonnegative")
    if power == 0:
        return 1 if n == 1 else 0
    return sum(
        c_coefficient(d, cutoff) * _c_power(n // d, cutoff, power - 1)
        for d in divisors(n)
    )


def mobius_geometric_value(n: int, cutoff: int, depth: int) -> int:
    """Evaluate the truncated geometric convolution identity at ``n``."""

    if depth < 1:
        raise ValueError("depth must be positive")
    total = 0
    for power in range(depth):
        convolution = sum(
            short_mobius(d, cutoff)
            * _c_power(n // d, cutoff, power)
            for d in divisors(n)
        )
        total += (-1) ** power * convolution
    return total


@dataclass(frozen=True)
class WrightFactorSavings:
    first: Fraction
    second: Fraction
    third: Fraction
    fourth: Fraction
    fifth: Fraction

    def values(self) -> tuple[Fraction, ...]:
        return (
            self.first,
            self.second,
            self.third,
            self.fourth,
            self.fifth,
        )


@dataclass(frozen=True)
class PascadiFullResidueSavings:
    """Four savings from Pascadi Theorem 7.8(i) at M=N=c."""

    first: Fraction
    second: Fraction
    third: Fraction
    fourth: Fraction

    def values(self) -> tuple[Fraction, ...]:
        return (self.first, self.second, self.third, self.fourth)


@dataclass(frozen=True)
class MQWBlockSavings:
    """Savings in Milićević--Qin--Wu Theorem 1.1.

    The bilinear block lengths are ``M=q^x`` and ``N=q^y``.  The three
    entries are the negative q-exponents of the three factors in the
    parenthesis in that theorem.
    """

    first: Fraction
    second: Fraction
    third: Fraction

    def values(self) -> tuple[Fraction, ...]:
        return (self.first, self.second, self.third)


def mqw_block_savings(x: Fraction, y: Fraction) -> MQWBlockSavings:
    """Return the exact three savings for a block of exponents ``x,y``."""

    if x < 0 or y < 0:
        raise ValueError("bilinear length exponents must be nonnegative")
    return MQWBlockSavings(
        first=x / 2 - Fraction(1, 6),
        second=3 * x / 25 + 3 * y / 10 - Fraction(1, 5),
        third=3 * (x + y) / 16 - Fraction(11, 64),
    )


def mqw_initial_rectangle_witness() -> tuple[Fraction, Fraction]:
    """Boundary point certifying the theorem's supremal saving."""

    return Fraction(5, 8), Fraction(5, 8)


def mqw_initial_rectangle_supremal_saving() -> Fraction:
    """Exact supremum allowed by the theorem's support constraints.

    The condition ``x+y <= 5/4`` forces the third saving to be at most
    1/16.  The witness ``x=y=5/8`` satisfies all size conditions and its
    other two savings are at least 1/16, so the ceiling is approached from
    inside the theorem's strict ``(7/5)x+y < 3/2`` condition.
    This is not a partition result for a full residue grid.  The theorem's
    variables are supported in ``[1, q^x]`` and ``[1, q^y]``; translating
    a high interval changes the product Kloosterman kernel.
    """

    x, y = mqw_initial_rectangle_witness()
    savings = mqw_block_savings(x, y)
    ceiling = Fraction(3, 16) * Fraction(5, 4) - Fraction(11, 64)
    if not (
        x <= y + Fraction(1, 4)
        and Fraction(7, 5) * x + y <= Fraction(3, 2)
        and x + y <= Fraction(5, 4)
        and min(savings.values()) == ceiling
    ):
        raise AssertionError("invalid exact MQW supremum certificate")
    return ceiling


def elementary_large_sieve_loss(box: ExponentBox) -> Fraction:
    """Power lost by the two-orientation Farey large-sieve bound.

    On the admissible polytope, ``A <= min(R^2, S^2)``.  Choosing the
    better of the original fraction orientation and reciprocity gives
    ``RS * sqrt(A)``.  Hence the loss over the local ``RS`` target is
    exactly half the third-variable exponent.
    """

    if not is_admissible(box):
        raise ValueError("large-sieve loss is defined only on admissible boxes")
    return box.third_length / 2


def pascadi_full_residue_savings(
    delta: Fraction,
) -> PascadiFullResidueSavings:
    """Return powers saved over the full-residue trivial scale.

    These are obtained from Pascadi Theorem 7.8(i) after setting both
    bilinear lengths equal to the modulus. The theorem assumes
    ``0 <= delta <= 1/24``.
    """

    if delta < 0 or delta > Fraction(1, 24):
        raise ValueError("Pascadi's delta must lie in [0, 1/24]")
    return PascadiFullResidueSavings(
        first=(Fraction(13, 64) - Fraction(53, 64) * delta),
        second=(1 + delta) / 6,
        third=(4 + delta) / 12,
        fourth=Fraction(13, 24),
    )


def pascadi_optimal_delta() -> Fraction:
    """Intersection of the two decisive full-residue savings."""

    return Fraction(7, 191)


def pascadi_balanced_gap() -> Fraction:
    """Residual T-exponent after optimistic use in the balanced box."""

    modulus_saving = min(
        pascadi_full_residue_savings(pascadi_optimal_delta()).values()
    )
    return Fraction(5) - 3 * modulus_saving


def wright_factor_savings(
    box: ExponentBox, tau: Fraction
) -> WrightFactorSavings:
    """Savings after fixing ``s = u n`` and summing ``u`` in L1.

    Here ``U = T^tau``. The formulas include the full factor ``U`` from
    taking absolute values over the fixed denominator factor.
    """

    a = box.third_length
    return WrightFactorSavings(
        first=box.sigma / 8 - a - 3 * tau / 8,
        second=box.rho / 4 - box.sigma / 8 - a - tau / 4,
        third=(
            3 * box.sigma / 20
            - box.rho / 10
            - 19 * a / 20
            - tau / 4
        ),
        fourth=(
            box.rho / 5
            - 3 * box.sigma / 20
            - 17 * a / 20
            - tau / 10
        ),
        fifth=(
            box.rho / 2
            - 3 * box.sigma / 8
            - a
            + tau / 8
        ),
    )


def wright_factor_covers(box: ExponentBox, tau: Fraction) -> bool:
    """Whether the termwise fixed-factor route reaches the local target."""

    if not is_admissible(box) or tau < 0 or tau > box.sigma:
        return False
    if box.rho > 2 * (box.sigma - tau):
        return False
    return all(value >= 0 for value in wright_factor_savings(box, tau).values())


def _format_fraction(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def main() -> None:
    for name, box in sorted(boundary_witnesses().items()):
        savings = wright_factor_savings(box, Fraction(0))
        text = ",".join(_format_fraction(value) for value in savings.values())
        print(f"{name}: tau=0 wright_factor_savings={text}")


if __name__ == "__main__":
    main()
