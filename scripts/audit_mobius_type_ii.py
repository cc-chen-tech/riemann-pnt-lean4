#!/usr/bin/env python3
"""Finite Möbius identity and fixed-factor Type-I exponent audit.

This module verifies finite convolution algebra and rational inequalities.
It does not prove the residual averaged Type-II oscillatory estimate.
"""

from __future__ import annotations

import cmath
from collections.abc import Mapping
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from math import gcd, lcm

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


def _euler_phi(n: int) -> int:
    if n < 1:
        raise ValueError("modulus must be positive")
    result = n
    remaining = n
    prime = 2
    while prime * prime <= remaining:
        if remaining % prime == 0:
            result -= result // prime
            while remaining % prime == 0:
                remaining //= prime
        prime += 1
    if remaining > 1:
        result -= result // remaining
    return result


def _kloosterman_sum(
    modulus: int, inverse_coefficient: int, linear_coefficient: int
) -> complex:
    if modulus < 1:
        raise ValueError("modulus must be positive")
    if modulus == 1:
        return 1 + 0j
    return sum(
        cmath.exp(
            2j
            * cmath.pi
            * (
                inverse_coefficient * pow(residue, -1, modulus)
                + linear_coefficient * residue
            )
            / modulus
        )
        for residue in range(modulus)
        if gcd(residue, modulus) == 1
    )


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


def two_sided_mobius_geometric_value(
    r: int,
    s: int,
    *,
    cutoff_r: int,
    cutoff_s: int,
    depth_r: int,
    depth_s: int,
) -> int:
    """Evaluate the exact finite expansion of ``mu(r) * mu(s)``.

    The two truncated geometric convolution identities are applied
    independently.  Keeping their product unexpanded in analytic work is
    what retains both outer short Möbius averages.
    """

    return mobius_geometric_value(
        r, cutoff_r, depth_r
    ) * mobius_geometric_value(s, cutoff_s, depth_s)


def mobius_two_cutoff_hyperbola_value(
    n: int,
    *,
    cutoff_left: int,
    cutoff_right: int,
) -> int:
    """Evaluate the exact short-short/long-long split of ``mu(n)``.

    For ``n > max(cutoff_left, cutoff_right)``, the two mixed rectangles
    in ``sum_{bc | n} mu(b) mu(c)`` vanish by divisor orthogonality.
    Thus ``mu(n)`` is the long-long rectangle minus the short-short one,
    with no truncation remainder.
    """

    if n < 1 or cutoff_left < 1 or cutoff_right < 1:
        raise ValueError("n and both cutoffs must be positive")
    if n <= max(cutoff_left, cutoff_right):
        raise ValueError("n must exceed both cutoffs")

    short_short = 0
    long_long = 0
    for left_factor in divisors(n):
        for right_factor in divisors(n // left_factor):
            contribution = mobius(left_factor) * mobius(right_factor)
            if (
                left_factor <= cutoff_left
                and right_factor <= cutoff_right
            ):
                short_short += contribution
            elif (
                left_factor > cutoff_left
                and right_factor > cutoff_right
            ):
                long_long += contribution
    return long_long - short_short


def mobius_two_cutoff_product_coefficient(
    product: int,
    *,
    cutoff_left: int,
    cutoff_right: int,
) -> TwoCutoffProductCoefficient:
    """Group the exact two-cutoff identity by the product ``m=bc``.

    The short-short field already includes its minus sign from the
    hyperbola identity.  Thus ``combined`` is the coefficient
    ``lambda_{U,V}(m)`` for which ``mu(n)=sum_{m|n} lambda_{U,V}(m)``
    whenever ``n>max(U,V)``.
    """

    if product < 1 or cutoff_left < 1 or cutoff_right < 1:
        raise ValueError("the product and both cutoffs must be positive")
    short_short = 0
    long_long = 0
    for left_factor in divisors(product):
        right_factor = product // left_factor
        contribution = mobius(left_factor) * mobius(right_factor)
        if left_factor <= cutoff_left and right_factor <= cutoff_right:
            short_short -= contribution
        elif left_factor > cutoff_left and right_factor > cutoff_right:
            long_long += contribution
    return TwoCutoffProductCoefficient(
        short_short=short_short,
        long_long=long_long,
        combined=short_short + long_long,
    )


def mobius_two_cutoff_product_value(
    product: int,
    *,
    cutoff_left: int,
    cutoff_right: int,
) -> int:
    """Return the grouped coefficient ``lambda_{U,V}(product)``."""

    return mobius_two_cutoff_product_coefficient(
        product,
        cutoff_left=cutoff_left,
        cutoff_right=cutoff_right,
    ).combined


def squarefree_high_product_multiplicity(
    product: int,
    *,
    cutoff_left: int,
    cutoff_right: int,
) -> int:
    """Count the long-long factorizations of a squarefree product.

    When ``product>U*V``, the short-short coefficient vanishes.  Every
    factor pair of a squarefree product is coprime, so each surviving
    Möbius product has the common sign ``mu(product)``.
    """

    if min(product, cutoff_left, cutoff_right) < 1:
        raise ValueError("the product and cutoffs must be positive")
    if mobius(product) == 0:
        raise ValueError("the high-product sign identity is squarefree")
    return sum(
        left_factor > cutoff_left
        and product // left_factor > cutoff_right
        for left_factor in divisors(product)
    )


def squarefree_complementary_sign_recombination(
    shifted_argument: int,
    product_divisor: int,
) -> tuple[int, int]:
    """Move ``mu(m)`` to ``mu(mk)mu(k)`` when ``mk`` is squarefree."""

    if min(shifted_argument, product_divisor) < 1:
        raise ValueError("the shifted argument and divisor must be positive")
    if shifted_argument % product_divisor != 0:
        raise ValueError("the product divisor must divide the shifted argument")
    if mobius(shifted_argument) == 0:
        raise ValueError("the shifted argument must be squarefree")
    quotient = shifted_argument // product_divisor
    direct = mobius(product_divisor)
    recombined = mobius(shifted_argument) * mobius(quotient)
    return direct, recombined


def mobius_two_cutoff_density_period_average(
    scalar: int,
    *,
    product_limit: int,
    cutoff_left: int,
    cutoff_right: int,
) -> tuple[Fraction, Fraction]:
    """Check the exact finite principal density through ``m<=M``.

    Average over one common period, restricted to residues coprime to
    ``scalar``.  A congruence ``m | scalar+d`` has relative density
    ``1/m`` precisely when ``(m,scalar)=1`` and otherwise has no allowed
    residue.  The returned pair is the direct period average and this
    finite density prefix; no limiting interchange is used.
    """

    if min(scalar, product_limit, cutoff_left, cutoff_right) < 1:
        raise ValueError("all inputs must be positive")
    product_period = 1
    for product in range(1, product_limit + 1):
        product_period = lcm(product_period, product)
    period = lcm(product_period, scalar)
    allowed_residues = tuple(
        shift for shift in range(period) if gcd(shift, scalar) == 1
    )
    direct_total = sum(
        mobius_two_cutoff_product_value(
            product,
            cutoff_left=cutoff_left,
            cutoff_right=cutoff_right,
        )
        for shift in allowed_residues
        for product in range(1, product_limit + 1)
        if (scalar + shift) % product == 0
    )
    density = sum(
        Fraction(
            mobius_two_cutoff_product_value(
                product,
                cutoff_left=cutoff_left,
                cutoff_right=cutoff_right,
            ),
            product,
        )
        for product in range(1, product_limit + 1)
        if gcd(product, scalar) == 1
    )
    return Fraction(direct_total, len(allowed_residues)), density


def mobius_two_cutoff_density_complement_ramanujan_coefficients(
    *,
    max_argument: int,
    density_cutoff: int,
    cutoff_left: int,
    cutoff_right: int,
) -> tuple[Fraction, ...]:
    """Finite Ramanujan coefficients of density plus large divisors.

    Put ``lambda(m)`` for the grouped two-cutoff coefficient.  For
    ``r>1`` the coefficient is

    ``C_r = sum_{D<m<=Y, r|m} lambda(m)/m``.

    At ``r=1`` the low-product density is added, so

    ``C_1 = sum_{m<=Y} lambda(m)/m``.

    The index-zero entry is a sentinel.  The identity
    ``sum_{r|m} c_r(n) = m * 1_{m|n}`` then reconstructs the density
    plus every complementary divisor exactly for ``n<=Y``.
    """

    if min(
        max_argument,
        density_cutoff,
        cutoff_left,
        cutoff_right,
    ) < 1:
        raise ValueError("all inputs must be positive")
    if density_cutoff > max_argument:
        raise ValueError("the density cutoff cannot exceed Y")

    product_coefficients = tuple(
        Fraction(
            mobius_two_cutoff_product_value(
                product,
                cutoff_left=cutoff_left,
                cutoff_right=cutoff_right,
            ),
            product,
        )
        for product in range(max_argument + 1)
        if product > 0
    )
    coefficients = [Fraction(0) for _ in range(max_argument + 1)]
    coefficients[1] = sum(product_coefficients)
    for reduced_denominator in range(2, max_argument + 1):
        coefficients[reduced_denominator] = sum(
            product_coefficients[product - 1]
            for product in range(
                reduced_denominator,
                max_argument + 1,
                reduced_denominator,
            )
            if product > density_cutoff
        )
    return tuple(coefficients)


def mobius_two_cutoff_density_complement_ramanujan_value(
    n: int,
    *,
    max_argument: int,
    density_cutoff: int,
    cutoff_left: int,
    cutoff_right: int,
) -> Fraction:
    """Direct density-plus-complementary value used by the expansion."""

    if n < 1 or n > max_argument:
        raise ValueError("require 1 <= n <= max_argument")
    coefficients = (
        mobius_two_cutoff_density_complement_ramanujan_coefficients(
            max_argument=max_argument,
            density_cutoff=density_cutoff,
            cutoff_left=cutoff_left,
            cutoff_right=cutoff_right,
        )
    )
    density = sum(
        Fraction(
            mobius_two_cutoff_product_value(
                product,
                cutoff_left=cutoff_left,
                cutoff_right=cutoff_right,
            ),
            product,
        )
        for product in range(1, density_cutoff + 1)
    )
    complementary = sum(
        mobius_two_cutoff_product_value(
            product,
            cutoff_left=cutoff_left,
            cutoff_right=cutoff_right,
        )
        for product in range(density_cutoff + 1, max_argument + 1)
        if n % product == 0
    )
    # Keep the coefficient construction live in this direct evaluator;
    # it also validates all cutoffs before the literal finite sum.
    if len(coefficients) != max_argument + 1:
        raise AssertionError("coefficient vector has the wrong length")
    return density + complementary


def mobius_two_cutoff_centered_divisor_split(
    n: int,
    *,
    product_cutoff: int,
    cutoff_left: int,
    cutoff_right: int,
) -> TwoCutoffCenteredSplit:
    """Split ``mu(n)`` into density, centered, and large divisors.

    This is the exact pointwise version of subtracting the unrestricted
    principal density only for ``m<=M``.  Nondivisor density terms
    cancel inside the centered field, so no auxiliary scalar or
    coprimality hypothesis is needed.
    """

    if min(n, product_cutoff, cutoff_left, cutoff_right) < 1:
        raise ValueError("all inputs must be positive")
    if n <= max(cutoff_left, cutoff_right):
        raise ValueError("n must exceed both two-cutoff parameters")
    density = sum(
        Fraction(
            mobius_two_cutoff_product_value(
                product,
                cutoff_left=cutoff_left,
                cutoff_right=cutoff_right,
            ),
            product,
        )
        for product in range(1, product_cutoff + 1)
    )
    centered = sum(
        mobius_two_cutoff_product_value(
            product,
            cutoff_left=cutoff_left,
            cutoff_right=cutoff_right,
        )
        * (
            Fraction(1 if n % product == 0 else 0)
            - Fraction(1, product)
        )
        for product in range(1, product_cutoff + 1)
    )
    complementary = sum(
        mobius_two_cutoff_product_value(
            product,
            cutoff_left=cutoff_left,
            cutoff_right=cutoff_right,
        )
        for product in divisors(n)
        if product > product_cutoff
    )
    total = density + centered + complementary
    return TwoCutoffCenteredSplit(
        density=density,
        centered=centered,
        complementary=Fraction(complementary),
        total=total,
    )


def mobius_principal_density_value(
    n: int,
    *,
    cutoff_left: int,
    cutoff_right: int,
) -> Fraction:
    """Principal-character density in the two-cutoff Möbius split."""

    if n < 1 or cutoff_left < 1 or cutoff_right < 1:
        raise ValueError("n and both cutoffs must be positive")
    if n <= max(cutoff_left, cutoff_right):
        raise ValueError("n must exceed both cutoffs")

    short_short = Fraction(0)
    long_long = Fraction(0)
    for left_factor in divisors(n):
        for right_factor in divisors(n // left_factor):
            product = left_factor * right_factor
            contribution = Fraction(
                mobius(left_factor) * mobius(right_factor),
                _euler_phi(product),
            )
            if (
                left_factor <= cutoff_left
                and right_factor <= cutoff_right
            ):
                short_short += contribution
            elif (
                left_factor > cutoff_left
                and right_factor > cutoff_right
            ):
                long_long += contribution
    return long_long - short_short


def _validate_scalar_factor_family(
    modulus: int,
    interval_length: int,
    scalar_factors: tuple[int, ...],
) -> None:
    if modulus < 2 or interval_length < 1:
        raise ValueError("the modulus and interval length must be positive")
    if mobius(modulus) == 0:
        raise ValueError("the primitive scalar identity requires squarefree s")
    if any(factor < 1 or modulus % factor != 0 for factor in scalar_factors):
        raise ValueError("every scalar factor must divide s")
    if len(set(scalar_factors)) != len(scalar_factors):
        raise ValueError("the scalar-factor family must not contain duplicates")


def _validate_primitive_scalar_inputs(
    modulus: int,
    shift: int,
    interval_length: int,
    scalar_factors: tuple[int, ...],
) -> None:
    _validate_scalar_factor_family(
        modulus,
        interval_length,
        scalar_factors,
    )
    if gcd(shift, modulus) != 1:
        raise ValueError("the shift must be a unit modulo s")


def _inverse_additive_phase(
    modulus: int,
    numerator: int,
    shift: int,
) -> complex:
    if modulus == 1:
        return 1 + 0j
    residue = numerator * pow(shift, -1, modulus) % modulus
    return cmath.exp(2j * cmath.pi * residue / modulus)


def primitive_scalar_direct_value(
    modulus: int,
    shift: int,
    frequency: int,
    interval_length: int,
    scalar_factors: tuple[int, ...],
) -> complex:
    """Sum fixed primitive scalar strata with their reduced moduli."""

    _validate_primitive_scalar_inputs(
        modulus,
        shift,
        interval_length,
        scalar_factors,
    )
    total = 0j
    for scalar_factor in scalar_factors:
        reduced_modulus = modulus // scalar_factor
        sign = mobius(scalar_factor) * mobius(reduced_modulus)
        total += sign * sum(
            _inverse_additive_phase(
                reduced_modulus,
                -frequency * reduced_numerator,
                shift,
            )
            for reduced_numerator in range(
                1,
                interval_length // scalar_factor + 1,
            )
        )
    return total


def primitive_scalar_recombined_value(
    modulus: int,
    shift: int,
    frequency: int,
    interval_length: int,
    scalar_factors: tuple[int, ...],
) -> complex:
    """Recombine ``s=gq, m=g*delta`` before estimating the scalar sum."""

    _validate_primitive_scalar_inputs(
        modulus,
        shift,
        interval_length,
        scalar_factors,
    )
    return mobius(modulus) * sum(
        _inverse_additive_phase(
            modulus,
            -frequency * scalar_factor * reduced_numerator,
            shift,
        )
        for scalar_factor in scalar_factors
        for reduced_numerator in range(
            1,
            interval_length // scalar_factor + 1,
        )
    )


def scalar_incidence_energy(
    modulus: int,
    interval_length: int,
    scalar_factors: tuple[int, ...],
) -> int:
    """Direct second moment of the scalar divisor-incidence count."""

    _validate_scalar_factor_family(
        modulus,
        interval_length,
        scalar_factors,
    )
    return sum(
        sum(multiple % factor == 0 for factor in scalar_factors) ** 2
        for multiple in range(1, interval_length + 1)
    )


def scalar_incidence_pair_energy_formula(
    modulus: int,
    interval_length: int,
    scalar_factors: tuple[int, ...],
) -> int:
    """LCM-pair formula for the scalar divisor-incidence energy."""

    _validate_scalar_factor_family(
        modulus,
        interval_length,
        scalar_factors,
    )
    return sum(
        interval_length
        // (left_factor * right_factor // gcd(left_factor, right_factor))
        for left_factor in scalar_factors
        for right_factor in scalar_factors
    )


def scalar_type_i_absolute_exponent(
    scalar_length: Fraction,
    left_cutoff: Fraction,
    right_cutoff: Fraction,
) -> Fraction:
    """Power cost of the absolute short-short congruence count."""

    if min(scalar_length, left_cutoff, right_cutoff) < 0:
        raise ValueError("all cutoff exponents must be nonnegative")
    return max(scalar_length, left_cutoff + right_cutoff)


def central_major_arc_mertens_ledger(
    *,
    scalar_length: Fraction,
    quotient_length: Fraction,
    shifted_length: Fraction,
    shift_average: Fraction,
    target: Fraction,
    scalar_relative_saving: Fraction,
    quotient_relative_saving: Fraction,
    shifted_relative_saving: Fraction,
) -> CentralMajorArcMertensLedger:
    """Audit a factorwise Mertens bound on the additive central arc.

    The first Möbius polynomial factors at zero frequency into lengths
    ``G`` and ``Q``; the shifted Möbius polynomial has length ``S``.
    A central arc of width the reciprocal of the longer polynomial gives
    the raw exponent below.  Relative savings ``eta`` mean a bound
    ``X^(1-eta)`` for the corresponding polynomial, uniformly across
    that arc by partial summation.
    """

    lengths = (
        scalar_length,
        quotient_length,
        shifted_length,
        shift_average,
        target,
    )
    savings = (
        scalar_relative_saving,
        quotient_relative_saving,
        shifted_relative_saving,
    )
    if min(lengths) < 0:
        raise ValueError("all length exponents must be nonnegative")
    if any(saving < 0 or saving > 1 for saving in savings):
        raise ValueError("relative savings must lie in [0,1]")
    first_polynomial = scalar_length + quotient_length
    central_arc_width = max(first_polynomial, shifted_length)
    raw_bound = (
        first_polynomial
        + shifted_length
        + shift_average
        - central_arc_width
    )
    available_saving = (
        scalar_length * scalar_relative_saving
        + quotient_length * quotient_relative_saving
        + shifted_length * shifted_relative_saving
    )
    conditional_bound = raw_bound - available_saving
    return CentralMajorArcMertensLedger(
        raw_bound=raw_bound,
        required_saving=raw_bound - target,
        available_saving=available_saving,
        conditional_bound=conditional_bound,
        gap=conditional_bound - target,
    )


def vinogradov_denominator_coverage_ledger(
    *,
    polynomial_length: Fraction,
    required_relative_saving: Fraction,
    actual_denominator_floor: Fraction,
    actual_denominator_ceiling: Fraction,
) -> VinogradovDenominatorCoverageLedger:
    """Coverage of a rational-approximation Möbius exponential bound.

    If ``X=T^x`` and ``alpha`` has a reduced approximation of
    denominator ``T^r``, Vaughan's two-fifths split gives the three
    exponent terms

    ``4x/5``, ``x-r/2``, and ``x/2+r/2``.

    Requiring a relative saving ``eta`` therefore restricts the
    denominator exponent to

    ``2*x*eta <= r <= x*(1-2*eta)``

    and also requires ``eta <= 1/5`` because of the Type-I floor.  The
    returned overlap is closed; ``has_positive_width_overlap`` is false
    when the theorem and application meet at only one endpoint.
    """

    lengths = (
        polynomial_length,
        actual_denominator_floor,
        actual_denominator_ceiling,
    )
    if min(lengths) < 0:
        raise ValueError("all length exponents must be nonnegative")
    if not 0 <= required_relative_saving <= 1:
        raise ValueError("the relative saving must lie in [0,1]")
    if actual_denominator_floor > actual_denominator_ceiling:
        raise ValueError("the denominator interval must be ordered")

    type_i_bound = Fraction(4, 5) * polynomial_length
    target_bound = polynomial_length * (1 - required_relative_saving)
    theorem_floor = (
        2 * polynomial_length * required_relative_saving
    )
    theorem_ceiling = polynomial_length * (
        1 - 2 * required_relative_saving
    )
    overlap_floor = max(actual_denominator_floor, theorem_floor)
    overlap_ceiling = min(actual_denominator_ceiling, theorem_ceiling)
    type_i_compatible = type_i_bound <= target_bound
    return VinogradovDenominatorCoverageLedger(
        polynomial_length=polynomial_length,
        required_relative_saving=required_relative_saving,
        type_i_bound=type_i_bound,
        target_bound=target_bound,
        theorem_denominator_floor=theorem_floor,
        theorem_denominator_ceiling=theorem_ceiling,
        actual_denominator_floor=actual_denominator_floor,
        actual_denominator_ceiling=actual_denominator_ceiling,
        overlap_floor=overlap_floor,
        overlap_ceiling=overlap_ceiling,
        has_positive_width_overlap=(
            type_i_compatible and overlap_floor < overlap_ceiling
        ),
    )


def nonzero_reduced_denominator_ledger(
    *,
    outer_length: Fraction,
    shift_length: Fraction,
    denominator_length: Fraction,
    fourier_decay_order: int,
    target: Fraction,
) -> NonzeroReducedDenominatorLedger:
    """Large-sieve ledger for ``2 <= r <= D`` Ramanujan modes.

    On ``r~R`` the finite coefficient satisfies
    ``|C_r| << T^epsilon/R``.  Cauchy and the additive large sieve give
    the two constants ``S+R^2`` and ``D+R^2``.  Since every primitive
    numerator is nonzero, the smooth shift transform additionally gains
    ``(R/D)^A``.  The zero numerator at ``r=1`` is excluded.
    """

    lengths = (
        outer_length,
        shift_length,
        denominator_length,
        target,
    )
    if min(lengths) < 0:
        raise ValueError("all length exponents must be nonnegative")
    if denominator_length > shift_length:
        raise ValueError("this ledger is for nonzero modes with R<=D")
    if fourier_decay_order < 0:
        raise ValueError("the Fourier decay order must be nonnegative")

    outer_large_sieve = max(outer_length, 2 * denominator_length)
    shift_large_sieve = max(shift_length, 2 * denominator_length)
    fourier_decay = fourier_decay_order * (
        denominator_length - shift_length
    )
    bound = (
        -denominator_length
        + outer_length / 2
        + shift_length / 2
        + outer_large_sieve / 2
        + shift_large_sieve / 2
        + fourier_decay
    )
    return NonzeroReducedDenominatorLedger(
        coefficient_weight=-denominator_length,
        outer_energy=outer_length,
        shift_energy=shift_length,
        outer_large_sieve_constant=outer_large_sieve,
        shift_large_sieve_constant=shift_large_sieve,
        fourier_decay=fourier_decay,
        bound=bound,
        target=target,
        margin=target - bound,
    )


def high_reduced_denominator_ledger(
    *,
    ambient_length: Fraction,
    shift_length: Fraction,
    reduced_denominator: Fraction,
) -> HighReducedDenominatorLedger:
    """Ambient top-face geometry of the ``r>D`` small-numerator modes.

    Write a complementary product as ``m=r*v``.  Smooth shift
    completion restricts a primitive reduced numerator ``u`` to
    ``u <= r/D``.  This legacy ledger puts ``m`` on its maximal face
    ``m=S``, so ``v<=S/r`` and the lifted full-modulus numerator
    ``a_R=u*v`` has length ``S/D``.  For an individual quotient block
    ``m=S/k``, use :func:`high_edge_polytope_ledger`; the exact sum of
    the two short exponents is then ``log_T(S/(kD))``.
    """

    lengths = (ambient_length, shift_length, reduced_denominator)
    if min(lengths) < 0:
        raise ValueError("all length exponents must be nonnegative")
    if not shift_length <= reduced_denominator <= ambient_length:
        raise ValueError("require D <= r <= S on the exponent scale")
    reduced_numerator = reduced_denominator - shift_length
    complementary_cofactor = ambient_length - reduced_denominator
    return HighReducedDenominatorLedger(
        reduced_denominator=reduced_denominator,
        reduced_numerator=reduced_numerator,
        complementary_cofactor=complementary_cofactor,
        lifted_numerator=(
            reduced_numerator + complementary_cofactor
        ),
    )


def high_edge_polytope_ledger(
    *,
    ambient_length: Fraction,
    shift_length: Fraction,
    complementary_quotient: Fraction,
    reduced_denominator: Fraction,
    target: Fraction,
) -> HighEdgePolytopeLedger:
    """Quotient-aware geometry and elementary high-edge gap.

    The complementary product has length ``S/k`` rather than always
    length ``S``.  If ``m=r*v`` and the small reduced numerator has
    length ``r/D``, then the two exponents add to ``m/D``.  The
    additive large sieve without Fourier decay is recorded exactly,
    as is the hypothetical saving from square-root cancellation in
    both of these artificial gcd coordinates.
    """

    lengths = (
        ambient_length,
        shift_length,
        complementary_quotient,
        reduced_denominator,
        target,
    )
    if min(lengths) < 0:
        raise ValueError("all length exponents must be nonnegative")
    product_length = ambient_length - complementary_quotient
    if product_length < shift_length:
        raise ValueError("the complementary product must exceed D")
    if not shift_length <= reduced_denominator <= product_length:
        raise ValueError("require D <= r <= m on the exponent scale")

    ramanujan_cofactor = product_length - reduced_denominator
    reduced_numerator = reduced_denominator - shift_length
    full_modulus_numerator = product_length - shift_length
    outer_large_sieve = max(ambient_length, 2 * reduced_denominator)
    shift_large_sieve = max(shift_length, 2 * reduced_denominator)
    large_sieve_bound = (
        -reduced_denominator
        + ambient_length / 2
        + shift_length / 2
        + outer_large_sieve / 2
        + shift_large_sieve / 2
    )
    large_sieve_gap = large_sieve_bound - target
    square_root_hybrid_saving = (
        ramanujan_cofactor + reduced_numerator
    ) / 2
    return HighEdgePolytopeLedger(
        complementary_quotient=complementary_quotient,
        product_length=product_length,
        reduced_denominator=reduced_denominator,
        ramanujan_cofactor=ramanujan_cofactor,
        reduced_numerator=reduced_numerator,
        full_modulus_numerator=full_modulus_numerator,
        large_sieve_bound=large_sieve_bound,
        target=target,
        large_sieve_gap=large_sieve_gap,
        square_root_hybrid_saving=square_root_hybrid_saving,
        square_root_hybrid_margin=(
            square_root_hybrid_saving - large_sieve_gap
        ),
    )


def high_reduced_frequency_lifts(
    *,
    modulus: int,
    denominator_cutoff: int,
) -> tuple[ReducedFrequencyLift, ...]:
    """Regroup reduced Ramanujan modes by their full-modulus numerator.

    For ``r|m``, put ``v=m/r`` and lift a primitive ``u mod r`` to
    ``a_R=u*v mod m``.  This is a bijection onto the nonzero residues
    whose reduced denominator ``m/gcd(a_R,m)`` exceeds the cutoff.
    """

    if modulus < 1 or denominator_cutoff < 1:
        raise ValueError("the modulus and cutoff must be positive")
    lifts = tuple(
        ReducedFrequencyLift(
            reduced_denominator=reduced_denominator,
            primitive_numerator=primitive_numerator,
            cofactor=modulus // reduced_denominator,
            full_numerator=(
                primitive_numerator * (modulus // reduced_denominator)
            ),
        )
        for reduced_denominator in divisors(modulus)
        if reduced_denominator > denominator_cutoff
        for primitive_numerator in range(1, reduced_denominator)
        if gcd(primitive_numerator, reduced_denominator) == 1
    )
    return tuple(sorted(lifts, key=lambda lift: lift.full_numerator))


def mobius_convolution_rational_proxy_ledger(
    *,
    product_length: Fraction,
    denominator_length: Fraction,
    required_saving: Fraction,
) -> MobiusConvolutionRationalProxyLedger:
    """Dong--Robles--Zaharescu--Zeindler ``mu*mu`` proxy.

    Their three terms save ``q^(1/4)``, ``X^(1/7)``, and
    ``(X/q)^(1/4)`` relative to length ``X``.  The minimum is the
    available uniform saving.  It is only a proxy here: selecting
    ``r|bc`` makes the phase at ``u/r`` resonant, so the complete
    convolution theorem does not estimate the actual coefficient.
    """

    lengths = (product_length, denominator_length, required_saving)
    if min(lengths) < 0:
        raise ValueError("all exponents must be nonnegative")
    if denominator_length > product_length:
        raise ValueError("the rational denominator cannot exceed X")
    denominator_term_saving = denominator_length / 4
    interior_term_saving = product_length / 7
    upper_denominator_term_saving = (
        product_length - denominator_length
    ) / 4
    available_saving = min(
        denominator_term_saving,
        interior_term_saving,
        upper_denominator_term_saving,
    )
    return MobiusConvolutionRationalProxyLedger(
        product_length=product_length,
        denominator_length=denominator_length,
        denominator_term_saving=denominator_term_saving,
        interior_term_saving=interior_term_saving,
        upper_denominator_term_saving=upper_denominator_term_saving,
        available_saving=available_saving,
        required_saving=required_saving,
        margin=available_saving - required_saving,
        structurally_applicable=False,
    )


def reciprocal_monomial_coverage_ledger(
    *,
    full_modulus_numerator: Fraction,
    phase_variation: Fraction,
) -> ReciprocalMonomialCoverageLedger:
    """Best possible margin from the published monomial-sum shape.

    On the theta-three edge the raw scalar form needs the fixed
    half-power plus the complete numerator length.  Robert--Sargos and
    Fouvry--Iwaniec contain an ``X^(-1/2)`` term, so their displayed
    arbitrary-coefficient bounds can guarantee at most half the phase
    variation, even before coefficient-norm losses are restored.
    """

    if min(full_modulus_numerator, phase_variation) < 0:
        raise ValueError("all exponents must be nonnegative")
    required_saving = full_modulus_numerator + Fraction(1, 2)
    published_saving_cap = phase_variation / 2
    margin = published_saving_cap - required_saving
    return ReciprocalMonomialCoverageLedger(
        full_modulus_numerator=full_modulus_numerator,
        phase_variation=phase_variation,
        required_saving=required_saving,
        published_saving_cap=published_saving_cap,
        margin=margin,
        covered=(margin >= 0),
    )


def coupled_product_circle_ledger(
    *,
    complementary_left: Fraction,
    complementary_right: Fraction,
    quotient_length: Fraction,
    circle_denominator: Fraction,
    quotient_gcd: Fraction,
    target: Fraction,
) -> CoupledProductCircleLedger:
    """Precompletion dual-product Type-II bound at theta three.

    After exact numerator completion and the long--long Möbius split,
    the determinant equation is ``b*c*k-g*q=d``.  On a circle band
    ``|alpha|=T^(-a)``, DRZZ Lemma 4.2 applies separately to the
    ``b*c`` polynomial at frequency ``alpha*k`` and to the ``g*q``
    polynomial at frequency ``-alpha``.  If
    ``(k,q_alpha)=T^tau``, multiplication by ``k`` reduces the rational
    denominator and introduces the exact Diophantine loss
    ``max(0,kappa-2*tau)``.  This ledger includes the size of that gcd
    stratum and the L1 mass ``T^(2-a)`` of the smooth d-kernel.

    The comparison Cauchy bound keeps the product coefficient intact;
    restricting ``k`` to the gcd stratum lowers its L2 energy by
    ``T^(-tau/2)``.  Neither entry uses unproved Möbius cancellation.
    """

    lengths = (
        complementary_left,
        complementary_right,
        quotient_length,
        circle_denominator,
        quotient_gcd,
        target,
    )
    if min(lengths) < 0:
        raise ValueError("all exponents must be nonnegative")
    ambient_length = Fraction(3)
    shift_length = Fraction(2)
    complementary_product = (
        complementary_left + complementary_right
    )
    if complementary_product + quotient_length != ambient_length:
        raise ValueError("require beta+gamma+kappa=3")
    if min(complementary_left, complementary_right) < 1:
        raise ValueError("the endpoint Type-II factors must be at least T")
    if not shift_length <= circle_denominator <= ambient_length:
        raise ValueError("the near-zero circle denominator lies in [2,3]")
    if quotient_gcd > min(quotient_length, circle_denominator):
        raise ValueError("the gcd exponent cannot exceed kappa or a")

    effective_denominator = circle_denominator - quotient_gcd
    approximation_loss = max(
        Fraction(0), quotient_length - 2 * quotient_gcd
    )
    complementary_type_ii_constant = max(
        complementary_product
        - effective_denominator
        + approximation_loss,
        complementary_left,
        complementary_right,
        effective_denominator,
    )
    shifted_type_ii_constant = max(
        ambient_length - circle_denominator,
        Fraction(1, 2),
        Fraction(5, 2),
        circle_denominator,
    )
    quotient_stratum = quotient_length - quotient_gcd
    circle_kernel_mass = shift_length - circle_denominator
    pointwise_bound = (
        quotient_stratum
        + (
            complementary_product
            + complementary_type_ii_constant
        )
        / 2
        + (ambient_length + shifted_type_ii_constant) / 2
        + circle_kernel_mass
    )
    cauchy_bound = (
        (ambient_length - quotient_gcd) / 2
        + ambient_length / 2
        + shift_length
    )
    best_bound = min(pointwise_bound, cauchy_bound)
    margin = target - best_bound
    return CoupledProductCircleLedger(
        complementary_left=complementary_left,
        complementary_right=complementary_right,
        quotient_length=quotient_length,
        complementary_product=complementary_product,
        circle_denominator=circle_denominator,
        quotient_gcd=quotient_gcd,
        effective_denominator=effective_denominator,
        approximation_loss=approximation_loss,
        complementary_type_ii_constant=(
            complementary_type_ii_constant
        ),
        shifted_type_ii_constant=shifted_type_ii_constant,
        quotient_stratum=quotient_stratum,
        circle_kernel_mass=circle_kernel_mass,
        pointwise_bound=pointwise_bound,
        cauchy_bound=cauchy_bound,
        best_bound=best_bound,
        target=target,
        margin=margin,
        covered=(margin >= 0),
    )


def shifted_divisor_proxy_ledger(
    *,
    ambient_length: Fraction,
    shift_length: Fraction,
    exceptional_exponent: Fraction,
    target: Fraction,
) -> ShiftedDivisorProxyLedger:
    """Audit the closest published ``d_3``--``d_2`` shift estimates.

    Topacogullari's fixed-shift error is
    ``X^(5/6+theta/3)``.  Summing a shift block of length ``D`` adds
    its full exponent.  The first-moment theorem of Baier--Browning--
    Marasingha--Zhao instead has errors ``D^2`` and
    ``D^(1/2) X^(13/12)``.  These formulas are exponent proxies only:
    the packet here has dyadically truncated Möbius convolutions rather
    than the standard divisor coefficients required by those theorems.

    The raw zero-frequency contribution has scale ``D*X`` and does not
    vanish as a finite identity, so numerical error-term coverage alone
    cannot close the packet.
    """

    lengths = (
        ambient_length,
        shift_length,
        exceptional_exponent,
        target,
    )
    if min(lengths) < 0:
        raise ValueError("all exponents must be nonnegative")

    fixed_shift_error = ambient_length * (
        Fraction(5, 6) + exceptional_exponent / 3
    )
    summed_fixed_shift_error = shift_length + fixed_shift_error
    selberg_endpoint = shift_length + 5 * ambient_length / 6
    averaged_shift_square_error = 2 * shift_length
    averaged_shift_moment_error = (
        shift_length / 2 + 13 * ambient_length / 12
    )
    averaged_shift_error = max(
        averaged_shift_square_error,
        averaged_shift_moment_error,
    )
    raw_zero_mode = ambient_length + shift_length
    standard_divisor_coefficients = False
    zero_mode_algebraically_vanishing = False
    return ShiftedDivisorProxyLedger(
        fixed_shift_error=fixed_shift_error,
        summed_fixed_shift_error=summed_fixed_shift_error,
        summed_fixed_shift_margin=target - summed_fixed_shift_error,
        selberg_endpoint=selberg_endpoint,
        averaged_shift_square_error=averaged_shift_square_error,
        averaged_shift_moment_error=averaged_shift_moment_error,
        averaged_shift_error=averaged_shift_error,
        averaged_shift_margin=target - averaged_shift_error,
        raw_zero_mode=raw_zero_mode,
        zero_mode_required_saving=raw_zero_mode - target,
        standard_divisor_coefficients=standard_divisor_coefficients,
        zero_mode_algebraically_vanishing=(
            zero_mode_algebraically_vanishing
        ),
        covered=(
            averaged_shift_error <= target
            and standard_divisor_coefficients
            and zero_mode_algebraically_vanishing
        ),
    )


def shifted_product_packet_sides(
    *,
    b_weights: tuple[tuple[int, int], ...],
    c_weights: tuple[tuple[int, int], ...],
    k_weights: tuple[tuple[int, int], ...],
    g_weights: tuple[tuple[int, int], ...],
    q_weights: tuple[tuple[int, int], ...],
    shift_weights: tuple[tuple[int, int], ...],
) -> tuple[int, int]:
    """Return both sides of the finite ``3 by 2`` shift identity.

    Extending the shift weight by zero outside its listed support gives

    ``sum b*c*k*g*q*z(b*c*k-g*q)``
    ``= sum_d z(d) sum_n A(n) C(n-d)``,

    where ``A`` is the three-factor product convolution and ``C`` the
    two-factor product convolution.  The integer weights can include
    Möbius signs and arbitrary finite smooth-weight samples.
    """

    factor_families = (
        b_weights,
        c_weights,
        k_weights,
        g_weights,
        q_weights,
    )
    if any(index < 1 for family in factor_families for index, _ in family):
        raise ValueError("product indices must be positive")
    if len({shift for shift, _ in shift_weights}) != len(shift_weights):
        raise ValueError("shift indices must be unique")
    shift_map = dict(shift_weights)

    direct = sum(
        b_weight
        * c_weight
        * k_weight
        * g_weight
        * q_weight
        * shift_map.get(b * c * k - g * q, 0)
        for b, b_weight in b_weights
        for c, c_weight in c_weights
        for k, k_weight in k_weights
        for g, g_weight in g_weights
        for q, q_weight in q_weights
    )

    left: dict[int, int] = {}
    for b, b_weight in b_weights:
        for c, c_weight in c_weights:
            for k, k_weight in k_weights:
                product = b * c * k
                left[product] = left.get(product, 0) + (
                    b_weight * c_weight * k_weight
                )
    right: dict[int, int] = {}
    for g, g_weight in g_weights:
        for q, q_weight in q_weights:
            product = g * q
            right[product] = right.get(product, 0) + g_weight * q_weight

    correlation = sum(
        shift_weight
        * left_weight
        * right.get(product - shift, 0)
        for shift, shift_weight in shift_weights
        for product, left_weight in left.items()
    )
    return direct, correlation


def shifted_product_zero_mode_sides(
    *,
    b_weights: tuple[tuple[int, int], ...],
    c_weights: tuple[tuple[int, int], ...],
    k_weights: tuple[tuple[int, int], ...],
    g_weights: tuple[tuple[int, int], ...],
    q_weights: tuple[tuple[int, int], ...],
    shift_weights: tuple[tuple[int, int], ...],
) -> tuple[int, int]:
    """Return expanded and factored zero modes of the product packet."""

    direct = sum(
        b_weight
        * c_weight
        * k_weight
        * g_weight
        * q_weight
        * shift_weight
        for _, b_weight in b_weights
        for _, c_weight in c_weights
        for _, k_weight in k_weights
        for _, g_weight in g_weights
        for _, q_weight in q_weights
        for _, shift_weight in shift_weights
    )
    factored = (
        sum(weight for _, weight in b_weights)
        * sum(weight for _, weight in c_weights)
        * sum(weight for _, weight in k_weights)
        * sum(weight for _, weight in g_weights)
        * sum(weight for _, weight in q_weights)
        * sum(weight for _, weight in shift_weights)
    )
    return direct, factored


def multiple_mobius_additive_ledger(
    *,
    ambient_length: Fraction,
    shift_length: Fraction,
    complementary_quotient: Fraction,
    target: Fraction,
) -> MultipleMobiusAdditiveLedger:
    """Nearest Banks--Shparlinski scale after fixing ``k``.

    In ``k*m-d-s=0`` the product variable has length ``S/k``.  Their
    short-interval theorem, with ``d`` in the weighted variable so its
    extra Möbius factor can be removed on squarefree coprime layers,
    gives ``(M+D)S`` schematically for fixed ``k``.  On exponent scale
    this is ``max(M,D)+S``; summing the dyadic k-block adds ``k``.
    """

    lengths = (
        ambient_length,
        shift_length,
        complementary_quotient,
        target,
    )
    if min(lengths) < 0:
        raise ValueError("all length exponents must be nonnegative")
    product_length = ambient_length - complementary_quotient
    if product_length < 0:
        raise ValueError("the complementary quotient cannot exceed S")
    fixed_bound = max(product_length, shift_length) + ambient_length
    summed_bound = fixed_bound + complementary_quotient
    return MultipleMobiusAdditiveLedger(
        product_length=product_length,
        fixed_quotient_bound=fixed_bound,
        summed_bound=summed_bound,
        target=target,
        gap=summed_bound - target,
    )


def postcompletion_cutoff_ledger(
    *,
    ambient_length: Fraction,
    shift_length: Fraction,
    outer_length: Fraction,
    left_cutoff: Fraction,
    right_cutoff: Fraction,
    fourier_decay_order: int,
    target: Fraction,
) -> PostcompletionCutoffLedger:
    """Cutoff geometry after completing the transition numerator.

    For ``m=bc<D``, smooth Poisson summation in the shift variable makes
    the nonzero frequency tail ``(m/D)^(A-1)``.  The sharp endpoint cost
    is retained separately.  The long-long complementary divisor
    ``k=n/m`` has the two displayed ceilings.
    """

    lengths = (
        ambient_length,
        shift_length,
        outer_length,
        left_cutoff,
        right_cutoff,
        target,
    )
    if min(lengths) < 0:
        raise ValueError("all length exponents must be nonnegative")
    if fourier_decay_order < 1:
        raise ValueError("the Fourier decay order must be positive")
    divisor_product = left_cutoff + right_cutoff
    if divisor_product > shift_length:
        raise ValueError("this Poisson ledger requires bc no longer than D")
    quotient_ceiling = ambient_length - divisor_product
    if quotient_ceiling < 0 or ambient_length < shift_length:
        raise ValueError("the ambient interval must contain the shift range")
    sharp_boundary = outer_length + divisor_product
    smooth_tail = (
        sharp_boundary
        + (fourier_decay_order - 1)
        * (divisor_product - shift_length)
    )
    return PostcompletionCutoffLedger(
        divisor_product_floor=divisor_product,
        quotient_ceiling=quotient_ceiling,
        fixed_product_quotient_window=max(
            Fraction(0), shift_length - divisor_product
        ),
        high_product_quotient_ceiling=ambient_length - shift_length,
        sharp_type_i_boundary=sharp_boundary,
        smooth_type_i_tail=smooth_tail,
        sharp_margin=target - sharp_boundary,
        smooth_margin=target - smooth_tail,
    )


def centered_low_modulus_large_sieve_ledger(
    *,
    modulus_length: Fraction,
    outer_length: Fraction,
    shift_length: Fraction,
    fourier_decay_order: int,
    target: Fraction,
) -> CenteredLowModulusLargeSieveLedger:
    """Additive-large-sieve bound for a centered ``m<=D`` block.

    The coefficient and outer L2 energies have exponents ``M`` and
    ``S``.  Fractions ``k/m`` contribute the classical ``S+M^2`` large
    sieve constant, while smooth Poisson modes gain
    ``(M/D)^(A-1)``.
    """

    lengths = (modulus_length, outer_length, shift_length, target)
    if min(lengths) < 0:
        raise ValueError("all length exponents must be nonnegative")
    if modulus_length > shift_length:
        raise ValueError("the centered low-modulus block requires M<=D")
    if fourier_decay_order < 1:
        raise ValueError("the Fourier decay order must be positive")
    large_sieve_constant = max(outer_length, 2 * modulus_length)
    fourier_decay = (
        fourier_decay_order - 1
    ) * (modulus_length - shift_length)
    bound = (
        modulus_length / 2
        + outer_length / 2
        + large_sieve_constant / 2
        + fourier_decay
    )
    return CenteredLowModulusLargeSieveLedger(
        coefficient_energy=modulus_length,
        outer_energy=outer_length,
        large_sieve_constant=large_sieve_constant,
        fourier_decay=fourier_decay,
        bound=bound,
        target=target,
        margin=target - bound,
    )


def asymptotic_sieve_transition_ledger(
    *,
    ambient_length: Fraction,
    distribution_level: Fraction,
    complementary_quotient: Fraction,
    short_divisor_cutoff: Fraction,
) -> AsymptoticSieveTransitionLedger:
    """Map the complementary divisor face to FI's sieve parameters.

    This ledger checks only the exponent syntax of Friedlander--Iwaniec
    conditions (B1)--(B3).  Their bilinear condition (B) is an input
    axiom, not a conclusion of the asymptotic sieve theorem.
    """

    lengths = (
        ambient_length,
        distribution_level,
        complementary_quotient,
        short_divisor_cutoff,
    )
    if min(lengths) < 0:
        raise ValueError("all exponents must be nonnegative")
    if distribution_level > ambient_length:
        raise ValueError("the distribution level cannot exceed x")
    square_root_level = distribution_level / 2
    square_root_ambient = ambient_length / 2
    b3_ceiling = ambient_length - distribution_level
    return AsymptoticSieveTransitionLedger(
        square_root_level=square_root_level,
        square_root_ambient=square_root_ambient,
        complementary_quotient=complementary_quotient,
        b3_coefficient_ceiling=b3_ceiling,
        short_divisor_cutoff=short_divisor_cutoff,
        quotient_at_lower_endpoint=(
            complementary_quotient == square_root_level
        ),
        cutoff_inside_b3_ceiling=(short_divisor_cutoff <= b3_ceiling),
    )


def complementary_one_factor_coverage_ledger(
    *,
    ambient_length: Fraction,
    shift_length: Fraction,
    other_long_factor_floor: Fraction,
    theorem_short_interval_ratio: Fraction,
) -> ComplementaryOneFactorCoverageLedger:
    """Test a one-factor all-interval theorem on the complementary face."""

    lengths = (ambient_length, shift_length, other_long_factor_floor)
    if min(lengths) < 0:
        raise ValueError("all length exponents must be nonnegative")
    if not 0 <= theorem_short_interval_ratio < 1:
        raise ValueError("the short-interval ratio must lie in [0,1)")
    if shift_length > ambient_length:
        raise ValueError("the shift cannot exceed the ambient length")
    maximum_factor = ambient_length - other_long_factor_floor
    # Fixing the other factor and the complementary quotient leaves a
    # Mobius interval of T-exponent beta-(ambient-shift).  Requiring this
    # to be at least beta*theta gives beta >= (ambient-shift)/(1-theta).
    required_factor = (
        ambient_length - shift_length
    ) / (1 - theorem_short_interval_ratio)
    return ComplementaryOneFactorCoverageLedger(
        maximum_factor_length=maximum_factor,
        required_factor_length=required_factor,
        coverage_gap=required_factor - maximum_factor,
        covered=(maximum_factor >= required_factor),
    )


def scalar_type_ii_cutoff_ledger(
    *,
    r_length: Fraction,
    reduced_modulus: Fraction,
    scalar_length: Fraction,
    shift_length: Fraction,
    left_cutoff: Fraction,
    right_cutoff: Fraction,
) -> ScalarTypeIICutoffLedger:
    """Exponent geometry after ``r=bc*k`` in the long-long packet."""

    if min(
        r_length,
        reduced_modulus,
        scalar_length,
        shift_length,
        left_cutoff,
        right_cutoff,
    ) < 0:
        raise ValueError("all exponent lengths must be nonnegative")
    divisor_product_floor = left_cutoff + right_cutoff
    quotient_ceiling = r_length - divisor_product_floor
    if quotient_ceiling < 0:
        raise ValueError("the divisor product cannot exceed r")
    return ScalarTypeIICutoffLedger(
        divisor_product_floor=divisor_product_floor,
        divisor_product_vs_scalar=(
            divisor_product_floor - scalar_length
        ),
        quotient_ceiling=quotient_ceiling,
        fixed_divisor_quotient_window=max(
            Fraction(0),
            shift_length - divisor_product_floor,
        ),
        rational_distance=(
            shift_length
            - divisor_product_floor
            - reduced_modulus
        ),
    )


def near_determinant_bettin_chandee_ledger(
    *,
    long_numerator: Fraction,
    long_modulus: Fraction,
    product_length: Fraction,
    scalar_coefficient_cost: Fraction,
    target: Fraction,
) -> NearDeterminantBCLedger:
    """Audit BC after the near-window weight is Fourier-separated.

    The long numerator coefficient, modulus coefficient, and product
    coefficient are charged by their square-root counting norms.  The
    optional scalar cost records what remains in the modulus coefficient.
    """

    if min(
        long_numerator,
        long_modulus,
        product_length,
        scalar_coefficient_cost,
        target,
    ) < 0:
        raise ValueError("all exponent lengths must be nonnegative")
    geometric_sum = long_numerator + long_modulus + product_length
    longest_variable = max(long_numerator, long_modulus)
    coefficient_norm = (
        geometric_sum / 2 + scalar_coefficient_cost
    )
    first_parenthetical = (
        Fraction(7, 20) * geometric_sum + longest_variable / 4
    )
    second_parenthetical = (
        Fraction(3, 8) * geometric_sum
        + (product_length + longest_variable) / 8
    )
    large_phase_penalty = max(
        Fraction(0),
        (product_length - long_numerator - long_modulus) / 2,
    )
    theorem_bound = (
        coefficient_norm
        + min(first_parenthetical, second_parenthetical)
        + large_phase_penalty
    )
    return NearDeterminantBCLedger(
        coefficient_norm=coefficient_norm,
        first_parenthetical=first_parenthetical,
        second_parenthetical=second_parenthetical,
        large_phase_penalty=large_phase_penalty,
        theorem_bound=theorem_bound,
        target=target,
        gap=theorem_bound - target,
    )


def partially_fixed_modulus_ledger(
    *,
    long_modulus: Fraction,
    quotient: Fraction,
    fixed_divisor: Fraction,
    product_numerator: Fraction,
    short_factor_triangle: Fraction,
    target: Fraction,
) -> PartiallyFixedModulusLedger:
    """Audit Wright's 2026 partially fixed-modulus theorem.

    Reciprocity maps ``e_q(-A*inverse(B*k))`` to the theorem with
    ``M=q``, ``N=k`` and fixed denominator factor ``R=B``.  The near
    determinant has already been Fourier-separated in this ledger, so
    its density is unavailable.  The third term uses the weaker
    ``A^(-1/20)`` printed in the theorem statement; the proof displays
    a stronger power, but that discrepancy does not select the maximum.
    """

    values = (
        long_modulus,
        quotient,
        fixed_divisor,
        product_numerator,
        short_factor_triangle,
        target,
    )
    if min(values) < 0:
        raise ValueError("all exponent inputs must be nonnegative")

    coefficient_norm = (
        long_modulus + quotient + product_numerator
    ) / 2
    geometric_factor = coefficient_norm
    fixed_factor = fixed_divisor / 4
    first_term = -quotient / 8
    second_term = (
        fixed_divisor / 8 + quotient / 8 - long_modulus / 4
    )
    third_term = (
        long_modulus / 10
        - 3 * fixed_divisor / 20
        - product_numerator / 20
        - 3 * quotient / 20
    )
    fourth_term = (
        3 * quotient / 20
        - 3 * product_numerator / 20
        - long_modulus / 5
    )
    fifth_term = 3 * quotient / 8 - long_modulus / 2
    fixed_block_bound = (
        coefficient_norm
        + geometric_factor
        + fixed_factor
        + max(first_term, second_term, third_term, fourth_term, fifth_term)
    )
    global_bound = fixed_block_bound + short_factor_triangle
    return PartiallyFixedModulusLedger(
        coefficient_norm=coefficient_norm,
        geometric_factor=geometric_factor,
        fixed_factor=fixed_factor,
        first_term=first_term,
        second_term=second_term,
        third_term=third_term,
        fourth_term=fourth_term,
        fifth_term=fifth_term,
        fixed_block_bound=fixed_block_bound,
        global_bound=global_bound,
        target=target,
        gap=global_bound - target,
    )


def mobius_character_mean_square_ledger(
    *,
    progression_modulus: Fraction,
    scalar_length: Fraction,
    long_length: Fraction,
    required_saving: Fraction,
) -> MobiusCharacterMeanSquareLedger:
    """Screen the character route on the affine endpoint packet.

    The progression density removes the count of moduli B before
    cancellation, so Bombieri--Vinogradov supplies logarithmic but no
    power saving.  After the principal and induced spectra have been
    separated, the displayed character energies are the optimistic
    primitive-character large-sieve exponents with dyadic 1/B
    normalization.
    """

    values = (
        progression_modulus,
        scalar_length,
        long_length,
        required_saving,
    )
    if min(values) < 0:
        raise ValueError("all exponent inputs must be nonnegative")

    raw_progression_bound = (
        progression_modulus
        + scalar_length
        + max(Fraction(0), long_length - progression_modulus)
    )
    bombieri_vinogradov_bound = scalar_length + long_length
    short_character_energy = (
        -progression_modulus
        + max(2 * progression_modulus, scalar_length)
        + scalar_length
    )
    long_character_energy = (
        -progression_modulus
        + max(2 * progression_modulus, long_length)
        + long_length
    )
    ordinary_large_sieve_bound = (
        short_character_energy + long_character_energy
    ) / 2
    required_bound = raw_progression_bound - required_saving
    ordinary_saving = raw_progression_bound - ordinary_large_sieve_bound
    required_long_character_energy = (
        2 * required_bound - short_character_energy
    )
    return MobiusCharacterMeanSquareLedger(
        raw_progression_bound=raw_progression_bound,
        bombieri_vinogradov_bound=bombieri_vinogradov_bound,
        short_character_energy=short_character_energy,
        long_character_energy=long_character_energy,
        ordinary_large_sieve_bound=ordinary_large_sieve_bound,
        required_bound=required_bound,
        ordinary_saving=ordinary_saving,
        required_saving=required_saving,
        gap=ordinary_large_sieve_bound - required_bound,
        required_long_character_energy=required_long_character_energy,
    )


def prime_kloosterman_average_ledger(
    *,
    modulus: Fraction,
    prime_length: Fraction,
    required_saving: Fraction,
) -> PrimeKloostermanLedger:
    """Audit Irving's averaged Kloosterman-over-primes theorem."""

    if min(modulus, prime_length, required_saving) < 0:
        raise ValueError("all exponent inputs must be nonnegative")
    if not 2 * modulus / 3 <= prime_length <= 3 * modulus / 2:
        raise ValueError("the theorem requires Q^(2/3) <= x <= Q^(3/2)")

    first_term = 5 * modulus / 4 + 5 * prime_length / 8
    second_term = modulus + 9 * prime_length / 10
    third_term = 7 * modulus / 6 + 13 * prime_length / 18
    theorem_bound = max(first_term, second_term, third_term)
    trivial_bound = modulus + prime_length
    theorem_saving = trivial_bound - theorem_bound
    return PrimeKloostermanLedger(
        first_term=first_term,
        second_term=second_term,
        third_term=third_term,
        theorem_bound=theorem_bound,
        trivial_bound=trivial_bound,
        theorem_saving=theorem_saving,
        required_saving=required_saving,
        gap=required_saving - theorem_saving,
    )


def prime_slice_variance_ledger(
    *,
    ambient_length: Fraction,
    shift_length: Fraction,
    scalar_length: Fraction,
) -> PrimeSliceVarianceLedger:
    """Audit Selberg variance and the density term on the prime slice.

    The interval has ambient scale ``x = T^ambient_length`` and length
    ``y = T^shift_length``.  The transition needs the scalar saving
    ``T^scalar_length``.  The unconditional Selberg-integral input used
    here is ``J(x, y/x) << x*y^2``; the RH diagnostic is ``J << x*y``.
    """

    if ambient_length <= 0:
        raise ValueError("the ambient exponent must be positive")
    if min(shift_length, scalar_length) < 0:
        raise ValueError("all exponent inputs must be nonnegative")
    if shift_length > ambient_length:
        raise ValueError("the short interval cannot exceed the ambient scale")
    if scalar_length > ambient_length:
        raise ValueError("the requested scalar saving exceeds the ambient scale")

    relative_interval = shift_length - ambient_length
    trivial_bound = ambient_length + shift_length
    target_bound = trivial_bound - scalar_length
    unconditional_variance = ambient_length + 2 * shift_length
    unconditional_cauchy_bound = (
        ambient_length + unconditional_variance
    ) / 2
    rh_variance = ambient_length + shift_length
    rh_cauchy_bound = (ambient_length + rh_variance) / 2
    density_required_mertens = target_bound - shift_length
    return PrimeSliceVarianceLedger(
        relative_interval=relative_interval,
        trivial_bound=trivial_bound,
        target_bound=target_bound,
        unconditional_variance=unconditional_variance,
        unconditional_cauchy_bound=unconditional_cauchy_bound,
        unconditional_gap=unconditional_cauchy_bound - target_bound,
        rh_variance=rh_variance,
        rh_cauchy_bound=rh_cauchy_bound,
        rh_margin=target_bound - rh_cauchy_bound,
        density_required_mertens=density_required_mertens,
        density_required_ratio=density_required_mertens / ambient_length,
        density_required_saving=ambient_length - density_required_mertens,
    )


def shifted_prime_mobius_ledger(
    *,
    ambient_length: Fraction,
    shift_length: Fraction,
    scalar_length: Fraction,
) -> ShiftedPrimeMobiusLedger:
    """Audit a logarithmic averaged shifted-prime Möbius estimate."""

    if min(ambient_length, shift_length, scalar_length) < 0:
        raise ValueError("all exponent inputs must be nonnegative")
    if shift_length > ambient_length:
        raise ValueError("the shift range cannot exceed the ambient scale")

    raw_bound = ambient_length + shift_length
    target_bound = raw_bound - scalar_length
    published_power_bound = raw_bound
    published_power_saving = raw_bound - published_power_bound
    return ShiftedPrimeMobiusLedger(
        raw_bound=raw_bound,
        published_power_bound=published_power_bound,
        target_bound=target_bound,
        published_power_saving=published_power_saving,
        required_power_saving=scalar_length,
        gap=published_power_bound - target_bound,
    )


def shifted_prime_mobius_coordinates(
    *,
    base: int,
    shift: int,
    shift_range: int,
) -> ShiftedPrimeMobiusCoordinates:
    """Map mu(s) * Lambda(s+d) to mu(n+h) * G(n)."""

    if shift_range < 1 or not 1 <= shift <= shift_range:
        raise ValueError("the shift must lie in the positive shift range")
    if base <= shift_range:
        raise ValueError("the base must exceed the shift range")
    return ShiftedPrimeMobiusCoordinates(
        mobius_shift=shift_range - shift,
        translated_base=base + shift - shift_range,
    )


def transition_archimedean_scale_ledger(
    *,
    r: Fraction,
    s: Fraction,
    first_zeta: Fraction,
    second_zeta: Fraction,
    determinant: Fraction,
    numerator: Fraction,
    scalar: Fraction,
    reduced_determinant: Fraction,
    reduced_modulus: Fraction,
) -> TransitionArchimedeanScaleLedger:
    """Evaluate every dimensionless frequency in the actual kernel (5.13b).

    The fields are respectively the exponents of ``T*lambda0``,
    ``omega0``, ``chi0``, ``KS/(MR)``, ``g*delta0/L``, and ``H/q``.
    Zero in every field means that numerator completion samples a
    bounded Fourier coefficient of a fixed-scale weight; there is no
    residual power of ``T`` available for integration by parts.
    """

    values = (
        r,
        s,
        first_zeta,
        second_zeta,
        determinant,
        numerator,
        scalar,
        reduced_determinant,
        reduced_modulus,
    )
    if any(value < 0 for value in values):
        raise ValueError("all scale exponents must be nonnegative")
    return TransitionArchimedeanScaleLedger(
        logarithmic_phase=1 + determinant - first_zeta - r,
        numerator_fourier_center=numerator + first_zeta - s,
        afe_argument=2 * first_zeta + r - s - 1,
        zeta_balance=second_zeta + s - first_zeta - r,
        scalar_dilation=scalar + reduced_determinant - determinant,
        poisson_sample=numerator - reduced_modulus,
    )


def transition_numerator_completion_ledger(
    *,
    raw_bound: Fraction,
    numerator_length: Fraction,
    modulus: Fraction,
    numerator_sum_length: Fraction,
    target: Fraction,
) -> TransitionNumeratorCompletionLedger:
    """Audit Poisson completion in the transition numerator variable."""

    if min(
        raw_bound,
        numerator_length,
        modulus,
        numerator_sum_length,
        target,
    ) < 0:
        raise ValueError("all exponent inputs must be nonnegative")
    dual_length = max(modulus - numerator_sum_length, Fraction(0))
    numerator_saving = numerator_length - dual_length
    completed_bound = raw_bound - numerator_saving
    return TransitionNumeratorCompletionLedger(
        dual_length=dual_length,
        numerator_saving=numerator_saving,
        completed_bound=completed_bound,
        target=target,
        gap=completed_bound - target,
    )


def transition_numerator_dual_coordinates(
    *,
    modulus: int,
    determinant: int,
    numerator: int,
    dual_frequency: int,
) -> TransitionNumeratorDualCoordinates:
    """Resolve delta congruent to ell*d modulo q in the separated range."""

    if modulus < 1 or numerator < 1 or determinant == 0 or dual_frequency == 0:
        raise ValueError("the modulus and numerator must be positive and modes nonzero")
    if gcd(determinant, modulus) != 1:
        raise ValueError("the determinant must be a unit modulo the modulus")
    dilation = dual_frequency * determinant
    if modulus <= numerator + abs(dilation):
        raise ValueError("the modulus must separate the two integer representatives")
    if (dilation - numerator) % modulus != 0:
        raise ValueError("the dual congruence is not satisfied")
    if dilation != numerator:
        raise AssertionError("separation and congruence must force exact equality")
    return TransitionNumeratorDualCoordinates(
        dual_frequency=dual_frequency,
        determinant=determinant,
        numerator=numerator,
    )


def centered_transition_completion_ledger(
    *,
    modulus: Fraction,
    determinant_length: Fraction,
) -> CenteredTransitionCompletionLedger:
    """Compare the point mass and uniform mean after centered completion.

    The normalized numerator transform is
    ``1_{delta = ell*d (mod q)} - 1/phi(q)``.  On two intervals of
    exponent ``D<q``, the aligned point mass has exponent ``D`` while
    the uniform background has exponent ``2D-q``.  Their ratio is the
    exact missing scalar exponent ``q-D``.
    """

    if determinant_length < 0 or modulus <= determinant_length:
        raise ValueError("require nonnegative D exponent strictly below q")
    uniform_background = 2 * determinant_length - modulus
    return CenteredTransitionCompletionLedger(
        point_mass=determinant_length,
        uniform_background=uniform_background,
        point_over_background=modulus - determinant_length,
    )


def centered_transition_diagonal_mass(
    modulus: int,
    interval_length: int,
) -> Fraction:
    """Exact centered mass on ``delta=d`` inside a short initial box.

    For ``D<q`` the congruence ``delta=d (mod q)`` is literal equality.
    If ``U`` is the number of units up to ``D``, the completed centered
    kernel therefore has mass ``U-U^2/phi(q)``.  In particular it need
    not have zero additive-shift mean after restriction to the short box.
    """

    if modulus < 2 or not 1 <= interval_length < modulus:
        raise ValueError("require q>=2 and 1<=D<q")
    unit_count = sum(
        gcd(value, modulus) == 1
        for value in range(1, interval_length + 1)
    )
    return Fraction(unit_count) - Fraction(
        unit_count * unit_count,
        _euler_phi(modulus),
    )


def completed_transition_scalar_weighted_sum(
    *,
    modulus: int,
    shift: int,
    scalar_weights: tuple[tuple[int, complex], ...],
) -> tuple[complex, complex]:
    """Recombine all scalar signs after the transition phase disappears.

    For squarefree ``s`` and every ``g|s``, squarefreeness gives
    ``mu(g)*mu(s/g)=mu(s)``.  Thus arbitrary scalar-dependent weights
    form one divisor-incidence coefficient; they do not retain an
    independent Möbius sign.  The returned pair is the direct sum and
    its recombined form.
    """

    if modulus < 2 or mobius(modulus) == 0:
        raise ValueError("the completed scalar identity requires squarefree s")
    if modulus + shift < 1 or gcd(shift, modulus) != 1:
        raise ValueError("the shifted argument must be positive and coprime to s")
    scalar_factors = tuple(factor for factor, _weight in scalar_weights)
    if any(
        factor < 1 or modulus % factor != 0
        for factor in scalar_factors
    ):
        raise ValueError("every scalar factor must divide s")
    if len(set(scalar_factors)) != len(scalar_factors):
        raise ValueError("the scalar factors must be distinct")
    shifted_sign = mobius(modulus + shift)
    direct = sum(
        mobius(factor)
        * mobius(modulus // factor)
        * shifted_sign
        * weight
        for factor, weight in scalar_weights
    )
    recombined = (
        mobius(modulus)
        * shifted_sign
        * sum(weight for _factor, weight in scalar_weights)
    )
    return direct, recombined


def near_determinant_coordinates(
    divisor_product: int,
    scalar_factor: int,
    determinant: int,
    parameter: int,
) -> NearDeterminantCoordinates:
    """Parametrize all positive solutions of ``B*k-g*q=d``."""

    if min(divisor_product, scalar_factor, determinant) < 1:
        raise ValueError("the factors and determinant must be positive")
    if divisor_product == 1:
        raise ValueError("the audited transition divisor product exceeds one")
    if parameter < 0:
        raise ValueError("the affine parameter must be nonnegative")
    if gcd(divisor_product, scalar_factor) != 1:
        raise ValueError("B and g must be coprime")
    if gcd(determinant, divisor_product * scalar_factor) != 1:
        raise ValueError("d must be coprime to B*g")

    base_modulus = (
        -determinant * pow(scalar_factor, -1, divisor_product)
    ) % divisor_product
    if base_modulus == 0:
        raise AssertionError("coprimality forces a nonzero base modulus")
    base_quotient = (
        determinant + scalar_factor * base_modulus
    ) // divisor_product
    return NearDeterminantCoordinates(
        base_modulus=base_modulus,
        base_quotient=base_quotient,
        modulus=base_modulus + divisor_product * parameter,
        quotient=base_quotient + scalar_factor * parameter,
    )


def near_determinant_dual_coordinates(
    divisor_product: int,
    scalar_factor: int,
    determinant: int,
    parameter: int,
    dual_frequency: int,
    dual_quotient: int,
) -> NearDeterminantDualCoordinates:
    """Add the exact delta-Poisson lattice h+n*q=j*d."""

    coordinates = near_determinant_coordinates(
        divisor_product,
        scalar_factor,
        determinant,
        parameter,
    )
    numerator = (
        dual_quotient * determinant
        - dual_frequency * coordinates.modulus
    )
    return NearDeterminantDualCoordinates(
        modulus=coordinates.modulus,
        determinant_quotient=coordinates.quotient,
        numerator=numerator,
        dual_quotient=dual_quotient,
    )


def near_determinant_complete_reciprocal_sum(
    divisor_product: int,
    scalar_factor: int,
    determinant: int,
    numerator: int,
) -> complex:
    """Complete reciprocal core along one determinant solution line."""

    total = 0j
    for parameter in range(determinant):
        coordinates = near_determinant_coordinates(
            divisor_product,
            scalar_factor,
            determinant,
            parameter,
        )
        if gcd(coordinates.modulus, determinant) == 1:
            total += _inverse_additive_phase(
                determinant,
                numerator,
                coordinates.modulus,
            )
    return total


def near_determinant_reciprocal_parseval_sides(
    divisor_product: int,
    scalar_factor: int,
    determinant: int,
    weights: tuple[complex, ...],
) -> tuple[float, float]:
    """Both sides of Parseval for the complete affine reciprocal transform.

    Only parameters for which ``q=q0+B*t`` is a unit modulo ``d`` occur.
    Since ``B`` is a unit modulo ``d``, these ``q`` values are distinct,
    and inversion permutes their reduced residue classes.
    """

    if len(weights) != determinant:
        raise ValueError("one coefficient is required for each residue parameter")
    transforms: list[complex] = []
    retained_energy = 0.0
    for numerator in range(determinant):
        value = 0j
        for parameter, weight in enumerate(weights):
            modulus = near_determinant_coordinates(
                divisor_product,
                scalar_factor,
                determinant,
                parameter,
            ).modulus
            if gcd(modulus, determinant) != 1:
                continue
            value += weight * _inverse_additive_phase(
                determinant, numerator, modulus
            )
            if numerator == 0:
                retained_energy += abs(weight) ** 2
        transforms.append(value)
    return (
        sum(abs(value) ** 2 for value in transforms),
        determinant * retained_energy,
    )


def near_determinant_complete_delta_product_sum(
    divisor_product: int,
    scalar_factor: int,
    determinant: int,
    h_length: int,
    delta_length: int,
    weights: tuple[complex, ...],
) -> complex:
    """Direct complete-delta product box on the affine solution line."""

    if min(h_length, delta_length) < 1:
        raise ValueError("product-box lengths must be positive")
    if delta_length % determinant != 0:
        raise ValueError("the delta interval must contain complete d-periods")
    if len(weights) != determinant:
        raise ValueError("one coefficient is required for each residue parameter")
    total = 0j
    for parameter, weight in enumerate(weights):
        modulus = near_determinant_coordinates(
            divisor_product,
            scalar_factor,
            determinant,
            parameter,
        ).modulus
        if gcd(modulus, determinant) != 1:
            continue
        inverse = pow(modulus, -1, determinant)
        total += weight * sum(
            cmath.exp(
                2j
                * cmath.pi
                * ((h * delta * inverse) % determinant)
                / determinant
            )
            for h in range(1, h_length + 1)
            for delta in range(1, delta_length + 1)
        )
    return total


def near_determinant_complete_delta_product_formula(
    divisor_product: int,
    scalar_factor: int,
    determinant: int,
    h_length: int,
    delta_length: int,
    weights: tuple[complex, ...],
) -> complex:
    """Collapsed value of the complete-delta product box.

    Every reciprocal frequency is a unit modulo ``d``.  A complete
    ``delta``-period therefore vanishes unless ``d`` divides ``h``.
    """

    if min(h_length, delta_length) < 1:
        raise ValueError("product-box lengths must be positive")
    if delta_length % determinant != 0:
        raise ValueError("the delta interval must contain complete d-periods")
    if len(weights) != determinant:
        raise ValueError("one coefficient is required for each residue parameter")
    retained = 0j
    for parameter, weight in enumerate(weights):
        modulus = near_determinant_coordinates(
            divisor_product,
            scalar_factor,
            determinant,
            parameter,
        ).modulus
        if gcd(modulus, determinant) == 1:
            retained += weight
    return delta_length * (h_length // determinant) * retained


def near_determinant_reciprocity_phase(
    modulus: int,
    determinant: int,
    numerator: int,
) -> complex:
    """Original inverse phase modulo the long modulus q."""

    if min(modulus, determinant) < 2:
        raise ValueError("both moduli must exceed one")
    if gcd(modulus, determinant) != 1:
        raise ValueError("q and d must be coprime")
    return cmath.exp(
        -2j
        * cmath.pi
        * numerator
        * pow(determinant, -1, modulus)
        / modulus
    )


def near_determinant_reciprocity_phase_formula(
    modulus: int,
    determinant: int,
    numerator: int,
) -> complex:
    """Reciprocal phase modulo d, retaining the exact smooth factor."""

    if min(modulus, determinant) < 2:
        raise ValueError("both moduli must exceed one")
    if gcd(modulus, determinant) != 1:
        raise ValueError("q and d must be coprime")
    reciprocal = cmath.exp(
        2j
        * cmath.pi
        * numerator
        * pow(modulus, -1, determinant)
        / determinant
    )
    archimedean = cmath.exp(
        -2j * cmath.pi * numerator / (determinant * modulus)
    )
    return reciprocal * archimedean


@dataclass(frozen=True)
class InverseFractionSeparation:
    """Centered numerator certificate for two fixed-numerator fractions.

    If ``u=inv_s(r)`` and ``v=inv_t(r)``, then ``numerator`` is the
    signed least residue of ``u*t-v*s`` modulo ``s*t``.  It satisfies

    ``r*numerator-(t-s) = congruence_quotient*s*t``.
    """

    numerator: int
    denominator: int
    distance: Fraction
    congruence_quotient: int


@dataclass(frozen=True)
class CrossInverseFractionCollision:
    """Certificate for two inverse fractions with different numerators.

    For ``u=inv_s(r)`` and ``v=inv_t(r_prime)``, ``numerator`` is the
    signed least residue of ``u*t-v*s`` modulo ``s*t``.  If it is denoted
    by ``k`` and ``congruence_quotient`` by ``ell``, then

    ``r*r_prime*k-(r_prime*t-r*s) = ell*s*t``

    and hence the exact divisor-switching identity

    ``(r*k-t)*(r_prime+ell*s) = r*s*(k*ell-1)``.

    The identity is necessary for a near collision without imposing any
    cross-coprimality that the original sum does not possess.
    """

    numerator: int
    denominator: int
    distance: Fraction
    congruence_quotient: int


@dataclass(frozen=True)
class CentralCollisionMargins:
    """Exact margins in the elementary dyadic central-arc bounds."""

    numerator_margin: Fraction
    quotient_margin: Fraction


@dataclass(frozen=True)
class CentralCollisionLedger:
    """Exponent ledger for the divisor-switched central collision family.

    ``degenerate_count`` records the separately counted ``k*ell=1``
    diagonals. ``divisor_parameter_count`` is only the nondegenerate bound
    obtained by summing the dyadic ``r,s,k,ell`` parameters and paying a
    divisor-function factor.
    ``random_collision_count`` is the diagonal-plus-volume benchmark, not
    a proved cancellation estimate.
    """

    numerator: Fraction
    quotient: Fraction
    degenerate_count: Fraction
    divisor_parameter_count: Fraction
    random_collision_count: Fraction
    counting_gap: Fraction


@dataclass(frozen=True)
class AdditiveDualShiftPhase:
    """Exact change from the completed numerator ``r`` to ``d=r-s``."""

    shift: int
    original: Fraction
    shifted: Fraction


@dataclass(frozen=True)
class AdditiveShiftedChowlaLedger:
    """Power ledger for the lowest nonzero additive-dual block.

    This ledger applies on the overlapping balanced face ``R=S``.  The
    natural Fourier lengths are ``s/H`` and ``s/L``.  Their product sets
    the near-diagonal window ``|r-s| <= s/((s/H)(s/L))``.  No cancellation
    is asserted: ``required_saving`` is precisely the power still needed
    after this finite change of coordinates.
    """

    h_frequency: Fraction
    delta_frequency: Fraction
    product_frequency: Fraction
    completion_amplitude: Fraction
    near_shift: Fraction
    near_trivial: Fraction
    local_target: Fraction
    required_saving: Fraction
    one_modulus_l2: Fraction | None
    one_modulus_l2_gap: Fraction | None


@dataclass(frozen=True)
class AdditiveDualBlockLedger:
    """Exponent ledger for one centered nonzero Fourier rectangle."""

    h_frequency: Fraction
    delta_frequency: Fraction
    h_fourier_amplitude: Fraction
    delta_fourier_amplitude: Fraction
    product_frequency: Fraction
    completion_amplitude: Fraction
    near_shift: Fraction
    near_trivial: Fraction
    local_target: Fraction
    required_saving: Fraction
    one_modulus_l2: Fraction | None
    one_modulus_l2_gap: Fraction | None


@dataclass(frozen=True)
class CompletedProductPhaseReduction:
    """Reduced fraction data for the shifted phase ``d*a*b/s``."""

    scalar_gcd: int
    reduced_numerator: int
    reduced_denominator: int


@dataclass(frozen=True)
class SquarefreeScalarGcdStratum:
    """Ordered scalar-gcd splitting of a squarefree modulus."""

    a_gcd: int
    b_gcd: int
    reduced_modulus: int
    a_reduced: int
    b_reduced: int
    mobius_sign: int


@dataclass(frozen=True)
class KloostermanFractionTripleLedger:
    """Exponent ledger for the coprimality-migrated BC interface.

    The theorem bound is Bettin--Chandee Theorem 1 after fixing the
    signless delta-gcd factor and the Ramanujan cofactor.  The ledger
    includes their exact coefficient norms, both parenthetical terms,
    the large-phase penalty, and the remaining fixed-factor L1 cost.
    """

    product_length: Fraction
    coefficient_norms: Fraction
    first_parenthesis: Fraction
    second_parenthesis: Fraction
    phase_penalty: Fraction
    fixed_factor_cost: Fraction
    theorem_bound: Fraction
    trivial_bound: Fraction
    local_target: Fraction
    theorem_gap: Fraction
    theorem_saving: Fraction


@dataclass(frozen=True)
class FareyCentralCollisionLedger:
    """Exponent ledger after counting reduced fractions before inverse lifts."""

    numerator: Fraction
    lift_multiplicity: Fraction
    elementary_count: Fraction
    random_collision_count: Fraction
    counting_gap: Fraction


def inverse_fraction_separation(
    r: int, s: int, t: int
) -> InverseFractionSeparation:
    """Exact distance modulo one between ``inv_s(r)/s`` and ``inv_t(r)/t``."""

    if r < 1 or s < 2 or t < 2:
        raise ValueError("require r >= 1 and s,t >= 2")
    if gcd(r, s * t) != 1:
        raise ValueError("r must be invertible modulo both s and t")
    denominator = s * t
    raw_numerator = pow(r, -1, s) * t - pow(r, -1, t) * s
    numerator = raw_numerator % denominator
    if 2 * numerator > denominator:
        numerator -= denominator
    congruence_difference = r * numerator - (t - s)
    if congruence_difference % denominator != 0:
        raise AssertionError("inverse-fraction congruence certificate failed")
    return InverseFractionSeparation(
        numerator=numerator,
        denominator=denominator,
        distance=Fraction(abs(numerator), denominator),
        congruence_quotient=congruence_difference // denominator,
    )


def cross_inverse_fraction_collision(
    r: int, s: int, r_prime: int, t: int
) -> CrossInverseFractionCollision:
    """Return the exact cross-numerator inverse-fraction certificate."""

    if min(r, r_prime) < 1 or min(s, t) < 2:
        raise ValueError("require r,r_prime >= 1 and s,t >= 2")
    if gcd(r, s) != 1 or gcd(r_prime, t) != 1:
        raise ValueError("each numerator must be invertible modulo its modulus")
    denominator = s * t
    raw_numerator = pow(r, -1, s) * t - pow(r_prime, -1, t) * s
    numerator = raw_numerator % denominator
    if 2 * numerator > denominator:
        numerator -= denominator
    congruence_difference = (
        r * r_prime * numerator - (r_prime * t - r * s)
    )
    if congruence_difference % denominator != 0:
        raise AssertionError("cross inverse-fraction congruence failed")
    congruence_quotient = congruence_difference // denominator
    left = (r * numerator - t) * (
        r_prime + congruence_quotient * s
    )
    right = r * s * (numerator * congruence_quotient - 1)
    if left != right:
        raise AssertionError("cross inverse-fraction factorization failed")
    return CrossInverseFractionCollision(
        numerator=numerator,
        denominator=denominator,
        distance=Fraction(abs(numerator), denominator),
        congruence_quotient=congruence_quotient,
    )


def central_cross_inverse_collision_margins(
    r: int,
    s: int,
    r_prime: int,
    t: int,
    *,
    lower_r: int,
    lower_s: int,
    product_length: int,
) -> CentralCollisionMargins:
    """Certify elementary bounds for a dyadic central near collision.

    Assume ``R < r,r_prime <= 2R``, ``S < s,t <= 2S`` and inverse-fraction
    distance at most ``1/A``.  With the certificate ``(k,ell)`` above,

    ``|k| <= 4*S^2/A`` and
    ``|ell| <= 4*R^2/A + 4*R/S``.

    The second estimate follows directly from the defining congruence;
    it does not use cross-coprimality or an equidistribution hypothesis.
    """

    if min(lower_r, lower_s, product_length) < 1:
        raise ValueError("dyadic endpoints and product length must be positive")
    if not (
        lower_r < r <= 2 * lower_r
        and lower_r < r_prime <= 2 * lower_r
        and lower_s < s <= 2 * lower_s
        and lower_s < t <= 2 * lower_s
    ):
        raise ValueError("variables must lie in their stated dyadic intervals")
    certificate = cross_inverse_fraction_collision(r, s, r_prime, t)
    if certificate.distance > Fraction(1, product_length):
        raise ValueError("the inverse fractions are not in the central arc")
    numerator_bound = Fraction(4 * lower_s * lower_s, product_length)
    quotient_bound = (
        Fraction(4 * lower_r * lower_r, product_length)
        + Fraction(4 * lower_r, lower_s)
    )
    numerator_margin = numerator_bound - abs(certificate.numerator)
    quotient_margin = quotient_bound - abs(certificate.congruence_quotient)
    if numerator_margin < 0 or quotient_margin < 0:
        raise AssertionError("elementary central-collision bound failed")
    return CentralCollisionMargins(
        numerator_margin=numerator_margin,
        quotient_margin=quotient_margin,
    )


def central_collision_ledger(box: ExponentBox) -> CentralCollisionLedger:
    """Return exact exponent sizes in the divisor-switched central arc.

    For ``R=T^rho``, ``S=T^sigma`` and ``A=T^a``, the signed numerator
    has length ``K=T^max(0,2*sigma-a)`` and the congruence quotient has
    length ``E=T^max(0,2*rho-a,rho-sigma)``.  Summing ``r,s,k,ell`` and
    using the factorization only through a divisor bound costs exponent
    ``rho+sigma+K+E`` away from ``k*ell=1``.  The latter two diagonal
    families cost ``rho+sigma`` in the balanced dyadic interval.  The
    volume benchmark for collisions among
    ``R*S`` points in an arc of width ``1/A`` is
    ``max(rho+sigma,2*(rho+sigma)-a)``.
    """

    if not is_admissible(box):
        raise ValueError("central collision ledger requires an admissible box")
    a = box.third_length
    numerator = max(Fraction(0), 2 * box.sigma - a)
    quotient = max(
        Fraction(0), 2 * box.rho - a, box.rho - box.sigma
    )
    divisor_parameter_count = box.rho + box.sigma + numerator + quotient
    random_collision_count = max(
        box.rho + box.sigma,
        2 * (box.rho + box.sigma) - a,
    )
    return CentralCollisionLedger(
        numerator=numerator,
        quotient=quotient,
        degenerate_count=box.rho + box.sigma,
        divisor_parameter_count=divisor_parameter_count,
        random_collision_count=random_collision_count,
        counting_gap=divisor_parameter_count - random_collision_count,
    )


def rectangular_product_multiplicities(
    h_length: int, delta_length: int
) -> dict[int, int]:
    """Multiplicity of ``a=h*delta`` in a finite rectangular product box."""

    if min(h_length, delta_length) < 1:
        raise ValueError("product-box lengths must be positive")
    result: dict[int, int] = {}
    for h in range(1, h_length + 1):
        for delta in range(1, delta_length + 1):
            product = h * delta
            result[product] = result.get(product, 0) + 1
    return result


def rectangular_product_residue_energy(
    h_length: int, delta_length: int, modulus: int
) -> int:
    """Exact energy after folding ``h*delta`` into residues modulo ``d``."""

    if modulus < 1:
        raise ValueError("modulus must be positive")
    residue_multiplicities = [0] * modulus
    for product, multiplicity in rectangular_product_multiplicities(
        h_length, delta_length
    ).items():
        residue_multiplicities[product % modulus] += multiplicity
    return sum(value * value for value in residue_multiplicities)


def rectangular_product_residue_energy_majorant(
    h_length: int, delta_length: int, modulus: int
) -> int:
    """Boundary-exact Cauchy majorant for product residue energy."""

    if modulus < 1:
        raise ValueError("modulus must be positive")
    multiplicities = rectangular_product_multiplicities(h_length, delta_length)
    product_ceiling = (
        h_length * delta_length + modulus - 1
    ) // modulus
    return product_ceiling * sum(value * value for value in multiplicities.values())


def rectangular_product_kernel(
    h_length: int, delta_length: int, phase: Fraction
) -> complex:
    """Evaluate ``sum_{h<=H,delta<=L} exp(2*pi*i*h*delta*phase)``."""

    if min(h_length, delta_length) < 1:
        raise ValueError("product-box lengths must be positive")
    return sum(
        cmath.exp(2j * cmath.pi * float((h * delta * phase) % 1))
        for h in range(1, h_length + 1)
        for delta in range(1, delta_length + 1)
    )


def linear_convolution_energy_on_multiples(
    left_length: int,
    right_length: int,
    left_multiplier: int,
    right_multiplier: int,
    divisor: int,
) -> int:
    """Energy of ``L*x+M*y`` restricted to values divisible by ``g``."""

    if min(
        left_length,
        right_length,
        left_multiplier,
        right_multiplier,
        divisor,
    ) < 1:
        raise ValueError("lengths, multipliers, and divisor must be positive")
    multiplicities: dict[int, int] = {}
    for left_value in range(1, left_length + 1):
        for right_value in range(1, right_length + 1):
            total = (
                left_multiplier * left_value
                + right_multiplier * right_value
            )
            if total % divisor == 0:
                multiplicities[total] = multiplicities.get(total, 0) + 1
    return sum(multiplicity * multiplicity for multiplicity in multiplicities.values())


def linear_convolution_energy_on_multiples_majorant(
    left_length: int,
    right_length: int,
    divisor: int,
) -> int:
    """Finite ``D^3/g`` majorant when the right multiplier is a unit mod g.

    For each left input, one residue class of right inputs survives modulo
    ``g``.  There are at most ``ceil(right_length/g)`` such inputs, while
    every exact convolution value has multiplicity at most the shorter
    interval length.
    """

    if min(left_length, right_length, divisor) < 1:
        raise ValueError("lengths and divisor must be positive")
    right_residue_count = (right_length - 1) // divisor + 1
    return (
        min(left_length, right_length)
        * left_length
        * right_residue_count
    )


def _finite_interval_fourier(length: int, frequency: int, modulus: int) -> complex:
    return sum(
        cmath.exp(-2j * cmath.pi * frequency * value / modulus)
        for value in range(1, length + 1)
    )


def additive_product_completion(
    r: int, modulus: int, h_length: int, delta_length: int
) -> complex:
    """Exact two-dimensional finite completion of the inverse product phase.

    If ``u=inv_modulus(r)`` and
    ``W_hat(a)=sum_{h<=H} e_modulus(-a*h)`` (similarly for ``V``), then

    ``sum_{h<=H,d<=L} e_modulus(-u*h*d)``
    ``= 1/modulus * sum_{a,b mod modulus} W_hat(a)V_hat(b)``
    ``  * e_modulus(r*a*b)``.

    The complete two-variable transform is elementary: summing first in
    the second residue forces ``x=r*b``.  In particular the inverse is
    removed, but a nonoscillatory dual zero mode remains.
    """

    if min(r, modulus, h_length, delta_length) < 1:
        raise ValueError("all completion parameters must be positive")
    if gcd(r, modulus) != 1:
        raise ValueError("r must be invertible modulo the modulus")
    h_fourier = [
        _finite_interval_fourier(h_length, a, modulus)
        for a in range(modulus)
    ]
    delta_fourier = [
        _finite_interval_fourier(delta_length, b, modulus)
        for b in range(modulus)
    ]
    return sum(
        h_fourier[a]
        * delta_fourier[b]
        * cmath.exp(2j * cmath.pi * ((r * a * b) % modulus) / modulus)
        for a in range(modulus)
        for b in range(modulus)
    ) / modulus


def weighted_additive_product_completion_sides(
    r: int,
    modulus: int,
    h_weights: Mapping[int, complex],
    delta_weights: Mapping[int, complex],
) -> tuple[complex, complex]:
    """Both sides of smooth finite completion (9.366).

    The dictionaries may have arbitrary signed integer support and
    arbitrary complex values.  This is the boundary-free finite identity
    underlying the modulated smooth transforms; decay of those transforms
    is a separate analytic statement.
    """

    if min(r, modulus) < 1:
        raise ValueError("r and modulus must be positive")
    if gcd(r, modulus) != 1:
        raise ValueError("r must be invertible modulo the modulus")

    inverse = pow(r, -1, modulus)
    direct = sum(
        h_weight
        * delta_weight
        * cmath.exp(
            -2j
            * cmath.pi
            * ((inverse * h * delta) % modulus)
            / modulus
        )
        for h, h_weight in h_weights.items()
        for delta, delta_weight in delta_weights.items()
    )
    h_fourier = [
        sum(
            weight
            * cmath.exp(-2j * cmath.pi * a * h / modulus)
            for h, weight in h_weights.items()
        )
        for a in range(modulus)
    ]
    delta_fourier = [
        sum(
            weight
            * cmath.exp(-2j * cmath.pi * b * delta / modulus)
            for delta, weight in delta_weights.items()
        )
        for b in range(modulus)
    ]
    completed = sum(
        h_fourier[a]
        * delta_fourier[b]
        * cmath.exp(
            2j * cmath.pi * ((r * a * b) % modulus) / modulus
        )
        for a in range(modulus)
        for b in range(modulus)
    ) / modulus
    return direct, completed


def additive_dual_shift_phase(
    r: int, modulus: int, a: int, b: int
) -> AdditiveDualShiftPhase:
    """Return ``e_s(rab)=e_s((r-s)ab)`` as an exact rational phase.

    In the completed inverse kernel the modulus is the original variable
    ``s``.  Writing ``d=r-s`` therefore turns the outer signs into the
    shifted pair ``mu(s)mu(s+d)`` without a boundary approximation.
    """

    if min(r, modulus) < 1 or min(a, b) < 0:
        raise ValueError("require positive r,s and nonnegative residues")
    shift = r - modulus
    original = Fraction(r * a * b, modulus) % 1
    shifted = Fraction(shift * a * b, modulus) % 1
    if original != shifted:
        raise AssertionError("subtracting the modulus changed the phase")
    return AdditiveDualShiftPhase(
        shift=shift,
        original=original,
        shifted=shifted,
    )


def completed_product_phase_reduction(
    shift: int, modulus: int, a: int, b: int
) -> CompletedProductPhaseReduction:
    """Reduce ``d*a*b/s`` when ``(d,s)=1`` without losing gcd strata.

    The only denominator drop comes from ``g=(a*b,s)``.  Thus the exact
    reduced denominator is ``s/g``; in a no-wrap block ``|a*b|<s`` it is
    at least ``s/|a*b|``.  This is the scalar-divisor interface that a
    far-arc estimate must retain.
    """

    if modulus < 1 or a == 0 or b == 0:
        raise ValueError("require a positive modulus and nonzero frequencies")
    if gcd(shift, modulus) != 1:
        raise ValueError("the shifted numerator must be a unit modulo s")
    scalar_gcd = gcd(abs(a * b), modulus)
    reduced_denominator = modulus // scalar_gcd
    reduced_numerator = (
        shift * (a * b // scalar_gcd)
    ) % reduced_denominator
    if gcd(reduced_numerator, reduced_denominator) != 1:
        raise AssertionError("the completed phase was not fully reduced")
    return CompletedProductPhaseReduction(
        scalar_gcd=scalar_gcd,
        reduced_numerator=reduced_numerator,
        reduced_denominator=reduced_denominator,
    )


def squarefree_scalar_gcd_stratum(
    modulus: int, a: int, b: int
) -> SquarefreeScalarGcdStratum:
    """Factor the scalar divisor stratum without double-counting primes.

    Put ``g_a=(a,s)``, ``g_b=(b,s/g_a)`` and ``q=s/(g_a*g_b)``.
    If ``s`` is squarefree then these three factors are pairwise coprime,
    ``g_a*g_b=(a*b,s)``, and

    ``a*b/s = (a/g_a)*(b/g_b)/q``.

    The outer sign also factors as ``mu(s)=mu(g_a)mu(g_b)mu(q)``.
    """

    if modulus < 1 or a == 0 or b == 0:
        raise ValueError("require a positive modulus and nonzero frequencies")
    if mobius(modulus) == 0:
        raise ValueError("the scalar-gcd splitting requires squarefree s")
    a_gcd = gcd(abs(a), modulus)
    remaining = modulus // a_gcd
    b_gcd = gcd(abs(b), remaining)
    reduced_modulus = remaining // b_gcd
    a_reduced = a // a_gcd
    b_reduced = b // b_gcd
    if a_gcd * b_gcd != gcd(abs(a * b), modulus):
        raise AssertionError("ordered gcd factors missed a scalar prime")
    if gcd(a_reduced * b_reduced, reduced_modulus) != 1:
        raise AssertionError("the reduced product is not a unit")
    mobius_sign = (
        mobius(a_gcd) * mobius(b_gcd) * mobius(reduced_modulus)
    )
    if mobius_sign != mobius(modulus):
        raise AssertionError("the squarefree Möbius sign did not factor")
    return SquarefreeScalarGcdStratum(
        a_gcd=a_gcd,
        b_gcd=b_gcd,
        reduced_modulus=reduced_modulus,
        a_reduced=a_reduced,
        b_reduced=b_reduced,
        mobius_sign=mobius_sign,
    )


def restricted_unit_fourier_lift(
    scalar: int, reduced_modulus: int, residue: int, length: int
) -> complex:
    """Direct unit-restricted lift of an interval transform from q to gq."""

    if min(scalar, reduced_modulus, length) < 1:
        raise ValueError("the lift parameters must be positive")
    if gcd(scalar, reduced_modulus) != 1:
        raise ValueError("the scalar and reduced modulus must be coprime")
    if gcd(residue, reduced_modulus) != 1:
        raise ValueError("the base residue must be a unit modulo q")
    modulus = scalar * reduced_modulus
    return sum(
        _finite_interval_fourier(length, lift, modulus)
        for lift in (
            residue + multiple * reduced_modulus
            for multiple in range(scalar)
        )
        if gcd(lift, modulus) == 1
    )


def restricted_unit_fourier_lift_formula(
    scalar: int, reduced_modulus: int, residue: int, length: int
) -> complex:
    """Ramanujan formula for :func:`restricted_unit_fourier_lift`."""

    if min(scalar, reduced_modulus, length) < 1:
        raise ValueError("the lift parameters must be positive")
    if gcd(scalar, reduced_modulus) != 1:
        raise ValueError("the scalar and reduced modulus must be coprime")
    if gcd(residue, reduced_modulus) != 1:
        raise ValueError("the base residue must be a unit modulo q")
    if reduced_modulus == 1:
        inverse_scalar = 0
    else:
        inverse_scalar = pow(scalar, -1, reduced_modulus)
    return sum(
        ramanujan_sum(scalar, value)
        * cmath.exp(
            2j
            * cmath.pi
            * ((-inverse_scalar * residue * value) % reduced_modulus)
            / reduced_modulus
        )
        for value in range(1, length + 1)
    )


def unrestricted_fourier_lift(
    scalar: int, reduced_modulus: int, residue: int, length: int
) -> complex:
    """Direct unrestricted lift of an interval transform from q to gq."""

    if min(scalar, reduced_modulus, length) < 1:
        raise ValueError("the lift parameters must be positive")
    if gcd(scalar, reduced_modulus) != 1:
        raise ValueError("the scalar and reduced modulus must be coprime")
    modulus = scalar * reduced_modulus
    return sum(
        _finite_interval_fourier(
            length,
            residue + multiple * reduced_modulus,
            modulus,
        )
        for multiple in range(scalar)
    )


def unrestricted_fourier_lift_formula(
    scalar: int, reduced_modulus: int, residue: int, length: int
) -> complex:
    """Orthogonality formula for :func:`unrestricted_fourier_lift`."""

    if min(scalar, reduced_modulus, length) < 1:
        raise ValueError("the lift parameters must be positive")
    if gcd(scalar, reduced_modulus) != 1:
        raise ValueError("the scalar and reduced modulus must be coprime")
    return scalar * _finite_interval_fourier(
        length // scalar,
        residue,
        reduced_modulus,
    )


def double_unit_bilinear_sum(
    modulus: int,
    a_coefficient: int,
    b_coefficient: int,
    bilinear_coefficient: int,
) -> complex:
    """Direct complete sum over two units modulo a squarefree modulus."""

    if modulus < 1 or mobius(modulus) == 0:
        raise ValueError("the double-unit sum requires squarefree q")
    if gcd(bilinear_coefficient, modulus) != 1:
        raise ValueError("the bilinear coefficient must be a unit modulo q")
    return sum(
        cmath.exp(
            2j
            * cmath.pi
            * (
                (
                    bilinear_coefficient * u * v
                    - a_coefficient * u
                    - b_coefficient * v
                )
                % modulus
            )
            / modulus
        )
        for u in range(modulus)
        if gcd(u, modulus) == 1
        for v in range(modulus)
        if gcd(v, modulus) == 1
    )


def double_unit_divisor_spectrum(
    modulus: int,
    a_coefficient: int,
    b_coefficient: int,
    bilinear_coefficient: int,
) -> complex:
    """Exact divisor spectrum of the complete double-unit bilinear sum.

    For squarefree ``q`` and ``(d,q)=1``, Chinese remaindering the local
    prime identity

    ``sum_{u,v != 0 mod p} e_p(d*u*v-A*u-B*v)``
    ``= p*e_p(-A*B/d)-c_p(A)``

    gives, after noting that the local stationary unit exists only when
    ``p`` does not divide ``B``,

    ``sum_{k|q, (k,B)=1} k*mu(q/k)*c_{q/k}(A)``
    ``  * e_k(-A*B*inv_k(d*(q/k)))``.

    The ``k=1`` phase is interpreted as one.
    """

    if modulus < 1 or mobius(modulus) == 0:
        raise ValueError("the divisor spectrum requires squarefree q")
    if gcd(bilinear_coefficient, modulus) != 1:
        raise ValueError("the bilinear coefficient must be a unit modulo q")
    total = 0j
    for divisor_modulus in divisors(modulus):
        if gcd(divisor_modulus, b_coefficient) != 1:
            continue
        cofactor = modulus // divisor_modulus
        coefficient = (
            divisor_modulus
            * mobius(cofactor)
            * ramanujan_sum(cofactor, a_coefficient)
        )
        if divisor_modulus == 1:
            phase = 1 + 0j
        else:
            inverse = pow(
                (bilinear_coefficient * cofactor) % divisor_modulus,
                -1,
                divisor_modulus,
            )
            phase = cmath.exp(
                2j
                * cmath.pi
                * (
                    (-a_coefficient * b_coefficient * inverse)
                    % divisor_modulus
                )
                / divisor_modulus
            )
        total += coefficient * phase
    return total


def mobius_weighted_double_unit_divisor_spectrum(
    modulus: int,
    a_coefficient: int,
    b_coefficient: int,
    bilinear_coefficient: int,
) -> complex:
    """Divisor spectrum after migrating the outer squarefree ``mu(q)``.

    Writing ``q=k*n``, squarefreeness gives
    ``mu(q)*mu(n)=mu(k)``.  Thus the cofactor Möbius sign disappears and
    the surviving sign is attached to the oscillatory divisor modulus.
    """

    if modulus < 1 or mobius(modulus) == 0:
        raise ValueError("the weighted spectrum requires squarefree q")
    if gcd(bilinear_coefficient, modulus) != 1:
        raise ValueError("the bilinear coefficient must be a unit modulo q")
    total = 0j
    for divisor_modulus in divisors(modulus):
        if gcd(divisor_modulus, b_coefficient) != 1:
            continue
        cofactor = modulus // divisor_modulus
        coefficient = (
            divisor_modulus
            * mobius(divisor_modulus)
            * ramanujan_sum(cofactor, a_coefficient)
        )
        if divisor_modulus == 1:
            phase = 1 + 0j
        else:
            inverse = pow(
                (bilinear_coefficient * cofactor) % divisor_modulus,
                -1,
                divisor_modulus,
            )
            phase = cmath.exp(
                2j
                * cmath.pi
                * (
                    (-a_coefficient * b_coefficient * inverse)
                    % divisor_modulus
                )
                / divisor_modulus
            )
        total += coefficient * phase
    return total


def centered_inverse_cross_correlation(
    left_modulus: int,
    left_numerator: int,
    right_modulus: int,
    right_numerator: int,
) -> complex:
    """Direct centered inverse-phase covariance on the common unit group."""

    if left_modulus < 1 or right_modulus < 1:
        raise ValueError("moduli must be positive")
    common_modulus = (
        left_modulus
        * right_modulus
        // gcd(left_modulus, right_modulus)
    )
    left_mean = Fraction(
        ramanujan_sum(left_modulus, left_numerator),
        _euler_phi(left_modulus),
    )
    right_mean = Fraction(
        ramanujan_sum(right_modulus, right_numerator),
        _euler_phi(right_modulus),
    )
    total = 0j
    for residue in range(common_modulus):
        if gcd(residue, common_modulus) != 1:
            continue
        if left_modulus == 1:
            left_phase = 1 + 0j
        else:
            left_phase = cmath.exp(
                2j
                * cmath.pi
                * (
                    left_numerator
                    * pow(residue, -1, left_modulus)
                    % left_modulus
                )
                / left_modulus
            )
        if right_modulus == 1:
            right_phase = 1 + 0j
        else:
            right_phase = cmath.exp(
                2j
                * cmath.pi
                * (
                    right_numerator
                    * pow(residue, -1, right_modulus)
                    % right_modulus
                )
                / right_modulus
            )
        total += (left_phase - float(left_mean)) * (
            right_phase - float(right_mean)
        ).conjugate()
    return total


def centered_inverse_cross_correlation_formula(
    left_modulus: int,
    left_numerator: int,
    right_modulus: int,
    right_numerator: int,
) -> Fraction:
    """Closed Ramanujan formula for the centered inverse covariance."""

    if left_modulus < 1 or right_modulus < 1:
        raise ValueError("moduli must be positive")
    common_modulus = (
        left_modulus
        * right_modulus
        // gcd(left_modulus, right_modulus)
    )
    combined_frequency = (
        left_numerator * (common_modulus // left_modulus)
        - right_numerator * (common_modulus // right_modulus)
    )
    return Fraction(ramanujan_sum(common_modulus, combined_frequency)) - Fraction(
        _euler_phi(common_modulus)
        * ramanujan_sum(left_modulus, left_numerator)
        * ramanujan_sum(right_modulus, right_numerator),
        _euler_phi(left_modulus) * _euler_phi(right_modulus),
    )


def centered_inverse_cross_correlation_gcd_formula(
    left_modulus: int,
    left_numerator: int,
    right_modulus: int,
    right_numerator: int,
) -> Fraction:
    """Squarefree common-divisor form of the centered covariance."""

    if left_modulus < 1 or right_modulus < 1:
        raise ValueError("moduli must be positive")
    if mobius(left_modulus) == 0 or mobius(right_modulus) == 0:
        raise ValueError("the gcd formula requires squarefree moduli")
    common_divisor = gcd(left_modulus, right_modulus)
    left_cofactor = left_modulus // common_divisor
    right_cofactor = right_modulus // common_divisor
    common_covariance = Fraction(
        ramanujan_sum(
            common_divisor,
            left_numerator * right_cofactor
            - right_numerator * left_cofactor,
        )
    ) - Fraction(
        ramanujan_sum(common_divisor, left_numerator)
        * ramanujan_sum(common_divisor, right_numerator),
        _euler_phi(common_divisor),
    )
    return (
        ramanujan_sum(left_cofactor, left_numerator)
        * ramanujan_sum(right_cofactor, right_numerator)
        * common_covariance
    )


def mobius_weighted_double_unit_mean(
    modulus: int,
    a_coefficient: int,
    b_coefficient: int,
) -> Fraction:
    """Unit average of the outer-Möbius-weighted double-unit spectrum."""

    if modulus < 1 or mobius(modulus) == 0:
        raise ValueError("the double-unit mean requires squarefree q")
    return Fraction(
        ramanujan_sum(modulus, a_coefficient)
        * ramanujan_sum(modulus, b_coefficient),
        _euler_phi(modulus),
    )


def mobius_weighted_centered_double_unit_divisor_spectrum(
    modulus: int,
    a_coefficient: int,
    b_coefficient: int,
    bilinear_coefficient: int,
) -> complex:
    """Centered divisor layers of the weighted double-unit spectrum."""

    if modulus < 1 or mobius(modulus) == 0:
        raise ValueError("the centered spectrum requires squarefree q")
    if gcd(bilinear_coefficient, modulus) != 1:
        raise ValueError("the bilinear coefficient must be a unit modulo q")
    total = 0j
    for divisor_modulus in divisors(modulus):
        if gcd(divisor_modulus, b_coefficient) != 1:
            continue
        cofactor = modulus // divisor_modulus
        coefficient = (
            divisor_modulus
            * mobius(divisor_modulus)
            * ramanujan_sum(cofactor, a_coefficient)
        )
        if divisor_modulus == 1:
            phase = 1 + 0j
        else:
            inverse = pow(
                (bilinear_coefficient * cofactor) % divisor_modulus,
                -1,
                divisor_modulus,
            )
            phase = cmath.exp(
                2j
                * cmath.pi
                * (
                    (-a_coefficient * b_coefficient * inverse)
                    % divisor_modulus
                )
                / divisor_modulus
            )
        layer_mean = Fraction(
            ramanujan_sum(divisor_modulus, a_coefficient),
            _euler_phi(divisor_modulus),
        )
        total += coefficient * (phase - float(layer_mean))
    return total


def centered_inverse_cross_fourier(
    left_modulus: int,
    left_numerator: int,
    right_modulus: int,
    right_numerator: int,
    frequency: int,
) -> complex:
    """Direct Fourier coefficient of a centered inverse-phase product."""

    if left_modulus < 1 or right_modulus < 1:
        raise ValueError("moduli must be positive")
    common_modulus = (
        left_modulus
        * right_modulus
        // gcd(left_modulus, right_modulus)
    )
    left_mean = Fraction(
        ramanujan_sum(left_modulus, left_numerator),
        _euler_phi(left_modulus),
    )
    right_mean = Fraction(
        ramanujan_sum(right_modulus, right_numerator),
        _euler_phi(right_modulus),
    )
    total = 0j
    for residue in range(common_modulus):
        if gcd(residue, common_modulus) != 1:
            continue
        if left_modulus == 1:
            left_phase = 1 + 0j
        else:
            left_phase = cmath.exp(
                2j
                * cmath.pi
                * (
                    left_numerator
                    * pow(residue, -1, left_modulus)
                    % left_modulus
                )
                / left_modulus
            )
        if right_modulus == 1:
            right_phase = 1 + 0j
        else:
            right_phase = cmath.exp(
                2j
                * cmath.pi
                * (
                    right_numerator
                    * pow(residue, -1, right_modulus)
                    % right_modulus
                )
                / right_modulus
            )
        centered_product = (left_phase - float(left_mean)) * (
            right_phase - float(right_mean)
        ).conjugate()
        additive_phase = cmath.exp(
            -2j * cmath.pi * (frequency * residue % common_modulus)
            / common_modulus
        )
        total += centered_product * additive_phase
    return total


def centered_inverse_cross_fourier_formula(
    left_modulus: int,
    left_numerator: int,
    right_modulus: int,
    right_numerator: int,
    frequency: int,
) -> complex:
    """Four-Kloosterman formula for the centered cross coefficient."""

    if left_modulus < 1 or right_modulus < 1:
        raise ValueError("moduli must be positive")
    common_modulus = (
        left_modulus
        * right_modulus
        // gcd(left_modulus, right_modulus)
    )
    left_lift = left_numerator * (common_modulus // left_modulus)
    right_lift = right_numerator * (common_modulus // right_modulus)
    left_mean = Fraction(
        ramanujan_sum(left_modulus, left_numerator),
        _euler_phi(left_modulus),
    )
    right_mean = Fraction(
        ramanujan_sum(right_modulus, right_numerator),
        _euler_phi(right_modulus),
    )
    return (
        _kloosterman_sum(
            common_modulus,
            left_lift - right_lift,
            -frequency,
        )
        - float(right_mean)
        * _kloosterman_sum(common_modulus, left_lift, -frequency)
        - float(left_mean)
        * _kloosterman_sum(common_modulus, -right_lift, -frequency)
        + float(left_mean * right_mean)
        * ramanujan_sum(common_modulus, frequency)
    )


def large_common_divisor_pair_bound(
    dyadic_scale: int, threshold: int
) -> int:
    """Finite union bound for dyadic pairs with a large common divisor."""

    if dyadic_scale < 1:
        raise ValueError("dyadic scale must be positive")
    if threshold < 2:
        raise ValueError("threshold must be at least two")
    return sum(
        (2 * dyadic_scale // common_divisor) ** 2
        for common_divisor in range(
            threshold,
            2 * dyadic_scale + 1,
        )
    )


def centered_kloosterman_transform(
    modulus: int, inverse_numerator: int, linear_frequency: int
) -> complex:
    """Fourier transform of one centered inverse phase."""

    if modulus < 1:
        raise ValueError("modulus must be positive")
    inverse_mean = Fraction(
        ramanujan_sum(modulus, inverse_numerator),
        _euler_phi(modulus),
    )
    return _kloosterman_sum(
        modulus,
        inverse_numerator,
        linear_frequency,
    ) - float(inverse_mean) * ramanujan_sum(
        modulus,
        linear_frequency,
    )


def centered_kloosterman_numerator_fourier(
    modulus: int,
    numerator_multiplier: int,
    linear_frequency: int,
    dual_frequency: int,
) -> complex:
    """Direct finite Fourier transform in the inverse numerator."""

    if modulus < 1:
        raise ValueError("modulus must be positive")
    if gcd(numerator_multiplier, modulus) != 1:
        raise ValueError("the numerator multiplier must be a unit")
    return sum(
        centered_kloosterman_transform(
            modulus,
            numerator_multiplier * numerator,
            linear_frequency,
        )
        * cmath.exp(
            -2j * cmath.pi * dual_frequency * numerator / modulus
        )
        for numerator in range(modulus)
    )


def centered_kloosterman_numerator_fourier_formula(
    modulus: int,
    numerator_multiplier: int,
    linear_frequency: int,
    dual_frequency: int,
) -> complex:
    """Closed numerator-Fourier formula with exact unit support."""

    if modulus < 1:
        raise ValueError("modulus must be positive")
    if gcd(numerator_multiplier, modulus) != 1:
        raise ValueError("the numerator multiplier must be a unit")
    if gcd(dual_frequency, modulus) != 1:
        return 0j
    if modulus == 1:
        phase = 1 + 0j
    else:
        dual_inverse = pow(dual_frequency % modulus, -1, modulus)
        phase = cmath.exp(
            2j
            * cmath.pi
            * (
                linear_frequency
                * numerator_multiplier
                * dual_inverse
                % modulus
            )
            / modulus
        )
    linear_mean = Fraction(
        ramanujan_sum(modulus, linear_frequency),
        _euler_phi(modulus),
    )
    return modulus * (phase - float(linear_mean))


def centered_inverse_numerator_fourier(
    modulus: int,
    numerator_multiplier: int,
    inverse_residue: int,
    dual_frequency: int,
) -> complex:
    """Fourier transform in the numerator before the inverse-residue sum."""

    if modulus < 1:
        raise ValueError("the modulus must be positive")
    if gcd(inverse_residue, modulus) != 1:
        raise ValueError("the inverse residue must be a unit")
    residue_inverse = (
        0
        if modulus == 1
        else pow(inverse_residue % modulus, -1, modulus)
    )
    return sum(
        (
            cmath.exp(
                2j
                * cmath.pi
                * (
                    numerator_multiplier * numerator * residue_inverse
                    % modulus
                )
                / modulus
            )
            - float(
                Fraction(
                    ramanujan_sum(
                        modulus,
                        numerator_multiplier * numerator,
                    ),
                    _euler_phi(modulus),
                )
            )
        )
        * cmath.exp(
            -2j * cmath.pi * dual_frequency * numerator / modulus
        )
        for numerator in range(modulus)
    )


def centered_inverse_numerator_fourier_formula(
    modulus: int,
    numerator_multiplier: int,
    inverse_residue: int,
    dual_frequency: int,
) -> complex:
    """Exact reduced-modulus delta-minus-mean numerator transform."""

    if modulus < 1:
        raise ValueError("the modulus must be positive")
    if gcd(inverse_residue, modulus) != 1:
        raise ValueError("the inverse residue must be a unit")
    multiplier_gcd = gcd(numerator_multiplier, modulus)
    reduced_modulus = modulus // multiplier_gcd
    if (
        dual_frequency % multiplier_gcd != 0
        or gcd(dual_frequency // multiplier_gcd, reduced_modulus) != 1
    ):
        return 0j
    reduced_dual = dual_frequency // multiplier_gcd
    reduced_multiplier = numerator_multiplier // multiplier_gcd
    dual_inverse = (
        0
        if reduced_modulus == 1
        else pow(reduced_dual % reduced_modulus, -1, reduced_modulus)
    )
    selected_residue = (
        reduced_multiplier * dual_inverse % reduced_modulus
    )
    point_mass = int(
        inverse_residue % reduced_modulus == selected_residue
    )
    return modulus * (
        point_mass - Fraction(1, _euler_phi(reduced_modulus))
    )


def centered_residue_collision_fourier(
    left_modulus: int,
    right_modulus: int,
    left_residue: int,
    right_residue: int,
    frequency: int,
) -> complex:
    """Direct Fourier transform of two centered residue point masses."""

    if left_modulus < 1 or right_modulus < 1:
        raise ValueError("moduli must be positive")
    if gcd(left_residue, left_modulus) != 1:
        raise ValueError("the left residue must be a unit")
    if gcd(right_residue, right_modulus) != 1:
        raise ValueError("the right residue must be a unit")
    common_modulus = (
        left_modulus
        * right_modulus
        // gcd(left_modulus, right_modulus)
    )
    left_mean = Fraction(1, _euler_phi(left_modulus))
    right_mean = Fraction(1, _euler_phi(right_modulus))
    return sum(
        (
            int(residue % left_modulus == left_residue % left_modulus)
            - float(left_mean)
        )
        * (
            int(residue % right_modulus == right_residue % right_modulus)
            - float(right_mean)
        )
        * cmath.exp(
            -2j * cmath.pi * frequency * residue / common_modulus
        )
        for residue in range(common_modulus)
        if gcd(residue, common_modulus) == 1
    )


def centered_residue_collision_fourier_formula(
    left_modulus: int,
    right_modulus: int,
    left_residue: int,
    right_residue: int,
    frequency: int,
) -> complex:
    """CRT collision, two Ramanujan marginals, and their common mean."""

    if left_modulus < 1 or right_modulus < 1:
        raise ValueError("moduli must be positive")
    if gcd(left_residue, left_modulus) != 1:
        raise ValueError("the left residue must be a unit")
    if gcd(right_residue, right_modulus) != 1:
        raise ValueError("the right residue must be a unit")
    common_factor = gcd(left_modulus, right_modulus)
    left_cofactor = left_modulus // common_factor
    right_cofactor = right_modulus // common_factor
    if (
        gcd(common_factor, left_cofactor) != 1
        or gcd(common_factor, right_cofactor) != 1
        or gcd(left_cofactor, right_cofactor) != 1
    ):
        raise ValueError("the common factor and cofactors must be pairwise coprime")
    common_modulus = common_factor * left_cofactor * right_cofactor

    collision = 0j
    if (left_residue - right_residue) % common_factor == 0:
        cofactor_inverse = (
            0
            if right_cofactor == 1
            else pow(left_cofactor, -1, right_cofactor)
        )
        lift = (
            (right_residue - left_residue)
            // common_factor
            * cofactor_inverse
        ) % right_cofactor
        collision_residue = (
            left_residue + left_modulus * lift
        ) % common_modulus
        collision = cmath.exp(
            -2j
            * cmath.pi
            * frequency
            * collision_residue
            / common_modulus
        )

    left_inverse = (
        0
        if left_modulus == 1
        else pow(right_cofactor, -1, left_modulus)
    )
    left_marginal = ramanujan_sum(
        right_cofactor,
        frequency,
    ) * cmath.exp(
        -2j
        * cmath.pi
        * (
            frequency * left_residue * left_inverse % left_modulus
        )
        / left_modulus
    )
    right_inverse = (
        0
        if right_modulus == 1
        else pow(left_cofactor, -1, right_modulus)
    )
    right_marginal = ramanujan_sum(
        left_cofactor,
        frequency,
    ) * cmath.exp(
        -2j
        * cmath.pi
        * (
            frequency * right_residue * right_inverse % right_modulus
        )
        / right_modulus
    )
    return (
        collision
        - left_marginal / _euler_phi(right_modulus)
        - right_marginal / _euler_phi(left_modulus)
        + ramanujan_sum(common_modulus, frequency)
        / (
            _euler_phi(left_modulus)
            * _euler_phi(right_modulus)
        )
    )


def ambient_centered_residue_collision_fourier(
    ambient_modulus: int,
    left_modulus: int,
    right_modulus: int,
    left_residue: int,
    right_residue: int,
    frequency: int,
) -> complex:
    """Direct centered collision lifted to a larger unit-group modulus."""

    if min(ambient_modulus, left_modulus, right_modulus) < 1:
        raise ValueError("moduli must be positive")
    if (
        ambient_modulus % left_modulus != 0
        or ambient_modulus % right_modulus != 0
    ):
        raise ValueError("both collision moduli must divide the ambient modulus")
    if gcd(left_residue, left_modulus) != 1:
        raise ValueError("the left residue must be a unit")
    if gcd(right_residue, right_modulus) != 1:
        raise ValueError("the right residue must be a unit")
    left_mean = Fraction(1, _euler_phi(left_modulus))
    right_mean = Fraction(1, _euler_phi(right_modulus))
    return sum(
        (
            int(residue % left_modulus == left_residue % left_modulus)
            - float(left_mean)
        )
        * (
            int(residue % right_modulus == right_residue % right_modulus)
            - float(right_mean)
        )
        * cmath.exp(
            -2j * cmath.pi * frequency * residue / ambient_modulus
        )
        for residue in range(ambient_modulus)
        if gcd(residue, ambient_modulus) == 1
    )


def ambient_centered_residue_collision_fourier_formula(
    ambient_modulus: int,
    left_modulus: int,
    right_modulus: int,
    left_residue: int,
    right_residue: int,
    frequency: int,
) -> complex:
    """Free Ramanujan factor times the reduced CRT collision."""

    if min(ambient_modulus, left_modulus, right_modulus) < 1:
        raise ValueError("moduli must be positive")
    if (
        ambient_modulus % left_modulus != 0
        or ambient_modulus % right_modulus != 0
    ):
        raise ValueError("both collision moduli must divide the ambient modulus")
    core_modulus = (
        left_modulus
        * right_modulus
        // gcd(left_modulus, right_modulus)
    )
    free_modulus = ambient_modulus // core_modulus
    if core_modulus * free_modulus != ambient_modulus:
        raise ValueError("the collision lcm must divide the ambient modulus")
    if gcd(core_modulus, free_modulus) != 1:
        raise ValueError("the free and collision moduli must be coprime")
    core_frequency = (
        0
        if core_modulus == 1
        else frequency * pow(free_modulus, -1, core_modulus)
    )
    return ramanujan_sum(
        free_modulus,
        frequency,
    ) * centered_residue_collision_fourier_formula(
        left_modulus,
        right_modulus,
        left_residue,
        right_residue,
        core_frequency,
    )


def centered_residue_collision_zero_formula(
    common_factor: int,
    left_residue: int,
    right_residue: int,
) -> Fraction:
    """Zero mode of the CRT collision: one congruence minus its unit mean."""

    if common_factor < 1:
        raise ValueError("the common factor must be positive")
    if gcd(left_residue, common_factor) != 1:
        raise ValueError("the left residue must be a unit")
    if gcd(right_residue, common_factor) != 1:
        raise ValueError("the right residue must be a unit")
    return Fraction(
        int((left_residue - right_residue) % common_factor == 0),
    ) - Fraction(1, _euler_phi(common_factor))


def centered_unit_congruence_sum(
    modulus: int,
    left_length: int,
    right_length: int,
    left_multiplier: int,
    right_multiplier: int,
) -> Fraction:
    """Finite centered unit congruence on two initial intervals."""

    if min(
        modulus,
        left_length,
        right_length,
        left_multiplier,
        right_multiplier,
    ) < 1:
        raise ValueError("modulus, lengths, and multipliers must be positive")
    if gcd(left_multiplier, modulus) != 1:
        raise ValueError("the left multiplier must be a unit")
    if gcd(right_multiplier, modulus) != 1:
        raise ValueError("the right multiplier must be a unit")
    unit_mean = Fraction(1, _euler_phi(modulus))
    return sum(
        (
            Fraction(
                int(
                    (
                        left_multiplier * left_value
                        + right_multiplier * right_value
                    )
                    % modulus
                    == 0
                )
            )
            - unit_mean
        )
        for left_value in range(1, left_length + 1)
        if gcd(left_value, modulus) == 1
        for right_value in range(1, right_length + 1)
        if gcd(right_value, modulus) == 1
    )


def centered_unit_congruence_boundary_majorant(
    modulus: int,
    left_length: int,
) -> int:
    """One-boundary-error-per-left-unit majorant for the centered sum."""

    if modulus < 1 or left_length < 1:
        raise ValueError("the modulus and interval length must be positive")
    return sum(
        gcd(left_value, modulus) == 1
        for left_value in range(1, left_length + 1)
    )


@dataclass(frozen=True)
class CenteredKloostermanCrtTerms:
    """The three non-principal terms in a two-factor CRT expansion."""

    both_centered: complex
    left_centered_right_mean: complex
    left_mean_right_centered: complex

    @property
    def summands(self) -> tuple[complex, complex, complex]:
        return (
            self.both_centered,
            self.left_centered_right_mean,
            self.left_mean_right_centered,
        )

    @property
    def total(self) -> complex:
        return sum(self.summands)


@dataclass(frozen=True)
class CenteredCrtUnitMeanLedger:
    """Pointwise saving from local principal means on the unit face."""

    saving_per_mean: Fraction
    one_mean_gap: Fraction
    two_mean_margin: Fraction


@dataclass(frozen=True)
class YoungDualReciprocityLedger:
    """Exponent ledger for Young's additive varying-level large sieve."""

    rational_height: Fraction
    large_sieve_constant: Fraction
    coefficient_energy: Fraction
    row_cauchy: Fraction
    theorem_bound: Fraction
    trivial_bound: Fraction
    saving: Fraction
    margin: Fraction


@dataclass(frozen=True)
class YoungDualGcdLedger:
    """Young-sieve exponent ledger after numerator/modulus gcd extraction."""

    reduced_outer_modulus: Fraction
    reduced_row_length: Fraction
    rational_height: Fraction
    large_sieve_constant: Fraction
    coefficient_energy: Fraction
    theorem_bound: Fraction
    target: Fraction
    margin: Fraction


@dataclass(frozen=True)
class YoungCommonFactorLedger:
    """Young-sieve ledger after an exact common-modulus CRT collision."""

    outer_modulus: Fraction
    row_length: Fraction
    rational_height: Fraction
    coefficient_energy: Fraction
    large_sieve_constant: Fraction
    fixed_common_factor_bound: Fraction
    summed_bound: Fraction
    target: Fraction
    margin: Fraction


@dataclass(frozen=True)
class YoungScalarTransitionLedger:
    """Young ledger after restoring the outer scalar-factor sum."""

    reduced_numerator: Fraction
    outer_modulus: Fraction
    row_length: Fraction
    rational_height: Fraction
    coefficient_energy: Fraction
    row_cauchy: Fraction
    large_sieve_constant: Fraction
    theorem_bound: Fraction
    raw_bound: Fraction
    second_moment_target: Fraction
    theorem_gap: Fraction
    required_saving: Fraction
    theorem_saving: Fraction


@dataclass(frozen=True)
class ScalarTypeIICutoffLedger:
    """Balanced short-short/long-long cutoff geometry."""

    divisor_product_floor: Fraction
    divisor_product_vs_scalar: Fraction
    quotient_ceiling: Fraction
    fixed_divisor_quotient_window: Fraction
    rational_distance: Fraction


@dataclass(frozen=True)
class NearDeterminantBCLedger:
    """Bettin--Chandee audit after separating the near determinant."""

    coefficient_norm: Fraction
    first_parenthetical: Fraction
    second_parenthetical: Fraction
    large_phase_penalty: Fraction
    theorem_bound: Fraction
    target: Fraction
    gap: Fraction


@dataclass(frozen=True)
class MobiusCharacterMeanSquareLedger:
    """Primitive-character screening after the affine delta completion."""

    raw_progression_bound: Fraction
    bombieri_vinogradov_bound: Fraction
    short_character_energy: Fraction
    long_character_energy: Fraction
    ordinary_large_sieve_bound: Fraction
    required_bound: Fraction
    ordinary_saving: Fraction
    required_saving: Fraction
    gap: Fraction
    required_long_character_energy: Fraction


@dataclass(frozen=True)
class PartiallyFixedModulusLedger:
    """Wright's fixed-denominator-factor theorem on the separated packet."""

    coefficient_norm: Fraction
    geometric_factor: Fraction
    fixed_factor: Fraction
    first_term: Fraction
    second_term: Fraction
    third_term: Fraction
    fourth_term: Fraction
    fifth_term: Fraction
    fixed_block_bound: Fraction
    global_bound: Fraction
    target: Fraction
    gap: Fraction


@dataclass(frozen=True)
class PrimeKloostermanLedger:
    """Averaged Kloosterman-over-primes exponent comparison."""

    first_term: Fraction
    second_term: Fraction
    third_term: Fraction
    theorem_bound: Fraction
    trivial_bound: Fraction
    theorem_saving: Fraction
    required_saving: Fraction
    gap: Fraction


@dataclass(frozen=True)
class PrimeSliceVarianceLedger:
    """Selberg-integral and zero-frequency exponent comparison."""

    relative_interval: Fraction
    trivial_bound: Fraction
    target_bound: Fraction
    unconditional_variance: Fraction
    unconditional_cauchy_bound: Fraction
    unconditional_gap: Fraction
    rh_variance: Fraction
    rh_cauchy_bound: Fraction
    rh_margin: Fraction
    density_required_mertens: Fraction
    density_required_ratio: Fraction
    density_required_saving: Fraction


@dataclass(frozen=True)
class ShiftedPrimeMobiusLedger:
    """Power-exponent audit for an averaged shifted-prime theorem."""

    raw_bound: Fraction
    published_power_bound: Fraction
    target_bound: Fraction
    published_power_saving: Fraction
    required_power_saving: Fraction
    gap: Fraction


@dataclass(frozen=True)
class ShiftedPrimeMobiusCoordinates:
    """Coordinates satisfying n+h=s and n+Y=s+d."""

    mobius_shift: int
    translated_base: int


@dataclass(frozen=True)
class TransitionArchimedeanScaleLedger:
    """Power exponents of the actual balanced transition kernel."""

    logarithmic_phase: Fraction
    numerator_fourier_center: Fraction
    afe_argument: Fraction
    zeta_balance: Fraction
    scalar_dilation: Fraction
    poisson_sample: Fraction


@dataclass(frozen=True)
class TwoCutoffProductCoefficient:
    """Short, long, and combined coefficients at one product ``m=bc``."""

    short_short: int
    long_long: int
    combined: int


@dataclass(frozen=True)
class TwoCutoffCenteredSplit:
    """Exact density/centered/complementary decomposition at one n."""

    density: Fraction
    centered: Fraction
    complementary: Fraction
    total: Fraction


@dataclass(frozen=True)
class CentralMajorArcMertensLedger:
    """Conditional fixed-power ledger for the additive central arc."""

    raw_bound: Fraction
    required_saving: Fraction
    available_saving: Fraction
    conditional_bound: Fraction
    gap: Fraction


@dataclass(frozen=True)
class VinogradovDenominatorCoverageLedger:
    """Rational-denominator interval for a fixed Möbius power saving."""

    polynomial_length: Fraction
    required_relative_saving: Fraction
    type_i_bound: Fraction
    target_bound: Fraction
    theorem_denominator_floor: Fraction
    theorem_denominator_ceiling: Fraction
    actual_denominator_floor: Fraction
    actual_denominator_ceiling: Fraction
    overlap_floor: Fraction
    overlap_ceiling: Fraction
    has_positive_width_overlap: bool


@dataclass(frozen=True)
class NonzeroReducedDenominatorLedger:
    """Bound for one nonzero reduced-denominator block through R=D."""

    coefficient_weight: Fraction
    outer_energy: Fraction
    shift_energy: Fraction
    outer_large_sieve_constant: Fraction
    shift_large_sieve_constant: Fraction
    fourier_decay: Fraction
    bound: Fraction
    target: Fraction
    margin: Fraction


@dataclass(frozen=True)
class HighReducedDenominatorLedger:
    """Small numerator/cofactor geometry above the shift length."""

    reduced_denominator: Fraction
    reduced_numerator: Fraction
    complementary_cofactor: Fraction
    lifted_numerator: Fraction


@dataclass(frozen=True)
class HighEdgePolytopeLedger:
    """Quotient-aware high-denominator exponent ledger."""

    complementary_quotient: Fraction
    product_length: Fraction
    reduced_denominator: Fraction
    ramanujan_cofactor: Fraction
    reduced_numerator: Fraction
    full_modulus_numerator: Fraction
    large_sieve_bound: Fraction
    target: Fraction
    large_sieve_gap: Fraction
    square_root_hybrid_saving: Fraction
    square_root_hybrid_margin: Fraction


@dataclass(frozen=True)
class ReducedFrequencyLift:
    """One primitive reduced frequency lifted to a full modulus."""

    reduced_denominator: int
    primitive_numerator: int
    cofactor: int
    full_numerator: int


@dataclass(frozen=True)
class MobiusConvolutionRationalProxyLedger:
    """Published ``mu*mu`` rational-phase savings versus the edge gap."""

    product_length: Fraction
    denominator_length: Fraction
    denominator_term_saving: Fraction
    interior_term_saving: Fraction
    upper_denominator_term_saving: Fraction
    available_saving: Fraction
    required_saving: Fraction
    margin: Fraction
    structurally_applicable: bool


@dataclass(frozen=True)
class ReciprocalMonomialCoverageLedger:
    """Published monomial-sum half-power cap versus required saving."""

    full_modulus_numerator: Fraction
    phase_variation: Fraction
    required_saving: Fraction
    published_saving_cap: Fraction
    margin: Fraction
    covered: bool


@dataclass(frozen=True)
class CoupledProductCircleLedger:
    """Two published product bounds on one precompletion circle band."""

    complementary_left: Fraction
    complementary_right: Fraction
    quotient_length: Fraction
    complementary_product: Fraction
    circle_denominator: Fraction
    quotient_gcd: Fraction
    effective_denominator: Fraction
    approximation_loss: Fraction
    complementary_type_ii_constant: Fraction
    shifted_type_ii_constant: Fraction
    quotient_stratum: Fraction
    circle_kernel_mass: Fraction
    pointwise_bound: Fraction
    cauchy_bound: Fraction
    best_bound: Fraction
    target: Fraction
    margin: Fraction
    covered: bool


@dataclass(frozen=True)
class ShiftedDivisorProxyLedger:
    """Published divisor-shift exponents versus the Möbius packet."""

    fixed_shift_error: Fraction
    summed_fixed_shift_error: Fraction
    summed_fixed_shift_margin: Fraction
    selberg_endpoint: Fraction
    averaged_shift_square_error: Fraction
    averaged_shift_moment_error: Fraction
    averaged_shift_error: Fraction
    averaged_shift_margin: Fraction
    raw_zero_mode: Fraction
    zero_mode_required_saving: Fraction
    standard_divisor_coefficients: bool
    zero_mode_algebraically_vanishing: bool
    covered: bool


@dataclass(frozen=True)
class MultipleMobiusAdditiveLedger:
    """Exponent mismatch for the nearest additive three-variable theorem."""

    product_length: Fraction
    fixed_quotient_bound: Fraction
    summed_bound: Fraction
    target: Fraction
    gap: Fraction


@dataclass(frozen=True)
class PostcompletionCutoffLedger:
    """Type-I completion and complementary-divisor exponent geometry."""

    divisor_product_floor: Fraction
    quotient_ceiling: Fraction
    fixed_product_quotient_window: Fraction
    high_product_quotient_ceiling: Fraction
    sharp_type_i_boundary: Fraction
    smooth_type_i_tail: Fraction
    sharp_margin: Fraction
    smooth_margin: Fraction


@dataclass(frozen=True)
class CenteredLowModulusLargeSieveLedger:
    """Exponent ledger for centered low product moduli."""

    coefficient_energy: Fraction
    outer_energy: Fraction
    large_sieve_constant: Fraction
    fourier_decay: Fraction
    bound: Fraction
    target: Fraction
    margin: Fraction


@dataclass(frozen=True)
class AsymptoticSieveTransitionLedger:
    """Exponent syntax of the FI parity-breaking bilinear axiom."""

    square_root_level: Fraction
    square_root_ambient: Fraction
    complementary_quotient: Fraction
    b3_coefficient_ceiling: Fraction
    short_divisor_cutoff: Fraction
    quotient_at_lower_endpoint: bool
    cutoff_inside_b3_ceiling: bool


@dataclass(frozen=True)
class ComplementaryOneFactorCoverageLedger:
    """Coverage of a complementary factor by an all-interval theorem."""

    maximum_factor_length: Fraction
    required_factor_length: Fraction
    coverage_gap: Fraction
    covered: bool


@dataclass(frozen=True)
class TransitionNumeratorCompletionLedger:
    """Exponent ledger after Poisson completion in h."""

    dual_length: Fraction
    numerator_saving: Fraction
    completed_bound: Fraction
    target: Fraction
    gap: Fraction


@dataclass(frozen=True)
class TransitionNumeratorDualCoordinates:
    """Exact relation delta = ell*d forced by the transition scales."""

    dual_frequency: int
    determinant: int
    numerator: int


@dataclass(frozen=True)
class CenteredTransitionCompletionLedger:
    """Short-box imbalance of the centered numerator transform."""

    point_mass: Fraction
    uniform_background: Fraction
    point_over_background: Fraction


@dataclass(frozen=True)
class NearDeterminantCoordinates:
    """One point on the affine line ``B*k-g*q=d``."""

    base_modulus: int
    base_quotient: int
    modulus: int
    quotient: int


@dataclass(frozen=True)
class NearDeterminantDualCoordinates:
    """One point satisfying both B*k-g*q=d and h+n*q=j*d."""

    modulus: int
    determinant_quotient: int
    numerator: int
    dual_quotient: int


@dataclass(frozen=True)
class CommonFactorMarginalLedger:
    """Exponent bounds for the three Ramanujan marginals in the CRT formula."""

    one_sided_bound: Fraction
    all_mean_bound: Fraction
    target: Fraction
    one_sided_margin: Fraction
    all_mean_margin: Fraction


def young_dual_reciprocity_ledger(
    outer_modulus: Fraction,
    row_length: Fraction,
    numerator_length: Fraction,
    denominator_length: Fraction,
    required_saving: Fraction,
) -> YoungDualReciprocityLedger:
    """Audit the unit-dual reciprocity route in exact T-exponents.

    The additive convolution of two numerator intervals of exponent
    ``numerator_length`` has second moment of exponent three times that
    length.  The denominator family contributes one further counting
    exponent.  Young's large-sieve constant is ``Q^2 + N``.
    """

    if min(
        outer_modulus,
        row_length,
        numerator_length,
        denominator_length,
        required_saving,
    ) < 0:
        raise ValueError("exponents must be nonnegative")
    rational_height = numerator_length + denominator_length
    large_sieve_constant = max(2 * outer_modulus, rational_height)
    coefficient_energy = denominator_length + 3 * numerator_length
    row_cauchy = (outer_modulus + row_length) / 2
    theorem_bound = row_cauchy + (
        large_sieve_constant + coefficient_energy
    ) / 2
    trivial_bound = (
        2 * outer_modulus + row_length + 2 * numerator_length
    )
    saving = trivial_bound - theorem_bound
    return YoungDualReciprocityLedger(
        rational_height=rational_height,
        large_sieve_constant=large_sieve_constant,
        coefficient_energy=coefficient_energy,
        row_cauchy=row_cauchy,
        theorem_bound=theorem_bound,
        trivial_bound=trivial_bound,
        saving=saving,
        margin=saving - required_saving,
    )


def young_scalar_transition_ledger(
    *,
    r_length: Fraction,
    total_modulus: Fraction,
    scalar_fixed: Fraction,
    oscillatory_modulus: Fraction,
    h_length: Fraction,
    delta_length: Fraction,
    common_factor: Fraction,
) -> YoungScalarTransitionLedger:
    """Audit Young after the scalar-gcd factors are summed by triangle.

    This is the transition face of (9.187): the Ramanujan factor is one,
    the oscillatory modulus has the same exponent as the h-interval, and
    the fixed scalar factors have total exponent g_a+j.  The reduced
    delta interval has exponent ell-(g_a+j).  A dispersion step has
    second-moment target R*S^2, hence exponent rho+2*sigma.
    """

    values = (
        r_length,
        total_modulus,
        scalar_fixed,
        oscillatory_modulus,
        h_length,
        delta_length,
        common_factor,
    )
    if any(value < 0 for value in values):
        raise ValueError("all exponent lengths must be nonnegative")
    if scalar_fixed + oscillatory_modulus != total_modulus:
        raise ValueError("the fixed and oscillatory factors must form S")
    if h_length != oscillatory_modulus:
        raise ValueError("this transition ledger requires H=lambda")
    reduced_numerator = delta_length - scalar_fixed
    if reduced_numerator < 0:
        raise ValueError("the reduced numerator interval is empty")
    base_row_length = 2 * oscillatory_modulus - r_length
    if base_row_length < 0:
        raise ValueError("the nonzero dispersion row is empty")
    if common_factor > min(
        oscillatory_modulus,
        reduced_numerator,
        base_row_length,
    ):
        raise ValueError("the common factor exceeds a reduced length")

    outer_modulus = oscillatory_modulus - common_factor
    row_length = base_row_length - common_factor
    rational_height = (
        reduced_numerator
        + oscillatory_modulus
        - 2 * common_factor
    )
    coefficient_energy = (
        oscillatory_modulus
        + 3 * reduced_numerator
        - 2 * common_factor
    )
    row_cauchy = (outer_modulus + row_length) / 2
    large_sieve_constant = max(
        2 * outer_modulus,
        rational_height,
    )
    theorem_bound = (
        scalar_fixed
        + common_factor
        + row_cauchy
        + (large_sieve_constant + coefficient_energy) / 2
    )
    raw_bound = (
        scalar_fixed
        + 4 * oscillatory_modulus
        - 2 * common_factor
        - r_length
        + 2 * reduced_numerator
    )
    second_moment_target = r_length + 2 * total_modulus
    return YoungScalarTransitionLedger(
        reduced_numerator=reduced_numerator,
        outer_modulus=outer_modulus,
        row_length=row_length,
        rational_height=rational_height,
        coefficient_energy=coefficient_energy,
        row_cauchy=row_cauchy,
        large_sieve_constant=large_sieve_constant,
        theorem_bound=theorem_bound,
        raw_bound=raw_bound,
        second_moment_target=second_moment_target,
        theorem_gap=theorem_bound - second_moment_target,
        required_saving=raw_bound - second_moment_target,
        theorem_saving=raw_bound - theorem_bound,
    )


def common_factor_marginal_ledger(
    common_factor: Fraction,
) -> CommonFactorMarginalLedger:
    """Audit the Ramanujan marginals after summing normalized means.

    A one-sided marginal sums one normalized Ramanujan factor over its
    free cofactor modulus and leaves 1/phi(t).  The dyadic t-sum absorbs
    that factor, so only u, the nonzero row, and the two numerator
    intervals remain.  The all-mean term sums normalized Ramanujan
    factors over t, u, and v, leaving only the row and numerator boxes.
    """

    if common_factor < 0 or common_factor > 2:
        raise ValueError("the common factor must lie in the nonzero dual range")
    one_sided_bound = Fraction(17, 2) - 2 * common_factor
    all_mean_bound = Fraction(6) - common_factor
    target = Fraction(9)
    return CommonFactorMarginalLedger(
        one_sided_bound=one_sided_bound,
        all_mean_bound=all_mean_bound,
        target=target,
        one_sided_margin=target - one_sided_bound,
        all_mean_margin=target - all_mean_bound,
    )


def young_common_factor_ledger(
    common_factor: Fraction,
    row_gcd: Fraction = Fraction(0),
    numerator_gcd: Fraction = Fraction(0),
    rational_gcd: Fraction = Fraction(0),
) -> YoungCommonFactorLedger:
    """Audit nonzero dual modes with a common modulus of the given exponent.

    Write m=t*u and n=t*v.  Numerator completion makes the two centered
    residue point masses compatible only when t divides
    M*delta + L*delta'.  The same t then cancels from the rational
    numerator and denominator in Young's additive large sieve.  For a
    fixed t this lowers both the convolution energy and the denominator
    count, while summing the dyadic t-box costs one copy of its exponent.
    The other three arguments extract the same row, outer-numerator, and
    lowest-rational gcd strata as in young_dual_reciprocity_gcd_ledger.
    """

    if common_factor < 0:
        raise ValueError("the common-factor exponent must be nonnegative")
    if common_factor > 2:
        raise ValueError("this ledger is for the nonzero dual range t <= T^2")
    if row_gcd < 0 or numerator_gcd < 0 or rational_gcd < 0:
        raise ValueError("gcd exponents must be nonnegative")
    numerator_length = Fraction(2) - common_factor
    outer_length = Fraction(5, 2) - common_factor
    if row_gcd > numerator_length:
        raise ValueError("the row gcd cannot exceed the row length")
    if row_gcd + numerator_gcd > outer_length:
        raise ValueError("the outer gcds cannot exceed the modulus")
    if numerator_gcd + rational_gcd > numerator_length:
        raise ValueError("the rational gcd cannot exceed the numerator")

    outer_modulus = outer_length - row_gcd - numerator_gcd
    row_length = numerator_length - row_gcd
    rational_height = (
        Fraction(9, 2)
        - 2 * common_factor
        - numerator_gcd
        - 2 * rational_gcd
    )
    coefficient_energy = (
        Fraction(17, 2) - 2 * common_factor - 2 * rational_gcd
    )
    large_sieve_constant = max(
        2 * outer_modulus,
        rational_height,
    )
    row_cauchy = (outer_modulus + row_length) / 2
    extracted_factor_count = row_gcd + numerator_gcd + rational_gcd
    fixed_common_factor_bound = (
        extracted_factor_count
        + row_cauchy
        + (large_sieve_constant + coefficient_energy) / 2
    )
    summed_bound = fixed_common_factor_bound + common_factor
    target = Fraction(9)
    return YoungCommonFactorLedger(
        outer_modulus=outer_modulus,
        row_length=row_length,
        rational_height=rational_height,
        coefficient_energy=coefficient_energy,
        large_sieve_constant=large_sieve_constant,
        fixed_common_factor_bound=fixed_common_factor_bound,
        summed_bound=summed_bound,
        target=target,
        margin=target - summed_bound,
    )


def young_dual_reciprocity_gcd_ledger(
    row_gcd: Fraction,
    numerator_gcd: Fraction,
    rational_gcd: Fraction = Fraction(0),
) -> YoungDualGcdLedger:
    """Audit every gcd stratum of the primitive Young-sieve application.

    Here ``row_gcd`` is the exponent of ``d = (k, q)`` and
    ``numerator_gcd`` is the exponent of ``e = (A, q / d)``, and
    ``rational_gcd`` is the exponent of ``g = (A/e, u)`` needed to put
    the rational numerator and denominator in lowest terms.  Extracting
    these factors leaves outer modulus exponent ``5/2-d-e``, row length
    ``2-d``, and rational height ``9/2-e-2g``.

    On a fixed ``g``-stratum, the denominator count loses ``g`` and the
    additive-convolution energy on numerators divisible by ``g`` loses
    another ``g``: the elementary bound is ``D^3/g``.  Thus the original
    coefficient-energy exponent ``17/2`` becomes ``17/2-2g``.  We charge
    ``d+e+g`` for selecting all extracted factors, a conservative finite
    exponent audit in which the two ``g`` savings exactly pay for the
    added ``g``-sum.
    """

    if row_gcd < 0 or numerator_gcd < 0 or rational_gcd < 0:
        raise ValueError("gcd exponents must be nonnegative")
    if row_gcd > 2:
        raise ValueError("the row gcd cannot exceed the row length")
    if row_gcd + numerator_gcd > Fraction(5, 2):
        raise ValueError("the extracted gcds cannot exceed the modulus")
    if numerator_gcd > 2:
        raise ValueError("the numerator gcd cannot exceed its length")
    if numerator_gcd + rational_gcd > 2:
        raise ValueError("the rational gcd cannot exceed the numerator")

    reduced_outer_modulus = Fraction(5, 2) - row_gcd - numerator_gcd
    reduced_row_length = Fraction(2) - row_gcd
    rational_height = (
        Fraction(9, 2) - numerator_gcd - 2 * rational_gcd
    )
    large_sieve_constant = max(
        2 * reduced_outer_modulus,
        rational_height,
    )
    row_cauchy = (reduced_outer_modulus + reduced_row_length) / 2
    coefficient_energy = Fraction(17, 2) - 2 * rational_gcd
    extracted_factor_count = row_gcd + numerator_gcd + rational_gcd
    theorem_bound = (
        extracted_factor_count
        + row_cauchy
        + (large_sieve_constant + coefficient_energy) / 2
    )
    target = Fraction(9)
    return YoungDualGcdLedger(
        reduced_outer_modulus=reduced_outer_modulus,
        reduced_row_length=reduced_row_length,
        rational_height=rational_height,
        large_sieve_constant=large_sieve_constant,
        coefficient_energy=coefficient_energy,
        theorem_bound=theorem_bound,
        target=target,
        margin=target - theorem_bound,
    )


def centered_crt_unit_mean_ledger(
    local_factor_exponent: Fraction,
    required_saving: Fraction,
) -> CenteredCrtUnitMeanLedger:
    """Compare local mean suppression with a required global saving.

    For unit Kloosterman arguments, a local centered transform has Weil
    size ``q^(1/2+o(1))`` while its principal mean has size
    ``q^(-1+o(1))``.  Replacing one centered local factor by its mean
    therefore saves ``q^(3/2-o(1))``.
    """

    if local_factor_exponent < 0 or required_saving < 0:
        raise ValueError("exponents must be nonnegative")
    saving_per_mean = Fraction(3, 2) * local_factor_exponent
    return CenteredCrtUnitMeanLedger(
        saving_per_mean=saving_per_mean,
        one_mean_gap=max(Fraction(0), required_saving - saving_per_mean),
        two_mean_margin=max(
            Fraction(0), 2 * saving_per_mean - required_saving
        ),
    )


def dual_unit_reciprocity_phase(
    left_modulus: int,
    right_modulus: int,
    left_dual: int,
    right_dual: int,
    frequency: int,
    left_numerator: int,
    right_numerator: int,
) -> complex:
    """Original pair of cross-inverse phases on positive dual modes."""

    if min(left_modulus, right_modulus, left_dual, right_dual) < 1:
        raise ValueError("moduli and dual frequencies must be positive")
    if gcd(left_modulus, right_modulus * left_dual) != 1:
        raise ValueError("the left cross inverse must exist")
    if gcd(right_modulus, left_modulus * right_dual) != 1:
        raise ValueError("the right cross inverse must exist")
    left_inverse = pow(
        (right_modulus * left_dual) % left_modulus,
        -1,
        left_modulus,
    )
    right_inverse = pow(
        (left_modulus * right_dual) % right_modulus,
        -1,
        right_modulus,
    )
    return cmath.exp(
        2j
        * cmath.pi
        * (-frequency * left_numerator * left_inverse)
        / left_modulus
    ) * cmath.exp(
        2j
        * cmath.pi
        * (frequency * right_numerator * right_inverse)
        / right_modulus
    )


def dual_unit_reciprocity_phase_formula(
    left_modulus: int,
    right_modulus: int,
    left_dual: int,
    right_dual: int,
    frequency: int,
    left_numerator: int,
    right_numerator: int,
) -> complex:
    """One rational character, one fixed twist, and a small real phase."""

    if min(left_modulus, right_modulus, left_dual, right_dual) < 1:
        raise ValueError("moduli and dual frequencies must be positive")
    combined_modulus = right_modulus * left_dual * right_dual
    if gcd(left_modulus, combined_modulus) != 1:
        raise ValueError("the combined rational denominator must be a unit")
    if gcd(right_dual, right_modulus) != 1:
        raise ValueError("the right dual frequency must be a unit")
    right_dual_inverse = pow(
        right_dual % right_modulus,
        -1,
        right_modulus,
    )
    fixed_twist = (
        right_dual * right_dual_inverse - 1
    ) // right_modulus
    left_inverse = pow(
        left_modulus % combined_modulus,
        -1,
        combined_modulus,
    )
    combined_numerator = (
        right_dual * left_numerator
        + left_dual * right_numerator
    )
    main_phase = cmath.exp(
        2j
        * cmath.pi
        * (
            frequency * combined_numerator * left_inverse
            % combined_modulus
        )
        / combined_modulus
    )
    if right_dual == 1:
        twist_phase = 1 + 0j
    else:
        inverse_mod_fixed = pow(
            left_modulus % right_dual,
            -1,
            right_dual,
        )
        twist_phase = cmath.exp(
            2j
            * cmath.pi
            * (
                frequency
                * fixed_twist
                * right_numerator
                * inverse_mod_fixed
                % right_dual
            )
            / right_dual
        )
    real_correction = cmath.exp(
        -2j
        * cmath.pi
        * frequency
        * left_numerator
        / (left_modulus * right_modulus * left_dual)
    )
    return main_phase * twist_phase * real_correction


def centered_kloosterman_crt_terms(
    left_factor: int,
    right_factor: int,
    inverse_numerator: int,
    linear_frequency: int,
) -> CenteredKloostermanCrtTerms:
    """Factor a centered transform over two coprime CRT factors.

    If ``m = left_factor * right_factor``, the raw Kloosterman sum is
    the product of its two local sums.  Subtracting the product of the
    two local means leaves exactly three terms: centered-centered and
    the two centered-mean cross terms.  In particular there is no
    all-principal term.
    """

    if left_factor < 1 or right_factor < 1:
        raise ValueError("CRT factors must be positive")
    if gcd(left_factor, right_factor) != 1:
        raise ValueError("CRT factors must be coprime")

    right_inverse_mod_left = (
        0
        if left_factor == 1
        else pow(right_factor, -1, left_factor)
    )
    left_inverse_mod_right = (
        0
        if right_factor == 1
        else pow(left_factor, -1, right_factor)
    )
    left_inverse_numerator = (
        inverse_numerator * right_inverse_mod_left
    )
    left_linear_frequency = (
        linear_frequency * right_inverse_mod_left
    )
    right_inverse_numerator = (
        inverse_numerator * left_inverse_mod_right
    )
    right_linear_frequency = (
        linear_frequency * left_inverse_mod_right
    )

    left_centered = centered_kloosterman_transform(
        left_factor,
        left_inverse_numerator,
        left_linear_frequency,
    )
    right_centered = centered_kloosterman_transform(
        right_factor,
        right_inverse_numerator,
        right_linear_frequency,
    )
    left_mean = Fraction(
        ramanujan_sum(left_factor, inverse_numerator)
        * ramanujan_sum(left_factor, linear_frequency),
        _euler_phi(left_factor),
    )
    right_mean = Fraction(
        ramanujan_sum(right_factor, inverse_numerator)
        * ramanujan_sum(right_factor, linear_frequency),
        _euler_phi(right_factor),
    )
    return CenteredKloostermanCrtTerms(
        both_centered=left_centered * right_centered,
        left_centered_right_mean=left_centered * float(right_mean),
        left_mean_right_centered=float(left_mean) * right_centered,
    )


def factorized_centered_kloosterman_numerator_fourier(
    left_factor: int,
    right_factor: int,
    numerator_multiplier: int,
    linear_frequency: int,
    dual_frequency: int,
) -> complex:
    """Direct numerator Fourier transform of the fully centered CRT term."""

    modulus = left_factor * right_factor
    if left_factor < 1 or right_factor < 1:
        raise ValueError("CRT factors must be positive")
    if gcd(left_factor, right_factor) != 1:
        raise ValueError("CRT factors must be coprime")
    if gcd(numerator_multiplier, modulus) != 1:
        raise ValueError("the numerator multiplier must be a unit")
    right_inverse_mod_left = (
        0
        if left_factor == 1
        else pow(right_factor, -1, left_factor)
    )
    left_inverse_mod_right = (
        0
        if right_factor == 1
        else pow(left_factor, -1, right_factor)
    )
    return sum(
        centered_kloosterman_transform(
            left_factor,
            numerator_multiplier * numerator * right_inverse_mod_left,
            linear_frequency * right_inverse_mod_left,
        )
        * centered_kloosterman_transform(
            right_factor,
            numerator_multiplier * numerator * left_inverse_mod_right,
            linear_frequency * left_inverse_mod_right,
        )
        * cmath.exp(
            -2j * cmath.pi * dual_frequency * numerator / modulus
        )
        for numerator in range(modulus)
    )


def factorized_centered_kloosterman_numerator_fourier_formula(
    left_factor: int,
    right_factor: int,
    numerator_multiplier: int,
    linear_frequency: int,
    dual_frequency: int,
) -> complex:
    """CRT product formula for the fully centered numerator transform."""

    modulus = left_factor * right_factor
    if left_factor < 1 or right_factor < 1:
        raise ValueError("CRT factors must be positive")
    if gcd(left_factor, right_factor) != 1:
        raise ValueError("CRT factors must be coprime")
    if gcd(numerator_multiplier, modulus) != 1:
        raise ValueError("the numerator multiplier must be a unit")
    right_inverse_mod_left = (
        0
        if left_factor == 1
        else pow(right_factor, -1, left_factor)
    )
    left_inverse_mod_right = (
        0
        if right_factor == 1
        else pow(left_factor, -1, right_factor)
    )
    left_transform = centered_kloosterman_numerator_fourier_formula(
        left_factor,
        numerator_multiplier * right_inverse_mod_left,
        linear_frequency * right_inverse_mod_left,
        dual_frequency * right_inverse_mod_left,
    )
    right_transform = centered_kloosterman_numerator_fourier_formula(
        right_factor,
        numerator_multiplier * left_inverse_mod_right,
        linear_frequency * left_inverse_mod_right,
        dual_frequency * left_inverse_mod_right,
    )
    return left_transform * right_transform


def coprime_centered_inverse_cross_fourier_factorization(
    left_modulus: int,
    left_numerator: int,
    right_modulus: int,
    right_numerator: int,
    frequency: int,
) -> complex:
    """CRT tensor factorization of a coprime centered cross coefficient."""

    if left_modulus < 1 or right_modulus < 1:
        raise ValueError("moduli must be positive")
    if gcd(left_modulus, right_modulus) != 1:
        raise ValueError("the tensor factorization requires coprime moduli")
    if left_modulus == 1:
        right_inverse_mod_left = 0
    else:
        right_inverse_mod_left = pow(
            right_modulus,
            -1,
            left_modulus,
        )
    if right_modulus == 1:
        left_inverse_mod_right = 0
    else:
        left_inverse_mod_right = pow(
            left_modulus,
            -1,
            right_modulus,
        )
    return centered_kloosterman_transform(
        left_modulus,
        left_numerator,
        -frequency * right_inverse_mod_left,
    ) * centered_kloosterman_transform(
        right_modulus,
        -right_numerator,
        -frequency * left_inverse_mod_right,
    )


def two_sided_centered_kloosterman_crt_terms(
    left_short_factor: int,
    left_long_factor: int,
    left_numerator: int,
    right_short_factor: int,
    right_long_factor: int,
    right_numerator: int,
    frequency: int,
) -> tuple[complex, ...]:
    """Nine-term Type-I/II expansion of a coprime centered tensor."""

    left_modulus = left_short_factor * left_long_factor
    right_modulus = right_short_factor * right_long_factor
    if min(
        left_short_factor,
        left_long_factor,
        right_short_factor,
        right_long_factor,
    ) < 1:
        raise ValueError("CRT factors must be positive")
    if gcd(left_short_factor, left_long_factor) != 1:
        raise ValueError("left CRT factors must be coprime")
    if gcd(right_short_factor, right_long_factor) != 1:
        raise ValueError("right CRT factors must be coprime")
    if gcd(left_modulus, right_modulus) != 1:
        raise ValueError("left and right moduli must be coprime")

    right_inverse_mod_left = (
        0
        if left_modulus == 1
        else pow(right_modulus, -1, left_modulus)
    )
    left_inverse_mod_right = (
        0
        if right_modulus == 1
        else pow(left_modulus, -1, right_modulus)
    )
    left_terms = centered_kloosterman_crt_terms(
        left_short_factor,
        left_long_factor,
        left_numerator,
        -frequency * right_inverse_mod_left,
    )
    right_terms = centered_kloosterman_crt_terms(
        right_short_factor,
        right_long_factor,
        -right_numerator,
        -frequency * left_inverse_mod_right,
    )
    return tuple(
        left_term * right_term
        for left_term in left_terms.summands
        for right_term in right_terms.summands
    )


def _validate_squarefree_scalar_factors(
    a_gcd: int, b_gcd: int, reduced_modulus: int, shift: int
) -> int:
    if min(a_gcd, b_gcd, reduced_modulus) < 1:
        raise ValueError("the scalar factors must be positive")
    modulus = a_gcd * b_gcd * reduced_modulus
    if mobius(modulus) == 0:
        raise ValueError("the three scalar factors must have squarefree product")
    if reduced_modulus == 1:
        raise ValueError("the off-axis divisor spectrum is stated for q>1")
    if gcd(shift, modulus) != 1:
        raise ValueError("the shift must be a unit modulo s")
    return modulus


def squarefree_scalar_stratum_completed_sum(
    a_gcd: int,
    b_gcd: int,
    reduced_modulus: int,
    shift: int,
    h_length: int,
    delta_length: int,
) -> complex:
    """Direct Möbius-weighted completed sum on one ordered gcd stratum."""

    modulus = _validate_squarefree_scalar_factors(
        a_gcd, b_gcd, reduced_modulus, shift
    )
    if min(h_length, delta_length) < 1:
        raise ValueError("the interval lengths must be positive")
    total = sum(
        _finite_interval_fourier(h_length, a, modulus)
        * _finite_interval_fourier(delta_length, b, modulus)
        * cmath.exp(
            2j
            * cmath.pi
            * ((shift * a * b) % modulus)
            / modulus
        )
        for a in range(modulus)
        if gcd(a, modulus) == a_gcd
        for b in range(modulus)
        if gcd(b, modulus // a_gcd) == b_gcd
    )
    return Fraction(mobius(modulus), modulus) * total


def squarefree_scalar_stratum_divisor_spectrum(
    a_gcd: int,
    b_gcd: int,
    reduced_modulus: int,
    shift: int,
    h_length: int,
    delta_length: int,
) -> complex:
    """Exact migrated divisor spectrum of one ordered scalar stratum.

    This composes the two lift identities with the Möbius-weighted
    double-unit spectrum.  It is a finite equality, not an estimate.
    """

    _validate_squarefree_scalar_factors(
        a_gcd, b_gcd, reduced_modulus, shift
    )
    if min(h_length, delta_length) < 1:
        raise ValueError("the interval lengths must be positive")
    prefactor = Fraction(
        mobius(a_gcd) * mobius(b_gcd),
        b_gcd * reduced_modulus,
    )
    total = 0j
    for h in range(1, h_length + 1):
        scalar_ramanujan = ramanujan_sum(b_gcd, h)
        for delta_reduced in range(1, delta_length // a_gcd + 1):
            for divisor_modulus in divisors(reduced_modulus):
                if gcd(divisor_modulus, delta_reduced) != 1:
                    continue
                cofactor = reduced_modulus // divisor_modulus
                coefficient = (
                    divisor_modulus
                    * mobius(divisor_modulus)
                    * ramanujan_sum(cofactor, h)
                )
                if divisor_modulus == 1:
                    phase = 1 + 0j
                else:
                    inverse = pow(
                        (shift * cofactor) % divisor_modulus,
                        -1,
                        divisor_modulus,
                    )
                    scalar_inverse = pow(
                        b_gcd, -1, divisor_modulus
                    )
                    phase = cmath.exp(
                        2j
                        * cmath.pi
                        * (
                            (
                                -scalar_inverse
                                * h
                                * delta_reduced
                                * inverse
                            )
                            % divisor_modulus
                        )
                        / divisor_modulus
                    )
                total += scalar_ramanujan * coefficient * phase
    return prefactor * total


def coprimality_migrated_scalar_stratum_spectrum(
    a_gcd: int,
    b_gcd: int,
    reduced_modulus: int,
    shift: int,
    h_length: int,
    delta_length: int,
) -> complex:
    """Triple-divisor spectrum after expanding ``(delta,q)=1``.

    Write ``q=j*l*n`` and ``delta=j*delta0``.  On squarefree ``q`` the
    outer sign and the coprimality sign satisfy

    ``mu(q) * mu(j) = mu(l*n) * mu(j) = mu(l) * mu(n) * mu(j)``,

    while the sign already present in the double-unit divisor spectrum
    cancels the ``j`` and ``n`` signs.  The resulting coefficient is
    ``mu(l)/n`` and the phase has modulus ``l``.  In particular, the
    product coefficient in ``h*delta0`` is independent of that modulus.
    This is an exact finite identity, not an analytic estimate.
    """

    _validate_squarefree_scalar_factors(
        a_gcd, b_gcd, reduced_modulus, shift
    )
    if min(h_length, delta_length) < 1:
        raise ValueError("the interval lengths must be positive")
    outer_sign = mobius(a_gcd) * mobius(b_gcd)
    total = 0j
    for delta_gcd in divisors(reduced_modulus):
        remaining = reduced_modulus // delta_gcd
        for oscillatory_modulus in divisors(remaining):
            ramanujan_factor = remaining // oscillatory_modulus
            coefficient = Fraction(
                outer_sign * mobius(oscillatory_modulus),
                b_gcd * ramanujan_factor,
            )
            delta_endpoint = delta_length // (a_gcd * delta_gcd)
            for h in range(1, h_length + 1):
                ramanujan = ramanujan_sum(
                    b_gcd * ramanujan_factor, h
                )
                for delta_reduced in range(1, delta_endpoint + 1):
                    if oscillatory_modulus == 1:
                        phase = 1 + 0j
                    else:
                        scalar_inverse = pow(
                            b_gcd, -1, oscillatory_modulus
                        )
                        shifted_inverse = pow(
                            (
                                shift * ramanujan_factor
                            )
                            % oscillatory_modulus,
                            -1,
                            oscillatory_modulus,
                        )
                        phase = cmath.exp(
                            2j
                            * cmath.pi
                            * (
                                -scalar_inverse
                                * h
                                * delta_reduced
                                * shifted_inverse
                                % oscillatory_modulus
                            )
                            / oscillatory_modulus
                        )
                    total += coefficient * ramanujan * phase
    return total


def scalar_stratum_bettin_chandee_ledger(
    *,
    r_length: Fraction,
    scalar_a_gcd: Fraction,
    delta_gcd_factor: Fraction,
    ramanujan_factor: Fraction,
    oscillatory_modulus: Fraction,
    h_length: Fraction,
    delta_length: Fraction,
    scalar_b_gcd: Fraction,
) -> KloostermanFractionTripleLedger:
    """Audit Bettin--Chandee Theorem 1 on the exact triple spectrum.

    All arguments are exponents of ``T``.  The squarefree scalar factors
    have exponents ``g_a, g_b, j, n, l`` and hence total modulus exponent
    ``sigma=g_a+g_b+j+n+l``.  After ``delta=j*delta0``, the Kloosterman
    numerator has product length ``H*L/(g_a*j)``.  Summing the fixed
    factors termwise costs only ``g_a+j`` because the exact coefficient
    ``1/(g_b*n)`` cancels the other two counting lengths.
    """

    values = (
        r_length,
        scalar_a_gcd,
        delta_gcd_factor,
        ramanujan_factor,
        oscillatory_modulus,
        h_length,
        delta_length,
        scalar_b_gcd,
    )
    if any(value < 0 for value in values):
        raise ValueError("all exponent lengths must be nonnegative")
    product_length = (
        h_length
        + delta_length
        - scalar_a_gcd
        - delta_gcd_factor
    )
    if product_length < 0:
        raise ValueError("the reduced product interval is empty")
    coefficient_support = (
        r_length + oscillatory_modulus + product_length
    )
    # For m=g_b*n, divisor expansion gives
    # sum_{h<=H}|c_m(h)|^2 << m*(H+m)*T^eps.  Relative to the raw
    # product support, the coefficient norm therefore has the following
    # piecewise cost.  It is m^(1/2) when m<=H and only gets worse when
    # m>H.
    ramanujan_scale = scalar_b_gcd + ramanujan_factor
    ramanujan_norm_cost = (
        ramanujan_scale
        + max(h_length, ramanujan_scale)
        - h_length
    ) / 2
    coefficient_norms = coefficient_support / 2 + ramanujan_norm_cost
    # The phase is e_l(-h*delta0*inverse(r*g_b*n)).  Thus the inverted
    # Bettin--Chandee variable lives at scale R*g_b*n, although its sparse
    # coefficient sequence still has only R entries.
    inverted_variable_scale = (
        r_length + scalar_b_gcd + ramanujan_factor
    )
    theorem_geometry = (
        inverted_variable_scale
        + oscillatory_modulus
        + product_length
    )
    longest_outer = max(inverted_variable_scale, oscillatory_modulus)
    first_parenthesis = (
        Fraction(7, 20) * theorem_geometry + longest_outer / 4
    )
    second_parenthesis = (
        Fraction(3, 8) * theorem_geometry
        + (product_length + longest_outer) / 8
    )
    phase_penalty = max(
        Fraction(0),
        (
            product_length
            - inverted_variable_scale
            - oscillatory_modulus
        )
        / 2,
    )
    fixed_factor_cost = scalar_a_gcd + delta_gcd_factor
    theorem_bound = (
        fixed_factor_cost
        + coefficient_norms
        + phase_penalty
        + max(first_parenthesis, second_parenthesis)
    )
    trivial_bound = fixed_factor_cost + coefficient_support
    sigma = (
        scalar_a_gcd
        + scalar_b_gcd
        + delta_gcd_factor
        + ramanujan_factor
        + oscillatory_modulus
    )
    local_target = r_length + sigma
    return KloostermanFractionTripleLedger(
        product_length=product_length,
        coefficient_norms=coefficient_norms,
        first_parenthesis=first_parenthesis,
        second_parenthesis=second_parenthesis,
        phase_penalty=phase_penalty,
        fixed_factor_cost=fixed_factor_cost,
        theorem_bound=theorem_bound,
        trivial_bound=trivial_bound,
        local_target=local_target,
        theorem_gap=theorem_bound - local_target,
        theorem_saving=trivial_bound - theorem_bound,
    )


def balanced_scalar_stratum_bettin_chandee_uniform_gap() -> Fraction:
    """Uniform lower bound for the direct BC gap on the balanced face.

    Put ``x=g_a+j``.  On ``rho=sigma=3`` and ``H=L=T^(5/2)``, the
    fixed-factor cost plus all three coefficient norms is exactly 11/2.
    The first Bettin--Chandee parenthesis is at least
    ``7/20*5+3/4=5/2`` because its geometric exponent is ``11-2*x>=5``
    and the inverted variable has exponent at least 3.  The local target
    is 6, so every such direct theorem insertion has gap at least 2.
    """

    coefficient_and_fixed = Fraction(11, 2)
    first_parenthesis_floor = Fraction(5, 2)
    local_target = Fraction(6)
    return (
        coefficient_and_fixed
        + first_parenthesis_floor
        - local_target
    )


def additive_completion_shifted(
    r: int, modulus: int, h_length: int, delta_length: int
) -> complex:
    """Evaluate (9.163) after the exact substitution ``d=r-s``.

    This is deliberately a second finite implementation rather than an
    alias for :func:`additive_product_completion`; the exhaustive tests
    check the shifted-Chowla coordinate change independently.
    """

    if min(r, modulus, h_length, delta_length) < 1:
        raise ValueError("all completion parameters must be positive")
    if gcd(r, modulus) != 1:
        raise ValueError("r must be invertible modulo the modulus")
    h_fourier = [
        _finite_interval_fourier(h_length, a, modulus)
        for a in range(modulus)
    ]
    delta_fourier = [
        _finite_interval_fourier(delta_length, b, modulus)
        for b in range(modulus)
    ]
    shift = r - modulus
    return sum(
        h_fourier[a]
        * delta_fourier[b]
        * cmath.exp(
            2j * cmath.pi * ((shift * a * b) % modulus) / modulus
        )
        for a in range(modulus)
        for b in range(modulus)
    ) / modulus


def weighted_inverse_product_box_sum(
    lower_r: int,
    lower_s: int,
    h_length: int,
    delta_length: int,
) -> complex:
    """Direct left side of (9.166) with ``W=1`` on finite dyadic boxes."""

    if min(lower_r, lower_s, h_length, delta_length) < 1:
        raise ValueError("all box parameters must be positive")
    return sum(
        mobius(r)
        * mobius(s)
        * rectangular_product_kernel(
            h_length,
            delta_length,
            Fraction(-pow(r, -1, s), s),
        )
        for s in range(lower_s + 1, 2 * lower_s + 1)
        for r in range(lower_r + 1, 2 * lower_r + 1)
        if gcd(r, s) == 1
    )


def weighted_shifted_completion_box_sum(
    lower_r: int,
    lower_s: int,
    h_length: int,
    delta_length: int,
) -> complex:
    """Right side of (9.166), retaining its moving ``d`` endpoints."""

    if min(lower_r, lower_s, h_length, delta_length) < 1:
        raise ValueError("all box parameters must be positive")
    total = 0j
    for s in range(lower_s + 1, 2 * lower_s + 1):
        for shift in range(lower_r - s + 1, 2 * lower_r - s + 1):
            if gcd(shift, s) != 1:
                continue
            r = s + shift
            total += (
                mobius(r)
                * mobius(s)
                * additive_completion_shifted(
                    r, s, h_length, delta_length
                )
            )
    return total


def additive_completion_axis_row(
    modulus: int, h_length: int, delta_length: int
) -> int:
    """Exact contribution of the complete row ``a=0`` in (9.163).

    Orthogonality gives
    ``sum_b 1_L_hat(b;s) = s*floor(L/s)``.  Hence the row, including
    the factor ``1/s``, equals ``H*floor(L/s)`` and vanishes when ``L<s``.
    """

    if min(modulus, h_length, delta_length) < 1:
        raise ValueError("all axis parameters must be positive")
    return h_length * (delta_length // modulus)


def additive_completion_axis_recombined(
    shift: int,
    modulus: int,
    h_length: int,
    delta_length: int,
) -> complex:
    """Sum the complete ``b`` axis into an exact residue incidence.

    Orthogonality in ``b`` turns (9.163) into

    ``sum_a 1_H_hat(a;s) * #{delta<=L: delta == d*a (mod s)}``.

    When ``L<s`` the count is an indicator.  This identity keeps the
    ``b=0`` point with the nonzero ``b`` frequencies that cancel it.
    """

    if min(modulus, h_length, delta_length) < 1:
        raise ValueError("all recombination parameters must be positive")
    if gcd(shift, modulus) != 1:
        raise ValueError("the shift must be invertible modulo the modulus")
    total = 0j
    for a in range(modulus):
        residue = (shift * a) % modulus
        if residue == 0:
            count = delta_length // modulus
        elif residue > delta_length:
            count = 0
        else:
            count = 1 + (delta_length - residue) // modulus
        total += _finite_interval_fourier(
            h_length, a, modulus
        ) * count
    return total


def additive_completion_axis_union(
    modulus: int, h_length: int, delta_length: int
) -> Fraction:
    """Exact contribution of ``a=0 or b=0`` in additive completion.

    The intersection ``(a,b)=(0,0)`` has contribution ``HL/s`` and is
    subtracted once.  In particular, when ``H,L<s`` the union is
    ``-HL/s`` even though each complete axis separately sums to zero.
    This records the cancellation that is lost by isolating the origin.
    """

    if min(modulus, h_length, delta_length) < 1:
        raise ValueError("all axis parameters must be positive")
    return (
        h_length * (delta_length // modulus)
        + delta_length * (h_length // modulus)
        - Fraction(h_length * delta_length, modulus)
    )


def additive_completion_zero_mode(
    modulus: int, h_length: int, delta_length: int
) -> Fraction:
    """The exact ``a=b=0`` contribution in additive product completion."""

    if min(modulus, h_length, delta_length) < 1:
        raise ValueError("all zero-mode parameters must be positive")
    return Fraction(h_length * delta_length, modulus)


def additive_completion_zero_mode_mobius_exponent(
    box: ExponentBox,
) -> Fraction:
    """Common power exponent forced by separately bounding the zero mode.

    If both dyadic Möbius sums were bounded by ``X^(beta+epsilon)``, the
    additive dual zero mode would have exponent
    ``a-sigma+beta*(rho+sigma)``.  Reaching the local ``R*S`` target
    requires

    ``beta <= (rho+2*sigma-a)/(rho+sigma)``.

    At the balanced maximal box this is exactly ``2/3``.  The ledger does
    not assert such a Möbius bound; it identifies why separating the zero
    mode reaches the same open power-saving barrier as earlier routes.
    """

    if not is_admissible(box):
        raise ValueError("zero-mode exponent requires an admissible box")
    return (
        box.rho + 2 * box.sigma - box.third_length
    ) / (box.rho + box.sigma)


def additive_shifted_chowla_ledger(
    box: ExponentBox,
) -> AdditiveShiftedChowlaLedger:
    """Return the exact lowest-dual-block exponent ledger.

    On the balanced face, put ``A=s/H`` and ``B=s/L``.  A smoothed
    completion localizes its lowest nonzero dual block at these scales;
    for the sharp finite completion this function is only the ledger for
    that block, not a claim that the complementary frequencies are small.
    The product frequency has exponent ``C=A*B`` and the phase
    ``e_s((r-s)ab)`` stops varying when ``|r-s| <= s/C``.
    """

    if not is_admissible(box):
        raise ValueError("shifted-Chowla ledger requires an admissible box")
    if box.rho != box.sigma:
        raise ValueError("this ledger is for the overlapping face R=S")
    if box.h > box.sigma or box.ell > box.sigma:
        raise ValueError("completion lengths must not exceed the modulus")
    h_frequency = box.sigma - box.h
    delta_frequency = box.sigma - box.ell
    product_frequency = h_frequency + delta_frequency
    completion_amplitude = box.third_length - box.sigma
    if completion_amplitude < 0:
        raise ValueError("the lowest-block amplitude must be nonnegative")
    near_shift = max(Fraction(0), box.sigma - product_frequency)
    near_trivial = (
        completion_amplitude
        + product_frequency
        + box.sigma
        + near_shift
    )
    local_target = box.rho + box.sigma
    one_modulus_l2 = None
    one_modulus_l2_gap = None
    if product_frequency < box.sigma:
        one_modulus_l2 = (
            box.sigma
            + box.h
            + box.ell
            + product_frequency / 2
        )
        one_modulus_l2_gap = max(
            Fraction(0), one_modulus_l2 - local_target
        )
    return AdditiveShiftedChowlaLedger(
        h_frequency=h_frequency,
        delta_frequency=delta_frequency,
        product_frequency=product_frequency,
        completion_amplitude=completion_amplitude,
        near_shift=near_shift,
        near_trivial=near_trivial,
        local_target=local_target,
        required_saving=max(Fraction(0), near_trivial - local_target),
        one_modulus_l2=one_modulus_l2,
        one_modulus_l2_gap=one_modulus_l2_gap,
    )


def additive_dual_block_ledger(
    box: ExponentBox,
    h_frequency: Fraction,
    delta_frequency: Fraction,
) -> AdditiveDualBlockLedger:
    """Ledger for centered frequencies ``|a|~T^alpha, |b|~T^beta``.

    The sharp Fourier bound (9.169) gives amplitudes
    ``min(h, sigma-alpha)`` and ``min(ell, sigma-beta)``.  On the
    circular near arc the shift length is
    ``T^max(0,sigma-alpha-beta)``.  The function records the resulting
    trivial exponent and does not estimate the complementary far arc.
    """

    if not is_admissible(box):
        raise ValueError("dual-block ledger requires an admissible box")
    if box.rho != box.sigma:
        raise ValueError("this ledger is for the overlapping face R=S")
    if not Fraction(0) <= h_frequency <= box.sigma:
        raise ValueError("the h frequency must lie in [1,s] on exponent scale")
    if not Fraction(0) <= delta_frequency <= box.sigma:
        raise ValueError(
            "the delta frequency must lie in [1,s] on exponent scale"
        )
    h_fourier_amplitude = min(box.h, box.sigma - h_frequency)
    delta_fourier_amplitude = min(
        box.ell, box.sigma - delta_frequency
    )
    product_frequency = h_frequency + delta_frequency
    completion_amplitude = (
        h_fourier_amplitude
        + delta_fourier_amplitude
        - box.sigma
    )
    near_shift = max(Fraction(0), box.sigma - product_frequency)
    near_trivial = (
        completion_amplitude
        + product_frequency
        + box.sigma
        + near_shift
    )
    local_target = box.rho + box.sigma
    one_modulus_l2 = None
    one_modulus_l2_gap = None
    if product_frequency < box.sigma:
        # Here AB=o(s), so congruent centered products have only O(1)
        # possible integer differences by multiples of s.  Divisor energy
        # then gives the displayed T^epsilon loss.  At AB>=s modular-
        # hyperbola multiplicities need a separate argument.
        one_modulus_l2 = (
            box.sigma
            + h_fourier_amplitude
            + delta_fourier_amplitude
            + product_frequency / 2
        )
        one_modulus_l2_gap = max(
            Fraction(0), one_modulus_l2 - local_target
        )
    return AdditiveDualBlockLedger(
        h_frequency=h_frequency,
        delta_frequency=delta_frequency,
        h_fourier_amplitude=h_fourier_amplitude,
        delta_fourier_amplitude=delta_fourier_amplitude,
        product_frequency=product_frequency,
        completion_amplitude=completion_amplitude,
        near_shift=near_shift,
        near_trivial=near_trivial,
        local_target=local_target,
        required_saving=max(Fraction(0), near_trivial - local_target),
        one_modulus_l2=one_modulus_l2,
        one_modulus_l2_gap=one_modulus_l2_gap,
    )


def reduced_inverse_fraction_denominator(
    u: int, s: int, v: int, t: int
) -> int:
    """Reduced denominator of ``u/s-v/t`` as an element of ``Q/Z``.

    When ``s,t`` are squarefree and both input fractions are reduced, put
    ``d=(s,t)`` and ``k=u*t-v*s``.  Then

    ``(k,s)=(k,t)=d`` and
    ``denominator = lcm(s,t)/(k/d,d)``.

    The function returns the equivalent formula ``s*t/(k,s*t)``; the
    squarefree refinement is audited separately by finite tests.
    """

    if min(s, t) < 2 or not (0 < u < s and 0 < v < t):
        raise ValueError("require proper positive fractions")
    if gcd(u, s) != 1 or gcd(v, t) != 1:
        raise ValueError("both fractions must be reduced")
    determinant = u * t - v * s
    return s * t // gcd(determinant, s * t)


def _centered_fraction_determinant(u: int, s: int, v: int, t: int) -> int:
    denominator = s * t
    numerator = (u * t - v * s) % denominator
    if 2 * numerator > denominator:
        numerator -= denominator
    return numerator


def farey_near_collision_count(lower: int, numerator_bound: int) -> int:
    """Count an exact finite circular Farey near-collision family.

    Denominators lie in ``(lower,2*lower]`` and both numerators are units.
    Ordered pairs are counted when their centered determinant has absolute
    value at most ``numerator_bound``.
    """

    if lower < 1 or numerator_bound < 0:
        raise ValueError("lower must be positive and the bound nonnegative")
    fractions = [
        (u, s)
        for s in range(lower + 1, 2 * lower + 1)
        for u in range(1, s)
        if gcd(u, s) == 1
    ]
    return sum(
        abs(_centered_fraction_determinant(u, s, v, t))
        <= numerator_bound
        for u, s in fractions
        for v, t in fractions
    )


def farey_near_collision_divisor_bound(
    lower: int, numerator_bound: int
) -> int:
    """Elementary divisor majorant for ``farey_near_collision_count``.

    For a nonzero centered determinant ``k``, fixing ``s,t`` leaves at
    most ``3*(s,t)`` solutions: the unreduced determinant can be
    ``k-st``, ``k``, or ``k+st``.  Grouping by ``d=(s,t)|k`` and dropping
    coprimality gives at most ``12*lower^2*tau(|k|)`` for each sign.
    The deliberately rounded finite bound below is therefore

    ``2*S^2 + 24*S^2*sum_{1<=k<=K} tau(k)``.

    It is coarse in constants but has the natural exponent ``S^2*K``.
    """

    if lower < 1 or numerator_bound < 0:
        raise ValueError("lower must be positive and the bound nonnegative")
    divisor_mass = sum(
        len(divisors(k)) for k in range(1, numerator_bound + 1)
    )
    return 2 * lower * lower + 24 * lower * lower * divisor_mass


def farey_central_collision_ledger(
    box: ExponentBox,
) -> FareyCentralCollisionLedger:
    """Exponent bound from the elementary circular Farey parameterization.

    A reduced fraction ``u/s`` has at most ``T^max(0,rho-sigma)`` lifts
    ``r`` in a dyadic interval of length ``R`` satisfying ``r*u=1 mod s``.
    Combining this with the finite ``S^2*K`` determinant bound removes
    the extra balanced power in the cruder ``r,s,k,ell`` divisor switch.
    This is an unsigned collision count; it supplies no Möbius saving.
    """

    if not is_admissible(box):
        raise ValueError("Farey collision ledger requires an admissible box")
    numerator = max(Fraction(0), 2 * box.sigma - box.third_length)
    lift_multiplicity = max(Fraction(0), box.rho - box.sigma)
    elementary_count = (
        2 * box.sigma + numerator + 2 * lift_multiplicity
    )
    random_collision_count = max(
        box.rho + box.sigma,
        2 * (box.rho + box.sigma) - box.third_length,
    )
    return FareyCentralCollisionLedger(
        numerator=numerator,
        lift_multiplicity=lift_multiplicity,
        elementary_count=elementary_count,
        random_collision_count=random_collision_count,
        counting_gap=elementary_count - random_collision_count,
    )


def inverse_lift_mobius_weight(u: int, s: int, *, lower_r: int) -> int:
    """Möbius weight of all inverse lifts in the stated dyadic interval.

    This is the exact coefficient obtained after replacing r by its
    inverse modulo s:

    M_R(u;s) = sum mu(r) * 1_{r*u = 1 (mod s)}.

    In the balanced interval lower_r=lower_s and s>lower_r, its absolute
    value is at most one because the interval is shorter than the modulus.
    """

    if lower_r < 1 or s < 2 or not 0 < u < s:
        raise ValueError("require a positive dyadic endpoint and 0 < u < s")
    if gcd(u, s) != 1:
        raise ValueError("u must be a unit modulo s")
    return sum(
        mobius(r)
        for r in range(lower_r + 1, 2 * lower_r + 1)
        if (r * u - 1) % s == 0
    )


def weighted_inverse_collision_sum(
    lower_r: int, lower_s: int, numerator_bound: int
) -> int:
    """Original four-Möbius finite collision sum in inverse coordinates."""

    if min(lower_r, lower_s) < 1 or numerator_bound < 0:
        raise ValueError("dyadic endpoints must be positive and bound nonnegative")
    points = [
        (r, s, mobius(r) * mobius(s))
        for s in range(lower_s + 1, 2 * lower_s + 1)
        for r in range(lower_r + 1, 2 * lower_r + 1)
        if gcd(r, s) == 1
    ]
    total = 0
    for r, s, weight in points:
        for r_prime, t, weight_prime in points:
            certificate = cross_inverse_fraction_collision(
                r, s, r_prime, t
            )
            if abs(certificate.numerator) <= numerator_bound:
                total += weight * weight_prime
    return total


def weighted_farey_collision_sum(
    lower_r: int, lower_s: int, numerator_bound: int
) -> int:
    """The same four-Möbius sum in exact signed Farey coordinates.

    Both outer modulus weights and both inverse-lift Möbius weights remain
    inside the collision sum.  Equality with the inverse-coordinate
    version is a finite change of variables, not a cancellation estimate.
    """

    if min(lower_r, lower_s) < 1 or numerator_bound < 0:
        raise ValueError("dyadic endpoints must be positive and bound nonnegative")
    points = [
        (
            u,
            s,
            mobius(s)
            * inverse_lift_mobius_weight(u, s, lower_r=lower_r),
        )
        for s in range(lower_s + 1, 2 * lower_s + 1)
        for u in range(1, s)
        if gcd(u, s) == 1
    ]
    return sum(
        weight * weight_prime
        for u, s, weight in points
        for v, t, weight_prime in points
        if abs(_centered_fraction_determinant(u, s, v, t))
        <= numerator_bound
    )


def balanced_inverse_fraction_spacing_margin(
    r: int, s: int, t: int, *, lower: int
) -> Fraction:
    """Margin over the elementary ``1/(16*lower)`` spacing bound.

    Assume ``lower < r,s,t <= 2*lower``, ``s != t``, and ``r`` is a unit
    modulo ``s*t``.  If the congruence quotient were zero, then
    ``r*k=t-s``; the dyadic inequalities force ``k=0`` and hence ``s=t``.
    Therefore the quotient is nonzero.  It follows that

    ``|r*k| >= s*t-|t-s| > lower^2-lower``

    and hence the distance modulo one is at least ``1/(16*lower)`` for
    ``lower >= 2``.  The returned nonnegative margin is directly checkable
    with exact rational arithmetic.
    """

    if lower < 2:
        raise ValueError("the dyadic lower endpoint must be at least 2")
    if not all(lower < value <= 2 * lower for value in (r, s, t)):
        raise ValueError("r,s,t must lie in the same dyadic interval")
    if s == t:
        raise ValueError("the spacing statement requires distinct moduli")
    certificate = inverse_fraction_separation(r, s, t)
    if certificate.congruence_quotient == 0:
        raise AssertionError("distinct balanced moduli cannot be resonant")
    margin = certificate.distance - Fraction(1, 16 * lower)
    if margin < 0:
        raise AssertionError("the certified inverse-fraction spacing failed")
    return margin


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
class BlomerPascadiMargins:
    """Margins of the three published terms over the best trivial bound.

    The interval length is ``N=c^nu``.  Positive entries mean that the
    corresponding term in Blomer--Pascadi, Theorem 1.1, saves a power of
    the modulus over ``min(c, N*sqrt(c))`` (with coefficient norms omitted
    on both sides).
    """

    first: Fraction
    second: Fraction
    third: Fraction

    def values(self) -> tuple[Fraction, ...]:
        return (self.first, self.second, self.third)


@dataclass(frozen=True)
class SmoothAdditiveDualSupportLedger:
    """Dual-support ledger for the actual modulated smooth kernel.

    The two centres come from ``s*x`` and ``s*T/(M*R)``; the two widths
    come from smooth completion at ``s/H`` and ``s/L``.  The effective
    frequencies are the larger centre/width scales.  The ledger records
    only exact exponent arithmetic and published-theorem applicability;
    it does not assert the remaining double-Mobius cancellation.
    """

    h_center: Fraction
    h_width: Fraction
    h_frequency: Fraction
    delta_center: Fraction
    delta_width: Fraction
    delta_frequency: Fraction
    product_frequency: Fraction
    completion_amplitude: Fraction
    near_shift: Fraction
    near_trivial: Fraction
    local_target: Fraction
    required_saving: Fraction
    fixed_modulus_nu: Fraction | None
    blomer_pascadi_margins: BlomerPascadiMargins | None
    blomer_pascadi_covered: bool


@dataclass(frozen=True)
class BlomerPascadiUnbalancedLedger:
    """Exponent ledger for Blomer--Pascadi Theorem 5.5."""

    first_term: Fraction
    second_term: Fraction
    third_term: Fraction
    fourth_term: Fraction
    fifth_term: Fraction
    saving_factor: Fraction
    best_trivial_factor: Fraction
    theorem_factor: Fraction
    theorem_gap: Fraction


def blomer_pascadi_unbalanced_ledger(
    left_length: Fraction,
    right_length: Fraction,
) -> BlomerPascadiUnbalancedLedger:
    """Audit Theorem 5.5 for interval lengths ``c^left`` and ``c^right``."""

    if not (
        0 <= left_length <= 1
        and 0 <= right_length <= 1
    ):
        raise ValueError("Theorem 5.5 requires both lengths between 1 and c")
    first_term = (
        left_length / 8
        + (
            max(Fraction(1), left_length + right_length)
            + max(Fraction(1), 2 * right_length)
        )
        / 16
        - Fraction(1, 4)
        + min(1 - left_length, Fraction(1, 2)) / 16
    )
    second_term = max(
        2 * right_length - 2,
        right_length / 2
        + left_length
        + max(Fraction(1), 2 * right_length)
        - Fraction(5, 2),
    ) / 16
    third_term = max(left_length, right_length) / 3 - Fraction(1, 5)
    fourth_term = max(
        left_length / 2 + right_length / 6,
        left_length / 6 + right_length / 2,
    ) - Fraction(7, 18)
    fifth_term = max(left_length, right_length) / 15 - Fraction(1, 15)
    saving_factor = max(
        first_term,
        second_term,
        third_term,
        fourth_term,
        fifth_term,
    )
    best_trivial_factor = min(
        Fraction(1),
        (1 + left_length + right_length) / 2,
    )
    theorem_factor = 1 + saving_factor
    return BlomerPascadiUnbalancedLedger(
        first_term=first_term,
        second_term=second_term,
        third_term=third_term,
        fourth_term=fourth_term,
        fifth_term=fifth_term,
        saving_factor=saving_factor,
        best_trivial_factor=best_trivial_factor,
        theorem_factor=theorem_factor,
        theorem_gap=theorem_factor - best_trivial_factor,
    )


def blomer_pascadi_best_trivial_margins(
    nu: Fraction,
) -> BlomerPascadiMargins:
    """Return exact margins in Blomer--Pascadi, Theorem 1.1.

    After writing ``N=c^nu``, the three terms in the theorem have modulus
    exponents

    ``29/32+nu/8``, ``13/16+5nu/16``, and ``11/18+2nu/3``.

    The elementary comparison is ``min(c, N*sqrt(c))``.  This ledger is
    an applicability check only; it does not identify the theorem's
    coefficients with the Möbius coupled kernel.
    """

    if nu < 0:
        raise ValueError("the interval-length exponent must be nonnegative")
    best_trivial = min(Fraction(1), nu + Fraction(1, 2))
    return BlomerPascadiMargins(
        first=best_trivial - (Fraction(29, 32) + nu / 8),
        second=best_trivial - (Fraction(13, 16) + 5 * nu / 16),
        third=best_trivial - (Fraction(11, 18) + 2 * nu / 3),
    )


def blomer_pascadi_beats_best_trivial(nu: Fraction) -> bool:
    """Whether every term has a strict power saving at length ``c^nu``."""

    return min(blomer_pascadi_best_trivial_margins(nu).values()) > 0


def smooth_additive_dual_support_ledger(
    box: ExponentBox,
) -> SmoothAdditiveDualSupportLedger:
    """Return the smooth two-dimensional completion support ledger.

    In the separated kernel (6.2), the ``h`` transform is centred at
    ``|s*x|`` with ``x~M/S`` and has width ``s/H``.  Its two exponents
    are therefore ``m`` and ``sigma-h``.  The ``delta`` transform is
    centred at ``s*T/(M*R)`` and has width ``s/L``.  Smooth summation by
    parts makes the complement of these centred windows smaller than
    every fixed power; this function records the surviving window.

    When the two effective lengths agree, their common exponent relative
    to the modulus is also checked against Blomer--Pascadi, Theorem 1.1.
    A positive theorem margin would only establish scale compatibility,
    not coefficient compatibility.
    """

    if not is_admissible(box):
        raise ValueError("smooth additive-dual support needs an admissible box")
    if box.rho != box.sigma:
        raise ValueError("this ledger is for the overlapping face R=S")

    zero = Fraction(0)
    h_center = max(zero, box.m)
    h_width = max(zero, box.sigma - box.h)
    h_frequency = max(h_center, h_width)
    delta_center = max(
        zero, box.sigma + 1 - box.m - box.rho
    )
    delta_width = max(zero, box.sigma - box.ell)
    delta_frequency = max(delta_center, delta_width)
    if max(h_frequency, delta_frequency) > box.sigma:
        raise ValueError("the centred dual window wraps around the modulus")

    product_frequency = h_frequency + delta_frequency
    completion_amplitude = box.third_length - box.sigma
    if completion_amplitude < 0:
        raise ValueError("the smooth transition amplitude must be nonnegative")
    near_shift = max(zero, box.sigma - product_frequency)
    near_trivial = (
        completion_amplitude
        + product_frequency
        + box.sigma
        + near_shift
    )
    local_target = box.rho + box.sigma

    fixed_modulus_nu = None
    margins = None
    covered = False
    if h_frequency == delta_frequency and box.sigma > 0:
        fixed_modulus_nu = h_frequency / box.sigma
        margins = blomer_pascadi_best_trivial_margins(
            fixed_modulus_nu
        )
        covered = min(margins.values()) > 0

    return SmoothAdditiveDualSupportLedger(
        h_center=h_center,
        h_width=h_width,
        h_frequency=h_frequency,
        delta_center=delta_center,
        delta_width=delta_width,
        delta_frequency=delta_frequency,
        product_frequency=product_frequency,
        completion_amplitude=completion_amplitude,
        near_shift=near_shift,
        near_trivial=near_trivial,
        local_target=local_target,
        required_saving=max(zero, near_trivial - local_target),
        fixed_modulus_nu=fixed_modulus_nu,
        blomer_pascadi_margins=margins,
        blomer_pascadi_covered=covered,
    )


@dataclass(frozen=True)
class PascadiModuliMargins:
    """Power savings in Pascadi, Corollary 7.9, for equal intervals.

    The two entries correspond to the two alternatives inside the minimum.
    Positive is a saving in the parenthetical factor; negative is a loss.
    """

    first: Fraction
    second: Fraction

    @property
    def best(self) -> Fraction:
        return max(self.first, self.second)


def pascadi_averaged_moduli_margins(
    *, length: Fraction, fixed_modulus: Fraction, amplifier: Fraction
) -> PascadiModuliMargins:
    """Exact equal-length exponent ledger for Pascadi, Corollary 7.9.

    Write ``M=N=C^length``, ``q=C^fixed_modulus`` and
    ``d=C^amplifier``.  For square-free ``q=de`` one has ``d'=1`` and
    the largest square divisor parameter in the corollary is ``f=d``.
    The returned values are minus one sixth of the largest exponent in
    each of the two alternatives.  This checks only the theorem's
    parenthetical gain; coefficient norms and the Fourier factor remain
    outside this diagnostic.
    """

    if not (0 <= length <= 1):
        raise ValueError("the interval exponent must lie in [0, 1]")
    if not (0 <= amplifier <= fixed_modulus <= 1):
        raise ValueError("require 0 <= amplifier <= fixed_modulus <= 1")
    first_terms = (
        amplifier + 4 * length - 3,
        amplifier + 2 * length - 2,
        -amplifier,
    )
    second_terms = (
        amplifier + 4 * length - fixed_modulus - 2,
        amplifier + 2 * length - fixed_modulus - 1,
        fixed_modulus - amplifier - 1,
    )
    return PascadiModuliMargins(
        first=-max(first_terms) / 6,
        second=-max(second_terms) / 6,
    )


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


def coherent_operator_required_exponent(box: ExponentBox) -> Fraction:
    """Operator exponent required after collapsing ``h,delta`` to products.

    Write the coherent cross-modulus kernel as a matrix from the product
    coefficient ``nu_a`` to the ``r`` sequence.  The input norms have
    exponents ``a/2`` and ``rho/2``.  To reach the local ``R*S`` target,
    its operator norm must therefore have exponent
    ``rho+sigma-(rho+a)/2``.

    This is only a sufficient arbitrary-coefficient interface: replacing
    the factorized ``h,delta`` family by an arbitrary ``nu_a`` discards
    structure that a successful proof may need.
    """

    if not is_admissible(box):
        raise ValueError("operator exponent is defined only on admissible boxes")
    return box.rho + box.sigma - (
        box.rho + box.third_length
    ) / 2


def coherent_operator_large_sieve_exponent(box: ExponentBox) -> Fraction:
    """Exponent supplied by the two-orientation Farey large sieve.

    Factoring the matrix through the ``(r,s)`` Farey rows gives the
    existing ``R*S*sqrt(A)`` bilinear bound.  Removing the input norms
    ``sqrt(R*A)`` leaves operator exponent ``rho/2+sigma``.
    """

    if not is_admissible(box):
        raise ValueError("operator exponent is defined only on admissible boxes")
    return box.rho / 2 + box.sigma


def coherent_operator_large_sieve_gap(box: ExponentBox) -> Fraction:
    """Power still missing in the arbitrary product-coefficient operator."""

    return coherent_operator_large_sieve_exponent(
        box
    ) - coherent_operator_required_exponent(box)


def dispersion_pointwise_mean_square_gap(box: ExponentBox) -> Fraction:
    """Gap between pointwise joint completion and dispersion target (9.40)."""

    if not is_admissible(box):
        raise ValueError("dispersion gap is defined only on admissible boxes")
    return 2 * min(box.ell, box.h)


def dispersion_random_benchmark_gap(box: ExponentBox) -> Fraction:
    """Extra power needed beyond the random-term benchmark in (9.42)."""

    if not is_admissible(box):
        raise ValueError("dispersion gap is defined only on admissible boxes")
    shorter = min(box.ell, box.h)
    longer = max(box.ell, box.h)
    return max(Fraction(0), 2 * shorter + longer - box.rho - box.sigma)


def direct_fourfold_random_margin(box: ExponentBox) -> Fraction:
    """Margin between the local target and the full random-term scale.

    The uncut ``r,s,h,delta`` sum has ``R*S*L*H`` terms, so its formal
    square-root scale has exponent ``(rho+sigma+a)/2``.  The local target
    has exponent ``rho+sigma``.  On the retained polytope ``a <=
    rho+sigma-1``, hence this diagnostic margin is always at least 1/2.
    It is only a scale comparison, not a cancellation theorem.
    """

    if not is_admissible(box):
        raise ValueError("random margin is defined only on admissible boxes")
    return (box.rho + box.sigma - box.third_length) / 2


def character_large_sieve_unit_gap(box: ExponentBox) -> Fraction:
    """Best exponent gap from the direct unit-stratum character sieve.

    With denominator length ``S``, character orthogonality, one second
    moment, and two fourth moments give

    ``S^(1/2) * ((S^2+R)R)^(1/2) * A^(1/2)``.

    Reciprocity supplies the same estimate with ``R,S`` interchanged.
    This function returns the smaller loss over the local ``RS`` target.
    A nonpositive value would mean that this diagnostic covers the box.
    """

    if not is_admissible(box):
        raise ValueError("character-sieve gap is defined only on admissible boxes")
    denominator_s = (
        box.third_length
        + max(2 * box.sigma, box.rho)
        - box.rho
        - box.sigma
    ) / 2
    denominator_r = (
        box.third_length
        + max(2 * box.rho, box.sigma)
        - box.rho
        - box.sigma
    ) / 2
    return min(denominator_s, denominator_r)


def balanced_dual_low_mode_mobius_exponent(box: ExponentBox) -> Fraction:
    """Per-variable Möbius exponent sufficient for the dual lowest mode.

    This diagnostic applies only when ``R=S``.  Dualizing both long
    character sums contributes ``A/S``.  If each of the remaining smooth
    Möbius sums of length ``R=S`` is bounded by ``R^beta``, the local
    ``RS`` target asks ``A/S * R^(2 beta) <= R*S``.
    """

    if not is_admissible(box):
        raise ValueError("dual-mode exponent is defined only on admissible boxes")
    if box.rho != box.sigma or box.rho == 0:
        raise ValueError("dual-mode exponent diagnostic requires R=S>1")
    return (3 * box.rho - box.third_length) / (2 * box.rho)


def balanced_principal_character_mobius_exponent(box: ExponentBox) -> Fraction:
    """Möbius exponent forced by estimating the principal character alone.

    On ``R=S``, the unit-stratum principal-character contribution has
    diagnostic scale ``A * M(R)``.  Requiring it to be at most ``R*S``
    asks ``M(R) <= R^beta`` with ``beta=(2*rho-a)/rho``.
    """

    if not is_admissible(box):
        raise ValueError("principal exponent is defined only on admissible boxes")
    if box.rho != box.sigma or box.rho == 0:
        raise ValueError("principal exponent diagnostic requires R=S>1")
    return (2 * box.rho - box.third_length) / box.rho


def induced_gauss_outer_mobius_sign(conductor: int, cofactor: int) -> int:
    """Arithmetic sign in ``mu(c) tau_c(chi)`` after induction.

    For squarefree coprime ``c=f*k`` and a character induced from conductor
    ``f``, the Gauss sum contributes ``mu(k)``.  Hence the outer Möbius
    sign becomes ``mu(f*k)mu(k)=mu(f)``: no Möbius sign remains on ``k``.
    """

    if conductor < 1 or cofactor < 1:
        raise ValueError("conductor and cofactor must be positive")
    if gcd(conductor, cofactor) != 1:
        raise ValueError("conductor and cofactor must be coprime")
    if mobius(conductor * cofactor) == 0:
        raise ValueError("the product must be squarefree")
    return mobius(conductor * cofactor) * mobius(cofactor)


def coprime_indicator_via_mobius(value: int, modulus: int) -> int:
    """Exact divisor expansion of ``1_(value,modulus)=1``."""

    if modulus < 1:
        raise ValueError("modulus must be positive")
    return sum(mobius(d) for d in divisors(gcd(abs(value), modulus)))


def global_unit_principal_completion_margin(box: ExponentBox) -> Fraction:
    """Margin in ``LM <= S`` for the globally completed unit principal mode.

    Summing the actual Fourier coefficients over all coprime nonzero
    ``h`` before dyadic absolute values replaces the local ``H`` count by
    a divisor-bounded reverse-Poisson sum.  A conservative normalized
    bound is ``R*L*M``; this function records the exponent margin between
    that scale and ``R*S``.
    """

    if not is_admissible(box):
        raise ValueError("principal completion margin requires an admissible box")
    return box.sigma - box.ell - box.m


def ramanujan_sum(n: int, frequency: int) -> int:
    """Exact integer Ramanujan sum ``c_n(frequency)``."""

    if n < 1:
        raise ValueError("modulus must be positive")
    return sum(
        d * mobius(n // d) for d in divisors(gcd(n, abs(frequency)))
    )


def squarefree_normalized_ramanujan_mean_formula(
    modulus: int, frequency: int
) -> Fraction:
    """Exact ``c_q(k)/phi(q)`` from the cofactor coprime to ``k``."""

    if modulus < 1 or mobius(modulus) == 0:
        raise ValueError("the modulus must be positive and squarefree")
    coprime_cofactor = modulus // gcd(modulus, abs(frequency))
    return Fraction(
        mobius(coprime_cofactor),
        _euler_phi(coprime_cofactor),
    )


def ramanujan_mean_dyadic_sum(scale: int, frequency: int) -> Fraction:
    """Absolute normalized Ramanujan means on one squarefree dyadic box."""

    if scale < 1 or frequency == 0:
        raise ValueError("the scale must be positive and frequency nonzero")
    return sum(
        (
            abs(
                squarefree_normalized_ramanujan_mean_formula(
                    modulus,
                    frequency,
                )
            )
            for modulus in range(scale + 1, 2 * scale + 1)
            if mobius(modulus) != 0
        ),
        start=Fraction(0),
    )


def ramanujan_mean_dyadic_divisor_majorant(
    scale: int, frequency: int
) -> Fraction:
    """Finite divisor/Euler-sum majorant for the dyadic mean family."""

    if scale < 1 or frequency == 0:
        raise ValueError("the scale must be positive and frequency nonzero")
    squarefree_euler_sum = sum(
        (
            Fraction(1, _euler_phi(cofactor))
            for cofactor in range(1, 2 * scale + 1)
            if mobius(cofactor) != 0
        ),
        start=Fraction(0),
    )
    return len(divisors(abs(frequency))) * squarefree_euler_sum


def squarefree_outer_mobius_ramanujan(n: int, frequency: int) -> int:
    """Value of ``mu(n)c_n(frequency)`` on squarefree ``n``."""

    if mobius(n) == 0:
        raise ValueError("modulus must be squarefree")
    return mobius(n) * ramanujan_sum(n, frequency)


def nonunit_principal_long_factor_floor(box: ExponentBox) -> Fraction:
    """Exponent floor for the long factor after global h completion.

    Reverse Poisson forces the complementary modulus ``v`` to satisfy
    ``v <= M``.  In ``s=u*v`` this leaves ``u >= S/M``.
    """

    if not is_admissible(box):
        raise ValueError("factor floor requires an admissible box")
    return box.sigma - box.m


def nonunit_principal_h_boundary_slack(box: ExponentBox) -> Fraction:
    """Distance from the only non-negligible principal Type-II h-face."""

    if not is_admissible(box):
        raise ValueError("boundary slack requires an admissible box")
    return box.sigma - box.m - box.h


def nonunit_principal_trivial_loss(box: ExponentBox) -> Fraction:
    """Loss ``L/M`` after ``wc`` and ``u`` localize to ``M`` and ``H``."""

    if not is_admissible(box):
        raise ValueError("principal loss requires an admissible box")
    return max(Fraction(0), box.ell - box.m)


def nonunit_principal_equal_mobius_exponent(box: ExponentBox) -> Fraction:
    """Equal Mertens exponent sufficient for the separated r,u route.

    On the top h-face the two Möbius lengths are ``R`` and ``S/M`` and
    the remaining loss is ``max(0,L/M)``.  If both sums obey ``X^beta``,
    this returns the largest beta that would close the local target.
    """

    if not is_admissible(box):
        raise ValueError("Möbius exponent requires an admissible box")
    total_mobius_length = box.rho + box.sigma - box.m
    if total_mobius_length == 0:
        return Fraction(1)
    return Fraction(1) - nonunit_principal_trivial_loss(box) / total_mobius_length


def nonunit_principal_is_residual_face(box: ExponentBox) -> bool:
    """Whether the zero-slack box survives global principal completion."""

    if not is_admissible(box):
        raise ValueError("residual classification requires an admissible box")
    return nonunit_principal_h_boundary_slack(box) == 0 and box.ell > box.m


def reverse_unit_solution_count_gap(box: ExponentBox) -> Fraction:
    """Gap left by counting the reverse-Poisson affine solutions.

    The elementary count is ``MKL + MRL``.  After restoring the exact
    kernel normalization, the centered target asks for a weighted count
    of exponent ``(rho+sigma+m+k)/2``.
    """

    if not is_admissible(box):
        raise ValueError("solution-count gap requires an admissible box")
    count_exponent = max(
        box.m + box.k + box.ell,
        box.m + box.rho + box.ell,
    )
    normalized_target = (
        box.rho + box.sigma + box.m + box.k
    ) / 2
    return max(Fraction(0), count_exponent - normalized_target)


def reverse_unit_affine_progression_length(box: ExponentBox) -> Fraction:
    """Generic exponent of the r,s solution-parameter interval."""

    if not is_admissible(box):
        raise ValueError("progression length requires an admissible box")
    return max(Fraction(0), box.rho - box.k)


@dataclass(frozen=True)
class CenteredDualScales:
    """Exponent ledger after divisor duality and delta completion."""

    cofactor: Fraction
    frequency: Fraction
    residue: Fraction
    quotient: Fraction
    progression: Fraction
    slope_penalty: Fraction


@dataclass(frozen=True)
class GeneralizedCenteredDualScales:
    """Exponent ledger for a nonunit gcd stratum and one ``k|e`` term."""

    raw_frequency: Fraction
    product_frequency: Fraction
    residue: Fraction
    quotient: Fraction
    progression: Fraction


@dataclass(frozen=True)
class NonprincipalSignMigration:
    """Exact reparametrization of one ``k|e`` reverse-Poisson term."""

    d: int
    dilation: int
    residual_modulus: int
    shifted_delta: int
    gcd_part: int
    centered_modulus: int
    s: int
    delta: int
    mobius_sign: int


def migrate_nonprincipal_mobius_sign(
    d: int,
    e: int,
    c: int,
    delta_reduced: int,
    k: int,
) -> NonprincipalSignMigration:
    """Move ``mu(e)mu(k)`` to the dilation ``E=e/k`` exactly.

    The input models one term of (9.113): ``d,e,c`` are pairwise
    coprime and squarefree, ``k|e``, and ``(delta_reduced,c)=1``.
    With ``E=e/k``, ``delta'=k*delta_reduced`` and ``f=k*c``, one has
    ``k=(delta',f)``, ``s=d*E*f``, ``delta=E*delta'`` and
    ``mu(e)mu(k)=mu(E)``.
    """

    if min(d, e, c, k) < 1 or delta_reduced == 0:
        raise ValueError("positive factors and nonzero reduced delta are required")
    if mobius(d * e * c) == 0:
        raise ValueError("d*e*c must be squarefree")
    if gcd(d, e) != 1 or gcd(d, c) != 1 or gcd(e, c) != 1:
        raise ValueError("d,e,c must be pairwise coprime")
    if e % k != 0 or gcd(delta_reduced, c) != 1:
        raise ValueError("require k|e and gcd(delta_reduced,c)=1")
    dilation = e // k
    shifted_delta = k * delta_reduced
    residual_modulus = k * c
    if gcd(shifted_delta, residual_modulus) != k:
        raise AssertionError("the inverse gcd map failed")
    return NonprincipalSignMigration(
        d=d,
        dilation=dilation,
        residual_modulus=residual_modulus,
        shifted_delta=shifted_delta,
        gcd_part=k,
        centered_modulus=c,
        s=d * dilation * residual_modulus,
        delta=dilation * shifted_delta,
        mobius_sign=mobius(e) * mobius(k),
    )


def centered_dual_scales(
    box: ExponentBox,
    modulus: Fraction,
) -> CenteredDualScales:
    """Return the exact scales ``C,V,B,Z,L`` for a divisor modulus ``J``.

    The centered divisor-dual support has ``max(M,L) <= J <= S``.
    Delta completion gives ``B=J/L`` and ``Z=R/L``; the affine family
    ``b*r-v=z*j`` has progression length ``L``.  Applying the averaged
    Chowla theorem termwise costs the square of the larger slope.
    """

    if not is_admissible(box):
        raise ValueError("centered dual scales require an admissible box")
    if not max(box.m, box.ell) <= modulus <= box.sigma:
        raise ValueError("divisor modulus must satisfy max(M,L) <= J <= S")
    residue = modulus - box.ell
    quotient = box.rho - box.ell
    if quotient < 0:
        raise ValueError("delta completion requires L <= R")
    return CenteredDualScales(
        cofactor=box.sigma - modulus,
        frequency=modulus - box.m,
        residue=residue,
        quotient=quotient,
        progression=box.ell,
        slope_penalty=2 * max(residue, quotient),
    )


def wright_unbalanced_modulus_margin(
    box: ExponentBox,
    modulus: Fraction,
    allowable_modulus_power: Fraction,
) -> Fraction:
    """Margin in ``J <= (B*R)^gamma`` for Wright's convolution route."""

    centered_dual_scales(box, modulus)
    if allowable_modulus_power <= 0:
        raise ValueError("allowable modulus power must be positive")
    convolution_length = box.rho + modulus - box.ell
    return allowable_modulus_power * convolution_length - modulus


def centered_dual_common_mobius_exponent(
    box: ExponentBox,
    modulus: Fraction,
) -> Fraction:
    """Common smooth-Mertens exponent sufficient on the central arc.

    The difference window has length ``V=J/M``.  If the two long
    Möbius sums of lengths ``R`` and ``J`` are each ``X^beta``, the
    central Fourier arc asks ``V <= (R*J)^(1-beta)``.
    """

    scales = centered_dual_scales(box, modulus)
    total_long_length = box.rho + modulus
    if total_long_length <= 0:
        raise ValueError("central arc requires a positive long length")
    return Fraction(1) - scales.frequency / total_long_length


def centered_dual_parseval_loss(
    box: ExponentBox,
    modulus: Fraction,
) -> Fraction:
    """Power loss of the general-coefficient centered Fourier bound.

    Equation (9.109) has scale ``V*X_0`` against target ``X_0``, where
    ``V=J/M``.  Hence the exact exponent loss is ``j-m``.  It vanishes
    precisely on the zero-slack face ``j=m``; the support condition
    ``j >= max(m, ell)`` then forces ``ell <= m``.
    """

    return centered_dual_scales(box, modulus).frequency


def centered_dual_parseval_covers(
    box: ExponentBox,
    modulus: Fraction,
) -> bool:
    """Whether Parseval alone closes a zero-slack centered dual box."""

    return centered_dual_parseval_loss(box, modulus) == 0


def generalized_centered_dual_scales(
    box: ExponentBox,
    modulus: Fraction,
    delta_gcd: Fraction,
    mobius_divisor: Fraction,
) -> GeneralizedCenteredDualScales:
    """Scales after dualizing a general ``(d,e,c)`` nonprincipal stratum.

    Write ``e=T^delta_gcd``, ``k=T^mobius_divisor`` and ``E=e/k``.
    The raw dual frequency has length ``J*E/M``.  Delta completion uses
    ``delta_1`` of length ``L/e`` and the product frequency ``k*v``;
    the equation is ``b*r-k*v=z*j``.
    """

    if not is_admissible(box):
        raise ValueError("generalized centered scales require an admissible box")
    if not Fraction(0) <= mobius_divisor <= delta_gcd <= box.ell:
        raise ValueError("require 1 <= k <= e <= L on the exponent scale")
    raw_frequency = modulus + delta_gcd - mobius_divisor - box.m
    if raw_frequency < 0:
        raise ValueError("the divisor modulus lies below Fourier support")
    return GeneralizedCenteredDualScales(
        raw_frequency=raw_frequency,
        product_frequency=modulus + delta_gcd - box.m,
        residue=modulus + delta_gcd - box.ell,
        quotient=box.rho + delta_gcd - box.ell,
        progression=box.ell - delta_gcd,
    )


@dataclass(frozen=True)
class ReducedInversePhase:
    """Exact gcd reduction of ``e_s(-h*delta*r^{-1})``.

    In the application ``s`` is squarefree because it carries ``mu(s)``.
    Then ``d``, ``e``, and ``modulus`` are pairwise coprime.  The phase
    reduction itself remains valid without squarefreeness.
    """

    d: int
    e: int
    modulus: int
    h_reduced: int
    delta_reduced: int


def reduce_inverse_product_phase(
    r: int, s: int, h: int, delta: int
) -> ReducedInversePhase:
    """Return the exact reduced-modulus data for the inverse phase.

    With ``d=(h,s)``, ``e=(delta,s/d)``, and ``c=s/(d*e)``, one has

    ``e_s(-h*delta*inv_s(r)) = e_c(-(h/d)*(delta/e)*inv_c(r))``.
    """

    if min(r, s, h, delta) < 1:
        raise ValueError("phase variables must be positive")
    if gcd(r, s) != 1:
        raise ValueError("r must be invertible modulo s")
    d = gcd(h, s)
    e = gcd(delta, s // d)
    modulus = s // (d * e)
    return ReducedInversePhase(
        d=d,
        e=e,
        modulus=modulus,
        h_reduced=h // d,
        delta_reduced=delta // e,
    )


def inverse_product_phase_mod_one(r: int, s: int, h: int, delta: int) -> Fraction:
    """Represent ``-h*delta*inv_s(r)/s`` as an exact element of Q/Z."""

    if s == 1:
        return Fraction(0)
    if gcd(r, s) != 1:
        raise ValueError("r must be invertible modulo s")
    return Fraction(-h * delta * pow(r, -1, s), s) % 1


def pascadi_2024_direct_dispersion_gap(box: ExponentBox) -> Fraction:
    """Gap from Pascadi 2024, Corollary 18 with C=D=1 and N=A.

    The regular-spectrum term dominates on the admissible polytope.  Its
    exponent is 3(rho+sigma)/2 + a/2 against the rho+sigma target.
    """

    if not is_admissible(box):
        raise ValueError("Pascadi gap is defined only on admissible boxes")
    return (box.rho + box.sigma + box.third_length) / 2


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
