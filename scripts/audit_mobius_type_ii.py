#!/usr/bin/env python3
"""Finite Möbius identity and fixed-factor Type-I exponent audit.

This module verifies finite convolution algebra and rational inequalities.
It does not prove the residual averaged Type-II oscillatory estimate.
"""

from __future__ import annotations

import cmath
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from math import gcd

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
