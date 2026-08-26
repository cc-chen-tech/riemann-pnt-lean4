#!/usr/bin/env python3
"""Finite Möbius identity and fixed-factor Type-I exponent audit.

This module verifies finite convolution algebra and rational inequalities.
It does not prove the residual averaged Type-II oscillatory estimate.
"""

from __future__ import annotations

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
