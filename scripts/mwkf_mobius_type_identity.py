#!/usr/bin/env python3
"""Finite checks for the exact Möbius Type-I/II decomposition."""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import gcd, isqrt


@dataclass(frozen=True)
class CenteredResonanceCoordinates:
    j: int
    w: int

    @property
    def linear_slope(self) -> int:
        return self.j + 1

    @property
    def distance(self) -> int:
        return abs(self.w)


@dataclass(frozen=True)
class ProportionalDiagonalCoordinates:
    sign: int
    common_n_factor: int
    primitive_n1: int
    primitive_n2: int
    common_y_factor: int


@dataclass(frozen=True)
class RestrictedZeroRayPairConvolution:
    u: int
    v: int
    k: int
    cutoff_u: int
    left_product: int
    right_product: int
    left_sector_sum: int
    right_sector_sum: int
    pair_sector_product: int
    squarefree_ray_support: bool
    common_k_mobius_cancels_exactly: bool


@dataclass(frozen=True)
class ZeroRayPhaseReduction:
    s_u: int
    a_u: int
    s_k: int
    a_k: int
    original_fixed_phase: Fraction
    reduced_fixed_phase: Fraction
    original_real_phase: Fraction
    product_real_phase: Fraction
    original_common_b_phase: Fraction
    product_common_b_phase: Fraction
    primitive_slope_removed_from_reciprocal_phase: bool


def proportional_diagonal_coordinates(
    *,
    n1: int,
    y1: int,
    n2: int,
    y2: int,
) -> ProportionalDiagonalCoordinates:
    """Parameterize exactly the zero complementary-divisor equation.

    For nonzero signed ``n_i`` and positive ``y_i``, the equation
    ``n1*y2=n2*y1`` forces the signs of ``n1,n2`` to agree.  Writing
    ``|n1|=g*u`` and ``|n2|=g*v`` with ``(u,v)=1`` then gives uniquely
    ``y1=u*k`` and ``y2=v*k``.
    """
    if n1 == 0 or n2 == 0 or y1 <= 0 or y2 <= 0:
        raise ValueError("require nonzero n_i and positive y_i")
    if n1 * y2 != n2 * y1:
        raise ValueError("not on the zero-complementary ray")

    common_n_factor = gcd(abs(n1), abs(n2))
    primitive_n1 = abs(n1) // common_n_factor
    primitive_n2 = abs(n2) // common_n_factor
    if y1 % primitive_n1 != 0 or y2 % primitive_n2 != 0:
        raise AssertionError("primitive proportionality divisibility failed")
    common_y_factor = y1 // primitive_n1
    if y2 // primitive_n2 != common_y_factor:
        raise AssertionError("primitive proportionality factor mismatch")

    return ProportionalDiagonalCoordinates(
        sign=1 if n1 > 0 else -1,
        common_n_factor=common_n_factor,
        primitive_n1=primitive_n1,
        primitive_n2=primitive_n2,
        common_y_factor=common_y_factor,
    )


def centered_resonance_coordinates(
    *,
    r: int,
    s: int,
) -> CenteredResonanceCoordinates:
    """Write ``r-s=j*s+w`` with the unique ``-s/2 < w <= s/2``.

    The positive representative is selected at an even-modulus tie.  Thus
    ``r=(j+1)*s+w`` and every integer product frequency satisfies
    ``a*r == a*w (mod s)`` without evaluating an exponential.
    """
    if r <= 0 or s <= 0:
        raise ValueError("require r,s > 0")
    difference = r - s
    w = difference % s
    if 2 * w > s:
        w -= s
    numerator = difference - w
    assert numerator % s == 0
    return CenteredResonanceCoordinates(j=numerator // s, w=w)


def _restricted_mobius(n: int, modulus: int) -> int:
    """Return ``mu(n)`` restricted to integers coprime to ``modulus``."""
    return mobius(n) if gcd(n, modulus) == 1 else 0


def coprime_centered_mobius_reindex(
    *,
    s: int,
    w: int,
    slope: int,
    q: int,
) -> int:
    """Evaluate the exact common-divisor reindexing of a centered pair.

    Put ``r=slope*s+w`` and ``mu_Q(n)=mu(n) 1_(n,Q)=1``.  Möbius
    inversion of ``(s,w)=1`` gives

    ``mu_q(s) mu_q(r) 1_(s,w)=1``
    `` = sum_{d|(s,w), (d,q)=1} mu(d)``
    ``     * mu_{qd}(s/d) mu_{qd}(slope*s/d+w/d)``.

    The return value is the right-hand side.  This finite helper checks
    the reindexing only; it makes no estimate for the resulting sums.
    """
    if s <= 0 or slope <= 0 or q <= 0:
        raise ValueError("require s, slope, q > 0")
    r = slope * s + w
    if r <= 0:
        raise ValueError("require slope*s+w > 0")

    total = 0
    common_divisor = gcd(s, abs(w))
    for d in divisors(common_divisor):
        coefficient = mobius(d)
        if coefficient == 0 or gcd(d, q) != 1:
            continue
        n = s // d
        shift = w // d
        restricted_modulus = q * d
        total += (
            coefficient
            * _restricted_mobius(n, restricted_modulus)
            * _restricted_mobius(
                slope * n + shift,
                restricted_modulus,
            )
        )
    return total


def mobius(n: int) -> int:
    if n < 1:
        raise ValueError("n must be positive")
    value = n
    primes = 0
    p = 2
    while p * p <= value:
        if value % p == 0:
            value //= p
            primes += 1
            if value % p == 0:
                return 0
            while value % p == 0:
                value //= p
        p += 1
    if value > 1:
        primes += 1
    return -1 if primes % 2 else 1


def divisors(n: int) -> tuple[int, ...]:
    small: list[int] = []
    large: list[int] = []
    for d in range(1, isqrt(n) + 1):
        if n % d == 0:
            small.append(d)
            if d * d != n:
                large.append(n // d)
    return tuple(small + list(reversed(large)))


def c_u(a: int, cutoff_u: int) -> int:
    return sum(mobius(d) for d in divisors(a) if d <= cutoff_u)


def full_truncated_mobius_convolution(
    *,
    n: int,
    cutoff_u: int,
) -> int:
    """Evaluate ``(mu*c_U)(n)=mu(n) 1_(n<=U)`` as a finite sum."""
    if n < 1 or cutoff_u < 1:
        raise ValueError("require n, cutoff_u >= 1")
    return sum(
        mobius(s) * c_u(n // s, cutoff_u)
        for s in divisors(n)
    )


def restricted_truncated_mobius_convolution(
    *,
    n: int,
    cutoff_u: int,
) -> int:
    """Evaluate the actual ``a>U`` convolution in one Type sector."""
    if n < 1 or cutoff_u < 1:
        raise ValueError("require n, cutoff_u >= 1")
    return sum(
        mobius(s) * c_u(n // s, cutoff_u)
        for s in divisors(n)
        if n // s > cutoff_u
    )


def restricted_zero_ray_pair_convolution(
    *,
    u: int,
    v: int,
    k: int,
    cutoff_u: int,
) -> RestrictedZeroRayPairConvolution:
    """Evaluate both restricted convolutions on one primitive zero ray.

    On squarefree support, ``(u,v)=1`` and the two products ``u*k`` and
    ``v*k`` squarefree imply ``(k,u*v)=1``.  Hence the common factor
    contributes ``mu(k)^2=1`` and the paired main coefficient is exactly
    ``mu(u)*mu(v)`` rather than a Möbius weight in ``k``.
    """
    if u < 1 or v < 1 or k < 1 or cutoff_u < 1:
        raise ValueError("require u, v, k, cutoff_u >= 1")
    if gcd(u, v) != 1:
        raise ValueError("require primitive coprime ray coordinates")

    left_product = u * k
    right_product = v * k
    left_sector_sum = restricted_truncated_mobius_convolution(
        n=left_product,
        cutoff_u=cutoff_u,
    )
    right_sector_sum = restricted_truncated_mobius_convolution(
        n=right_product,
        cutoff_u=cutoff_u,
    )
    pair_sector_product = left_sector_sum * right_sector_sum
    squarefree_ray_support = (
        mobius(left_product) != 0 and mobius(right_product) != 0
    )
    common_k_mobius_cancels_exactly = (
        left_product > cutoff_u
        and right_product > cutoff_u
        and squarefree_ray_support
        and pair_sector_product == mobius(u) * mobius(v)
    )

    return RestrictedZeroRayPairConvolution(
        u=u,
        v=v,
        k=k,
        cutoff_u=cutoff_u,
        left_product=left_product,
        right_product=right_product,
        left_sector_sum=left_sector_sum,
        right_sector_sum=right_sector_sum,
        pair_sector_product=pair_sector_product,
        squarefree_ray_support=squarefree_ray_support,
        common_k_mobius_cancels_exactly=(
            common_k_mobius_cancels_exactly
        ),
    )


def _normalized_modular_phase(
    *,
    numerator: int,
    invert: int,
    modulus: int,
) -> Fraction:
    if modulus < 1:
        raise ValueError("modulus must be positive")
    if modulus == 1:
        return Fraction(0)
    if gcd(invert, modulus) != 1:
        raise ValueError("phase denominator is not invertible")
    residue = numerator * pow(invert, -1, modulus) % modulus
    return Fraction(residue, modulus)


def zero_ray_phase_reduction(
    *,
    u: int,
    k: int,
    s: int,
    a: int,
    b: int,
    g: int,
) -> ZeroRayPhaseReduction:
    """Remove the primitive slope from all zero-ray reciprocal phases.

    Assume the original squarefree support, ``s*a=u*k`` and
    ``(u,k)=(s,a)=(u*k,b)=1``.  Splitting the prime allocation as
    ``s=s_u*s_k`` and ``a=a_u*a_k`` gives

    ``g*u*bar(s*b)/a = g*bar(s_k*b)/a_k (mod 1)``.

    The smooth real phase is exactly ``-g/(k*b)``, and the common-``b``
    phase is ``g*bar(k)/b``.  Thus none of these phases has a primitive
    slope conductor.
    """
    if min(u, k, s, a, b) < 1 or g == 0:
        raise ValueError("require positive factors and nonzero g")
    if mobius(u * k) == 0:
        raise ValueError("require squarefree u*k")
    if gcd(u, k) != 1 or s * a != u * k:
        raise ValueError("require coprime u,k and s*a=u*k")
    if gcd(s, a) != 1 or gcd(u * k, b) != 1:
        raise ValueError("require the original coprimality support")

    s_u = gcd(s, u)
    a_u = gcd(a, u)
    s_k = gcd(s, k)
    a_k = gcd(a, k)
    if s_u * a_u != u or s_k * a_k != k:
        raise AssertionError("squarefree prime allocation failed")
    if s_u * s_k != s or a_u * a_k != a:
        raise AssertionError("factorization allocation mismatch")

    original_fixed_phase = _normalized_modular_phase(
        numerator=g * u,
        invert=s * b,
        modulus=a,
    )
    reduced_fixed_phase = _normalized_modular_phase(
        numerator=g,
        invert=s_k * b,
        modulus=a_k,
    )
    original_real_phase = Fraction(-g * u, a * b * s)
    product_real_phase = Fraction(-g, k * b)
    original_common_b_phase = _normalized_modular_phase(
        numerator=g * u,
        invert=s * a,
        modulus=b,
    )
    product_common_b_phase = _normalized_modular_phase(
        numerator=g,
        invert=k,
        modulus=b,
    )
    primitive_slope_removed = (
        original_fixed_phase == reduced_fixed_phase
        and original_real_phase == product_real_phase
        and original_common_b_phase == product_common_b_phase
    )

    return ZeroRayPhaseReduction(
        s_u=s_u,
        a_u=a_u,
        s_k=s_k,
        a_k=a_k,
        original_fixed_phase=original_fixed_phase,
        reduced_fixed_phase=reduced_fixed_phase,
        original_real_phase=original_real_phase,
        product_real_phase=product_real_phase,
        original_common_b_phase=original_common_b_phase,
        product_common_b_phase=product_common_b_phase,
        primitive_slope_removed_from_reciprocal_phase=(
            primitive_slope_removed
        ),
    )


def split_mobius_identity(
    n: int,
    *,
    cutoff_u: int,
    cutoff_v: int,
) -> tuple[int, int, int]:
    """Return ``mu(n)``, the Type-I sum, and the Type-II sum.

    This interface requires ``n > cutoff_u``.  The identity checked is
    ``mu(n) = -(type_i + type_ii)``.
    """
    if n <= cutoff_u:
        raise ValueError("identity requires n > cutoff_u")
    type_i = 0
    type_ii = 0
    for a in divisors(n):
        if a <= cutoff_u:
            continue
        b = n // a
        term = c_u(a, cutoff_u) * mobius(b)
        if b <= cutoff_v:
            type_i += term
        else:
            type_ii += term
    return mobius(n), type_i, type_ii


def double_split_mobius_identity(
    r: int,
    s: int,
    *,
    cutoff_u: int,
    cutoff_v: int,
) -> tuple[int, dict[str, int]]:
    """Split ``mu(r) * mu(s)`` into the four exact Type sectors.

    Each one-variable identity has a minus sign.  Their product therefore
    has a plus sign in every ``I/I``, ``I/II``, ``II/I``, and ``II/II``
    sector.
    """
    mu_r, r_i, r_ii = split_mobius_identity(
        r, cutoff_u=cutoff_u, cutoff_v=cutoff_v
    )
    mu_s, s_i, s_ii = split_mobius_identity(
        s, cutoff_u=cutoff_u, cutoff_v=cutoff_v
    )
    sectors = {
        "I/I": r_i * s_i,
        "I/II": r_i * s_ii,
        "II/I": r_ii * s_i,
        "II/II": r_ii * s_ii,
    }
    return mu_r * mu_s, sectors


def crt_reciprocity_numerators(
    *,
    s: int,
    a: int,
    b: int,
    n: int,
) -> tuple[Fraction, Fraction, Fraction]:
    """Return the three rational phases in the squarefree CRT identity.

    If ``(a,b)=(s,a*b)=1``, then modulo one

    ``n*bar(s)/(a*b) = n*bar(s*b)/a + n*bar(s*a)/b``.

    Returning exact :class:`Fraction` values lets tests check the congruence
    without floating-point evaluation of the exponential.
    """
    if a <= 1 or b <= 1 or gcd(a, b) != 1 or gcd(s, a * b) != 1:
        raise ValueError("require a,b > 1 and (a,b)=(s,a*b)=1")
    inverse = Fraction(n * pow(s, -1, a * b), a * b)
    mod_a = Fraction(n * pow(s * b, -1, a), a)
    mod_b = Fraction(n * pow(s * a, -1, b), b)
    return inverse, mod_a, mod_b


def poisson_congruence_reparametrization(
    *,
    r: int,
    s: int,
    delta: int,
    k: int,
) -> tuple[int, int]:
    """Reparametrize an ``h``-Poisson frequency by a shifted equation.

    With ``bar(r)`` chosen modulo ``s``, put
    ``v = k*s + delta*bar(r)``.  Then the returned integer ``j`` satisfies
    the exact equation ``delta = r*v - j*s``.
    """
    if r <= 0 or s <= 1 or gcd(r, s) != 1:
        raise ValueError("require r > 0, s > 1, and (r,s)=1")
    v = k * s + delta * pow(r, -1, s)
    numerator = r * v - delta
    assert numerator % s == 0
    return v, numerator // s


def determinant_lattice_solution(
    *,
    r: int,
    s: int,
    delta: int,
    translate: int,
) -> tuple[int, int]:
    """Parameterize the full affine lattice ``r*v-j*s=delta``.

    Choose ``v_0`` as the inverse of ``r`` modulo ``s`` and put
    ``j_0=(r*v_0-1)/s``.  Every translated pair

    ``j=delta*j_0+translate*r``,
    ``v=delta*v_0+translate*s``

    has determinant ``delta``; conversely every integral solution is one
    such translate because ``(r,s)=1``.
    """
    if r <= 0 or s <= 1 or gcd(r, s) != 1:
        raise ValueError("require r > 0, s > 1, and (r,s)=1")
    v_0 = pow(r, -1, s)
    j_0 = (r * v_0 - 1) // s
    return delta * j_0 + translate * r, delta * v_0 + translate * s


def _ceil_div(numerator: int, denominator: int) -> int:
    return -((-numerator) // denominator)


def signed_shift_solutions(
    *,
    r: int,
    s: int,
    v: int,
    delta_min: int,
    delta_max: int,
    sign: int,
) -> tuple[tuple[int, int], ...]:
    """Return every ``(j,delta)`` in one signed determinant window.

    The returned solutions satisfy ``delta=r*v-j*s`` and
    ``delta_min <= sign*delta <= delta_max``.  If the window width is
    strictly smaller than ``s``, the tuple has length at most one.
    """
    if r <= 0 or s <= 0:
        raise ValueError("require r,s > 0")
    if delta_min < 0 or delta_min > delta_max:
        raise ValueError("require 0 <= delta_min <= delta_max")
    if sign not in (-1, 1):
        raise ValueError("sign must be -1 or 1")
    product = r * v
    if sign == 1:
        j_min = _ceil_div(product - delta_max, s)
        j_max = (product - delta_min) // s
    else:
        j_min = _ceil_div(product + delta_min, s)
        j_max = (product + delta_max) // s
    return tuple((j, product - j * s) for j in range(j_min, j_max + 1))


def nonzero_character_orthogonality(modulus: int, integer: int) -> int:
    """Exact sum of all nontrivial additive characters modulo ``modulus``.

    Algebraically,
    ``sum_{c=1}^{s-1} exp(2*pi*i*c*n/s)`` is ``s-1`` when ``s|n`` and
    ``-1`` otherwise.  Returning that integer avoids floating-point roots
    of unity in the finite-completion audit.
    """
    if modulus <= 1:
        raise ValueError("modulus must exceed one")
    return modulus - 1 if integer % modulus == 0 else -1


def centered_completion_via_orthogonality(
    values: tuple[int | Fraction, ...],
    *,
    residue: int,
) -> Fraction:
    """Evaluate the nonzero-frequency centered finite Fourier inversion.

    For a function ``G`` on ``Z/sZ``, nonzero-character orthogonality gives

    ``G(n)-G(0) = (1/s) sum_x G(x) [K(n-x)-K(-x)]``,

    where ``K(y)`` is the sum of the nontrivial additive characters.  Thus
    a signed shift weight with ``G(0)=0`` is recovered using only nonzero
    completion frequencies and the centered phase ``e(c*n/s)-1``.
    """
    modulus = len(values)
    if modulus <= 1:
        raise ValueError("values must define a group of order > 1")
    n = residue % modulus
    total = sum(
        Fraction(value)
        * (
            nonzero_character_orthogonality(modulus, n - x)
            - nonzero_character_orthogonality(modulus, -x)
        )
        for x, value in enumerate(values)
    )
    return total / modulus


def centered_product_frequency_coefficients(
    terms: tuple[tuple[int, int, int | Fraction], ...],
) -> dict[int, Fraction]:
    """Group a centered ``(c,v)`` sum exactly by ``a=c*v``.

    The centered completion has no ``c=0`` term and carries the phase
    ``e(c*v*r/s)-1``.  Terms with ``v=0`` therefore vanish identically.
    Every remaining pair has a nonzero integer product, so finite
    reindexing gives one coefficient for each product frequency ``a``.
    """
    grouped: dict[int, Fraction] = {}
    for c, v, weight in terms:
        if c == 0:
            raise ValueError("completion frequency c must be nonzero")
        if v == 0:
            continue
        product = c * v
        new_weight = grouped.get(product, Fraction(0)) + Fraction(weight)
        if new_weight:
            grouped[product] = new_weight
        else:
            grouped.pop(product, None)
    return grouped


def bilinear_gauss_via_orthogonality(
    *,
    r: int,
    modulus: int,
    c: int,
    v: int,
) -> tuple[int, int]:
    """Return the exact coefficient and phase of the finite bilinear kernel.

    If ``bar(r)`` is the inverse of ``r`` modulo ``s``, summing first in
    ``x`` gives

    ``sum_{x,y mod s} e((c*x+v*y-bar(r)*x*y)/s)``
    ``= s*e(r*c*v/s)``.

    The return value ``(s, r*c*v mod s)`` records this identity without
    evaluating any floating-point roots of unity.
    """
    if modulus <= 1 or gcd(r, modulus) != 1:
        raise ValueError("require modulus > 1 and (r,modulus)=1")
    surviving_y = (r * c) % modulus
    return modulus, (v * surviving_y) % modulus


def double_centered_completion_via_orthogonality(
    values: tuple[tuple[int | Fraction, ...], ...],
    *,
    residue_x: int,
    residue_y: int,
) -> Fraction:
    """Evaluate exact two-dimensional nonzero-character centering.

    For a function ``F`` on ``(Z/sZ)^2``, the centered transform equals

    ``F(x,y)-F(x,0)-F(0,y)+F(0,0)``.

    In particular, if ``F`` vanishes on both coordinate axes, its complete
    value is recovered using only nonzero characters in both variables.
    """
    modulus = len(values)
    if modulus <= 1 or any(len(row) != modulus for row in values):
        raise ValueError("values must be a square group table of order > 1")
    target_x = residue_x % modulus
    target_y = residue_y % modulus
    total = Fraction(0)
    for x, row in enumerate(values):
        kernel_x = (
            nonzero_character_orthogonality(modulus, target_x - x)
            - nonzero_character_orthogonality(modulus, -x)
        )
        for y, value in enumerate(row):
            kernel_y = (
                nonzero_character_orthogonality(modulus, target_y - y)
                - nonzero_character_orthogonality(modulus, -y)
            )
            total += Fraction(value) * kernel_x * kernel_y
    return total / (modulus * modulus)


@dataclass(frozen=True)
class TypeScaleBounds:
    u_exp: Fraction
    v_exp: Fraction
    type_i_a_min: Fraction
    type_ii_a_min: Fraction
    type_ii_a_max: Fraction
    type_ii_b_min: Fraction
    type_ii_b_max: Fraction


def type_scale_bounds(
    rho: Fraction,
    *,
    u: Fraction,
    v: Fraction,
) -> TypeScaleBounds:
    if rho < 0 or not (0 < u < 1) or not (0 < v < 1):
        raise ValueError("require rho >= 0 and 0 < u,v < 1")
    u_exp = rho * u
    v_exp = rho * v
    return TypeScaleBounds(
        u_exp=u_exp,
        v_exp=v_exp,
        type_i_a_min=rho - v_exp,
        type_ii_a_min=u_exp,
        type_ii_a_max=rho - v_exp,
        type_ii_b_min=v_exp,
        type_ii_b_max=rho - u_exp,
    )
