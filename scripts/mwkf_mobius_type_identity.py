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


@dataclass(frozen=True)
class CommonBPhaseReciprocity:
    determinant: int
    original_phase: Fraction
    determinant_phase: Fraction
    smooth_real_phase: Fraction
    dual_reciprocal_phase: Fraction
    reciprocal_completed_phase: Fraction
    b_divides_determinant: bool


@dataclass(frozen=True)
class DeterminantLineCoordinates:
    gcd_j_v: int
    primitive_j: int
    primitive_v: int
    shift_quotient: int
    particular_r: int
    particular_s: int

    def solution(self, n: int) -> tuple[int, int]:
        return (
            self.particular_r + self.primitive_j * n,
            self.particular_s + self.primitive_v * n,
        )


@dataclass(frozen=True)
class DeterminantSlopeSquareCoordinates:
    shift1: int
    shift2: int
    cross_determinant: int
    recovered_primitive_j: int | None
    recovered_primitive_v: int | None
    zero_determinant_is_identity_diagonal: bool


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


def _fractional_part(value: Fraction) -> Fraction:
    return Fraction(value.numerator % value.denominator, value.denominator)


def common_b_phase_reciprocity(
    *,
    n1: int,
    y1: int,
    n2: int,
    y2: int,
    b: int,
) -> CommonBPhaseReciprocity:
    """Rewrite the full common-``b`` phase without imposing ``b|Delta``.

    With ``Delta=n1*y2-n2*y1`` and ``(b,y1*y2)=1``, the phase is

    ``Delta*bar(y1*y2)/b``
    `` = Delta/(b*y1*y2)-Delta*bar(b)/(y1*y2) (mod 1)``.

    Divisibility by ``b`` is only a special zero mode, not a condition in
    the original expanded square.
    """
    if min(y1, y2, b) < 1:
        raise ValueError("require positive y1, y2, b")
    product = y1 * y2
    if gcd(b, product) != 1:
        raise ValueError("require b coprime to y1*y2")

    determinant = n1 * y2 - n2 * y1
    original_phase = _fractional_part(
        _normalized_modular_phase(
            numerator=n1,
            invert=y1,
            modulus=b,
        )
        + _normalized_modular_phase(
            numerator=-n2,
            invert=y2,
            modulus=b,
        )
    )
    determinant_phase = _normalized_modular_phase(
        numerator=determinant,
        invert=product,
        modulus=b,
    )
    smooth_real_phase = Fraction(determinant, b * product)
    dual_reciprocal_phase = _normalized_modular_phase(
        numerator=-determinant,
        invert=b,
        modulus=product,
    )
    reciprocal_completed_phase = _fractional_part(
        smooth_real_phase + dual_reciprocal_phase
    )

    return CommonBPhaseReciprocity(
        determinant=determinant,
        original_phase=original_phase,
        determinant_phase=determinant_phase,
        smooth_real_phase=smooth_real_phase,
        dual_reciprocal_phase=dual_reciprocal_phase,
        reciprocal_completed_phase=reciprocal_completed_phase,
        b_divides_determinant=determinant % b == 0,
    )


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


def _extended_gcd_nonnegative(a: int, b: int) -> tuple[int, int, int]:
    if a < 0 or b < 0:
        raise ValueError("extended gcd inputs must be nonnegative")
    old_r, r = a, b
    old_s, s = 1, 0
    old_t, t = 0, 1
    while r:
        quotient = old_r // r
        old_r, r = r, old_r - quotient * r
        old_s, s = s, old_s - quotient * s
        old_t, t = t, old_t - quotient * t
    return old_r, old_s, old_t


def determinant_line_coordinates(
    *,
    j: int,
    v: int,
    delta: int,
) -> DeterminantLineCoordinates:
    """Parameterize exactly ``r*v-j*s=delta`` by one integer ``n``.

    Put ``g=(|j|,|v|)``.  Solubility forces ``g|delta``.  After dividing
    by ``g``, Bezout gives a particular solution; the primitive kernel
    vector is ``(j/g,v/g)``.  Hence every solution is returned exactly
    once by :meth:`DeterminantLineCoordinates.solution`.
    """
    if j == 0 or v == 0 or delta == 0:
        raise ValueError("require nonzero j, v, and delta")
    common_gcd = gcd(abs(j), abs(v))
    if delta % common_gcd != 0:
        raise ValueError("determinant shift is not divisible by (j,v)")

    primitive_j = j // common_gcd
    primitive_v = v // common_gcd
    shift_quotient = delta // common_gcd
    bezout_gcd, x_abs, y_abs = _extended_gcd_nonnegative(
        abs(primitive_v),
        abs(primitive_j),
    )
    if bezout_gcd != 1:
        raise AssertionError("primitive determinant slopes are not coprime")
    x = x_abs if primitive_v > 0 else -x_abs
    y = y_abs if primitive_j > 0 else -y_abs
    if x * primitive_v + y * primitive_j != 1:
        raise AssertionError("signed Bezout normalization failed")

    particular_r = shift_quotient * x
    particular_s = -shift_quotient * y
    if (
        particular_r * primitive_v
        - particular_s * primitive_j
        != shift_quotient
    ):
        raise AssertionError("particular determinant solution failed")

    return DeterminantLineCoordinates(
        gcd_j_v=common_gcd,
        primitive_j=primitive_j,
        primitive_v=primitive_v,
        shift_quotient=shift_quotient,
        particular_r=particular_r,
        particular_s=particular_s,
    )


def determinant_line_coprimality_residue(
    coordinates: DeterminantLineCoordinates,
    *,
    divisor: int,
) -> int:
    """Return the unique ``n mod divisor`` making both line entries zero."""
    if divisor < 1 or abs(coordinates.shift_quotient) % divisor != 0:
        raise ValueError("require a positive divisor of the shift quotient")
    if mobius(divisor) == 0:
        raise ValueError("require a squarefree divisor")
    hits = tuple(
        n
        for n in range(divisor)
        if all(value % divisor == 0 for value in coordinates.solution(n))
    )
    if len(hits) != 1:
        raise AssertionError("coprime primitive slopes must give one residue")
    return hits[0]


def determinant_line_coprimality_indicator(
    coordinates: DeterminantLineCoordinates,
    *,
    n: int,
) -> int:
    """Evaluate the exact divisor expansion of ``1_(r_n,s_n)=1``."""
    total = 0
    for divisor in divisors(abs(coordinates.shift_quotient)):
        coefficient = mobius(divisor)
        if coefficient == 0:
            continue
        residue = determinant_line_coprimality_residue(
            coordinates,
            divisor=divisor,
        )
        if n % divisor == residue:
            total += coefficient
    return total


def determinant_slope_square_coordinates(
    *,
    r1: int,
    s1: int,
    r2: int,
    s2: int,
    primitive_j: int,
    primitive_v: int,
) -> DeterminantSlopeSquareCoordinates:
    """Recover the common slope in the square of a determinant-line sum.

    With ``delta_i=r_i*v-s_i*j`` and
    ``Delta=r1*s2-r2*s1``, Cramer's rule gives, for ``Delta != 0``,

    ``v=(delta1*s2-delta2*s1)/Delta`` and
    ``j=(delta1*r2-delta2*r1)/Delta``.

    If ``Delta=0`` and both positive pairs ``(r_i,s_i)`` are primitive,
    proportionality forces the pairs to be identical.  This is exactly
    the positive identity diagonal in the slope square function.
    """
    if min(r1, s1, r2, s2) < 1:
        raise ValueError("require positive determinant-row entries")
    if gcd(r1, s1) != 1 or gcd(r2, s2) != 1:
        raise ValueError("require primitive determinant-row pairs")
    if primitive_j == 0 or primitive_v == 0:
        raise ValueError("require a nonzero primitive slope")
    if gcd(abs(primitive_j), abs(primitive_v)) != 1:
        raise ValueError("require coprime primitive slope entries")

    shift1 = r1 * primitive_v - s1 * primitive_j
    shift2 = r2 * primitive_v - s2 * primitive_j
    cross_determinant = r1 * s2 - r2 * s1
    if cross_determinant == 0:
        if (r1, s1) != (r2, s2):
            raise AssertionError(
                "positive primitive proportional pairs must be equal"
            )
        return DeterminantSlopeSquareCoordinates(
            shift1=shift1,
            shift2=shift2,
            cross_determinant=0,
            recovered_primitive_j=None,
            recovered_primitive_v=None,
            zero_determinant_is_identity_diagonal=True,
        )

    v_numerator = shift1 * s2 - shift2 * s1
    j_numerator = shift1 * r2 - shift2 * r1
    if (
        v_numerator % cross_determinant != 0
        or j_numerator % cross_determinant != 0
    ):
        raise AssertionError("Cramer numerators are not integral")
    recovered_v = v_numerator // cross_determinant
    recovered_j = j_numerator // cross_determinant
    if (recovered_j, recovered_v) != (primitive_j, primitive_v):
        raise AssertionError("Cramer recovery changed the primitive slope")

    return DeterminantSlopeSquareCoordinates(
        shift1=shift1,
        shift2=shift2,
        cross_determinant=cross_determinant,
        recovered_primitive_j=recovered_j,
        recovered_primitive_v=recovered_v,
        zero_determinant_is_identity_diagonal=False,
    )


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


def double_zero_sum_nonzero_mass(
    values: tuple[tuple[int | Fraction, ...], ...],
) -> tuple[Fraction, Fraction]:
    """Identify the constant mass left after double centering.

    If every row and every column of ``Theta`` sums to zero, then

    ``sum_(c != 0, v != 0) Theta(c,v) = Theta(0,0)``.

    Thus the ``-1`` in a centered phase does not vanish by itself; its
    nonzero-frequency contribution is exactly ``-Theta(0,0)``.  The
    equality uses the full two-dimensional zero-sum structure.
    """
    modulus = len(values)
    if modulus == 0 or any(len(row) != modulus for row in values):
        raise ValueError("values must be a nonempty square group table")
    table = tuple(tuple(Fraction(value) for value in row) for row in values)
    if any(sum(row, Fraction(0)) != 0 for row in table) or any(
        sum((table[c][v] for c in range(modulus)), Fraction(0)) != 0
        for v in range(modulus)
    ):
        raise ValueError("row and column sums must vanish")
    nonzero_mass = sum(
        (
            table[c][v]
            for c in range(1, modulus)
            for v in range(1, modulus)
        ),
        Fraction(0),
    )
    return nonzero_mass, table[0][0]


def restricted_squarefree_expansion(*, e: int, modulus: int) -> int:
    """Expand the exact squarefree and coprimality support of ``e``.

    The returned double divisor sum is

    ``sum_(k^2|e) mu(k) * sum_(ell|(e,modulus)) mu(ell)``

    and therefore equals ``mu(e)^2 * 1_(e,modulus)=1``.  This is the
    expansion required before Poisson summation can turn the remaining
    cofactor into an unweighted integer variable.
    """
    if e <= 0 or modulus <= 0:
        raise ValueError("e and modulus must be positive")
    squarefree_sum = sum(
        mobius(k) for k in divisors(e) if e % (k * k) == 0
    )
    coprimality_sum = sum(mobius(ell) for ell in divisors(gcd(e, modulus)))
    return squarefree_sum * coprimality_sum


def long_cutoff_quotient_progression(
    *,
    j: int,
    delta: int,
    b: int,
    d: int,
    v: int,
) -> tuple[int, int] | None:
    """Reduce the exact integrality condition for the quotient cofactor.

    After writing ``r=a*b`` and expanding
    ``c_U(a)=sum_(d|a,d<=U) mu(d)`` with ``a=d*e``, the determinant

    ``d*e*b*v-j*s=delta``

    makes ``e`` integral precisely when ``j*s+delta`` is divisible by
    ``b*d*v``.  Put ``M=|b*d*v|`` and ``g=(j,M)``.  There is no solution
    unless ``g|delta``; otherwise the condition is the single reduced
    progression

    ``s = -(delta/g)*(j/g)^(-1) (mod M/g)``.

    The returned residue is the least nonnegative representative.  In
    particular the gcd reduction can only decrease the modulus used by a
    possible arithmetic-progression theorem.
    """
    if b <= 0 or d <= 0 or v == 0:
        raise ValueError("b,d must be positive and v nonzero")
    modulus = abs(b * d * v)
    common = gcd(j, modulus)
    if delta % common:
        return None
    reduced_modulus = modulus // common
    if reduced_modulus == 1:
        return 1, 0
    reduced_j = j // common
    reduced_delta = delta // common
    residue = (-reduced_delta * pow(reduced_j, -1, reduced_modulus)) % (
        reduced_modulus
    )
    return reduced_modulus, residue


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
