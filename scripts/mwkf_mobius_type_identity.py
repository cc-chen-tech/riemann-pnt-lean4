#!/usr/bin/env python3
"""Finite checks for the exact Möbius Type-I/II decomposition."""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import gcd, isqrt


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
