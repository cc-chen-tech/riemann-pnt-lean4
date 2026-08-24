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
