#!/usr/bin/env python3
"""Finite checks for the exact Möbius Type-I/II decomposition."""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import isqrt


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
