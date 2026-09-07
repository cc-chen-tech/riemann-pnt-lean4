#!/usr/bin/env python3
"""Finite transcription guards for the RV3 and RV5 identities.

This script does not certify Poisson summation, the analytic large sieve, or the
ACZ theorem.  It checks only the exact finite algebra and exponent ledger to
which those theorems are applied.
"""

from __future__ import annotations

import cmath
import itertools
import math
from fractions import Fraction


def primes_up_to(limit: int) -> list[int]:
    result = []
    for n in range(2, limit + 1):
        if all(n % d for d in range(2, math.isqrt(n) + 1)):
            result.append(n)
    return result


def primitive_root(q: int) -> int:
    factors = []
    n = q - 1
    d = 2
    while d * d <= n:
        if n % d == 0:
            factors.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        factors.append(n)
    for g in range(2, q):
        if all(pow(g, (q - 1) // ell, q) != 1 for ell in factors):
            return g
    raise AssertionError(f"no primitive root modulo {q}")


def discrete_logs(q: int) -> dict[int, int]:
    g = primitive_root(q)
    logs = {}
    x = 1
    for exponent in range(q - 1):
        logs[x] = exponent
        x = x * g % q
    assert len(logs) == q - 1
    return logs


def character(q: int, index: int, n: int, logs: dict[int, int]) -> complex:
    residue = n % q
    if residue == 0:
        return 0j
    return cmath.exp(2j * math.pi * index * logs[residue] / (q - 1))


def product_coefficients(weights: dict[int, complex]) -> dict[int, complex]:
    coefficients: dict[int, complex] = {}
    for p1, p2 in itertools.product(weights, repeat=2):
        coefficients[p1 * p2] = (
            coefficients.get(p1 * p2, 0j) + weights[p1] * weights[p2]
        )
    return coefficients


def check_energy_identity(weights: dict[int, complex]) -> None:
    coefficients = product_coefficients(weights)
    energy = sum(abs(value) ** 2 for value in coefficients.values())
    sy = sum(abs(value) ** 2 for value in weights.values())
    fourth = sum(abs(value) ** 4 for value in weights.values())
    expected = 2 * sy * sy - fourth
    assert abs(energy - expected) < 1e-9 * max(1.0, abs(expected))
    assert energy <= 2 * sy * sy + 1e-9


def check_character_factorization(
    q: int, weights: dict[int, complex]
) -> int:
    coefficients = product_coefficients(weights)
    logs = discrete_logs(q)
    cases = 0
    for index in range(q - 1):
        prime_polynomial = sum(
            value * character(q, index, p, logs) for p, value in weights.items()
        )
        product_polynomial = sum(
            value * character(q, index, n, logs)
            for n, value in coefficients.items()
        )
        assert abs(prime_polynomial**2 - product_polynomial) < 1e-8
        cases += 1
    return cases


def check_gauss_identity(q: int) -> int:
    """Check sum_r chi(r)e(hr/q) = conjugate(chi(h))*tau(chi)."""
    logs = discrete_logs(q)
    cases = 0
    wrong_orientation_detected = False
    for index in range(1, q - 1):
        tau = sum(
            character(q, index, residue, logs)
            * cmath.exp(2j * math.pi * residue / q)
            for residue in range(q)
        )
        assert abs(abs(tau) - math.sqrt(q)) < 1e-9
        for h in range(1, q):
            twisted = sum(
                character(q, index, residue, logs)
                * cmath.exp(2j * math.pi * h * residue / q)
                for residue in range(q)
            )
            expected = character(q, index, h, logs).conjugate() * tau
            assert abs(twisted - expected) < 1e-8
            wrong_orientation = character(q, index, h, logs) * tau
            if abs(twisted - wrong_orientation) > 1e-6:
                wrong_orientation_detected = True
            cases += 1
    assert wrong_orientation_detected
    return cases


def main() -> None:
    prime_pool = primes_up_to(31)
    samples = [
        {p: complex((p % 5) - 2, (p % 7) - 3) for p in prime_pool[1:5]},
        {p: complex((-1) ** p, p % 3 - 1) for p in prime_pool[2:7]},
        {p: complex(p - 10, 2 * p - 17) for p in prime_pool[3:8]},
    ]
    character_cases = 0
    gauss_cases = 0
    for weights in samples:
        check_energy_identity(weights)
        for q in (5, 7, 11, 13):
            character_cases += check_character_factorization(q, weights)

    for q in (5, 7, 11, 13):
        gauss_cases += check_gauss_identity(q)

    # RV5.8 uses M_Y <= (log P / P) S_Y and RV4.2 costs P S_Y^2.
    # Their P powers cancel before the outer square root.
    flatness_power = -1
    large_sieve_power = 1
    assert (flatness_power + large_sieve_power) / 2 == 0

    # In RV5.6, (A/sqrt(q))^4 * H^2 with H=q/A is exactly A^2.
    a_power = Fraction(4) + Fraction(-2)
    q_power = Fraction(-2) + Fraction(2)
    assert a_power == 2
    assert q_power == 0

    print(f"RV3 energy samples: {len(samples)}")
    print(f"RV3 character-factorization cases: {character_cases}")
    print(f"RV5 Gauss-identity cases: {gauss_cases}")
    print("RV5 exponent ledger: exact")


if __name__ == "__main__":
    main()
