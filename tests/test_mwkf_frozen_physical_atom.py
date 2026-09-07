"""Exact finite guards for MWKF-PHYS-v1; no analytic coverage assertion."""

from fractions import Fraction
from math import gcd

import pytest

from scripts.audit_mobius_type_ii import mobius


@pytest.mark.parametrize("e", [5, 7])
def test_literal_physical_witness_uses_original_h_delta_shells(e):
    T, q0, Q, n, u = 64, 1, 6007, 30011, 850
    N = T**3
    R = S = N // 8
    Kz = Mz = 8
    H = L = 4096
    s, h, delta = e * Q, e * u, e * u
    assert R / 2 <= n <= 2 * R and S / 2 <= s <= 2 * S
    assert H <= h <= 2 * H and L <= delta <= 2 * L
    assert q0 * max(n, s) <= N / 2
    assert Kz * Mz <= T and Fraction(Kz * S, Mz * R) == 1
    assert gcd(n, q0 * s) == gcd(e, q0 * Q) == gcd(u * u, Q) == 1
    assert mobius(Q) and mobius(n) and mobius(e)
    assert gcd(h * delta, s) == e
    assert Kz / 2 <= Fraction(Mz * n + delta, s) <= 2 * Kz
    original = Fraction(-h * delta * pow(n, -1, s), s) % 1
    reduced = Fraction(-e * u * u * pow(n, -1, Q), Q) % 1
    assert original == reduced
    assert mobius(n) * mobius(s) == mobius(Q) * mobius(e) * mobius(n)


@pytest.mark.parametrize("q0,Q,e", [(1, 5, 6), (2, 5, 21), (1, 6, 35), (3, 10, 7)])
@pytest.mark.parametrize("k", [0, 1, 2])
def test_fp7_matches_exact_residue_coefficients_with_all_masks(q0, Q, e, k):
    # Compare coefficient vectors before evaluating any roots of unity.
    # A coupled rational weight prevents testing only a separated toy constant.
    cap, u, v = 67, 3, -2

    def weight(n):
        return Fraction((n + e * u)**2 + e * v * n, 1 + n + e)

    direct = [Fraction(0) for _ in range(Q)]
    descended = [Fraction(0) for _ in range(Q)]
    for n in range(1, cap + 1):
        if gcd(n, q0 * e * Q) == 1:
            direct[-k * n % Q] += mobius(n) * weight(n)
    for f in range(1, e + 1):
        if e % f:
            continue
        for m in range(1, cap // f + 1):
            if gcd(m, f * q0 * Q) == 1:
                descended[-k * f * m % Q] += mobius(f)**2 * mobius(m) * weight(f * m)
    assert direct == descended


def test_genuine_gcd_and_type_frequency_gcd_are_different():
    reduced = [105 // d for d in (3, 5)]
    assert reduced == [35, 21]
    assert [gcd(Q, 15) for Q in reduced] == [5, 3]
    assert [gcd(1, Q) for Q in reduced] == [1, 1]
    assert [(-pow(dtf, -1, 5)) % 5 for dtf in (2, 3)] == [2, 3]


def test_positive_overlap_alone_is_not_the_genuine_mobius_layer():
    for divides_h in (0, 1):
        for divides_delta in (0, 1):
            lhs = -int(bool(divides_h or divides_delta))
            rhs = -divides_h - divides_delta + divides_h * divides_delta
            assert lhs == rhs
    assert mobius(5) == -1 != mobius(5)**2


def test_fixed_type_frequency_does_not_fix_collapsed_product_column():
    Q, k, u, v = 11, 2, 3, 1
    assert (-5 * u * v * k) % Q != (-7 * u * v * k) % Q
