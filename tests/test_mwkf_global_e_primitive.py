"""Finite all-e/primitive-frequency guards; no analytic operator bound."""

import cmath
from fractions import Fraction as F
from math import gcd, pi

import pytest

from scripts import mwkf_physical_type_ramanujan as pt
from scripts.mwkf_mobius_type_identity import divisors, mobius


@pytest.mark.parametrize("n,Q", [(1, 6), (2, 3), (4, 3), (12, 5), (30, 7), (6, 3)])
def test_u_one_keeps_the_integer_endpoint_and_nonsquarefree_quotient(n, Q):
    row = pt.mobius_u_one_ledger(n, Q)
    assert row["bulk"] + row["endpoint"] == mobius(n)*(gcd(n, Q) == 1)
    assert row["endpoint"] == (n == 1)
    if n == 4:
        assert row["atoms"] == ((1, 4, -1), (2, 2, 1))
    if gcd(n, Q) > 1:
        assert row["atoms"] == ()


@pytest.mark.parametrize("M,B,j,k,l", [
    (6, 30, 1, 2, 3), (30, 42, -2, 3, -5), (7, 11, 1, -2, 3),
    (1, 6, -1, -3, -2), (6, 1, 2, 1, 3), (4, 6, 1, 2, 3), (6, 4, 1, 2, 3),
])
def test_global_e_packet_matches_original_allocation_and_primitive_residues(M, B, j, k, l):
    ns = tuple(n for n in range(-8, 9) if n)
    weight = lambda m, b, n: complex(F(m+n, b+1), F(n*n, 19))
    row = pt.global_e_primitive_packet(M, B, j, k, l, ns, weight)
    direct, primitive = 0j, 0j
    allocations = []
    # Deliberately enumerate every original e, rather than use gcd to obtain it.
    for e in range(1, min(M, B)+1):
        if M % e or B % e:
            continue
        A, b = M//e, B//e
        if not (mobius(A) and mobius(e) and mobius(b)) or gcd(e, A) != 1 or gcd(b, A*e) != 1:
            continue
        allocations.append((e, A, b))
        for v in divisors(A*e):
            for n in ns:
                if n % (A*e//v) == 0:
                    direct += F(mobius(A)*mobius(b)*mobius(v), e*b*v*abs(j))*weight(M, B, n)*cmath.exp(-2j*pi*float(F(n*k*l, j*e*b)))
    if mobius(M) and mobius(B):
        for u in range(M):
            if gcd(u, M) == 1:
                primitive += F(mobius(M)*mobius(B), M*B*abs(j))*sum(
                    weight(M, B, n)*cmath.exp(2j*pi*float(F(n*u, M)-F(n*k*l, j*B))) for n in ns)
    assert row["allocation"] == (allocations[0] if allocations else None)
    assert row["direct"] == pytest.approx(direct, abs=1e-10)
    assert row["fused"] == pytest.approx(direct, abs=1e-10)
    assert row["fused"] == pytest.approx(primitive, abs=1e-10)


def test_shared_M_B_primes_are_retained_with_the_B_mobius_sign():
    row = pt.global_e_primitive_packet(6, 30, 1, 2, 3, (1, 2, 3, 6), lambda m, b, n: 1)
    assert row["allocation"] == (6, 1, 5)
    assert row["coefficients"] == {1: F(-1, 180), 2: F(1, 180), 3: F(1, 90), 6: F(-1, 90)}


@pytest.mark.parametrize("M,j,kl", [(1, 1, 6), (6, 1, 10), (6, 2, 10), (30, -6, 35), (7, 3, -10), (10, -3, -21)])
def test_resonance_divisor_family_matches_exhaustive_B_and_unit_h(M, j, kl):
    row = pt.primitive_resonant_rows(M, j, kl, 250)
    expected = []
    for B in range(1, 251):
        if not mobius(B) or (M*kl) % (j*B):
            continue
        h = -(M*kl)//(j*B)
        if gcd(h, M) == 1:
            expected.append((B, h, gcd(M, B), B//row["M1"], mobius(M)*mobius(B)))
    assert row["rows"] == tuple(expected)
    assert len(row["rows"]) <= row["divisor_bound"] == len(divisors(abs(kl)))
    assert all(M % gcd(M, abs(j)) == 0 and (j*B) % M == 0 for B, *_ in row["rows"])


def test_shared_j_primes_do_not_force_M_to_divide_B():
    row = pt.primitive_resonant_rows(6, 2, 10, 100)
    assert (row["d"], row["M1"], row["j1"]) == (2, 3, 1)
    assert row["rows"] == ((6, -5, 6, 2, 1), (30, -1, 6, 10, -1))
    row = pt.primitive_resonant_rows(6, 2, 5, 100)
    assert row["rows"] == ((3, -5, 3, 1, -1), (15, -1, 3, 5, 1))


@pytest.mark.parametrize("M,B,j,kl,H", [(101, 1011, 1, 10, F(1, 100)), (6, 15, -2, 3, 2), (1, 2, 1, -1, F(3, 2)), (7, 1, 2, -3, 0)])
def test_primitive_band_keeps_near_resonance_and_all_finite_endpoints(M, B, j, kl, H):
    rows = pt.primitive_band_rows(M, B, j, kl, H)
    expected = tuple((h, j*B*h+M*kl, F(B*h, M)+F(kl, j))
                     for h in range(-200, 201)
                     if gcd(h, M) == 1 and abs(F(B*h, M)+F(kl, j)) <= H)
    assert rows == expected
    assert all(gcd(delta, M) == gcd(j*B, M) for h, delta, freq in rows)
    if M == 101:
        assert rows == ((-1, -1, F(-1, 101)),)


@pytest.mark.parametrize("call", [
    lambda: pt.mobius_u_one_ledger(0, 1),
    lambda: pt.global_e_primitive_packet(0, 1, 1, 1, 1, (1,), lambda *args: 1),
    lambda: pt.global_e_primitive_packet(1, 1, 0, 1, 1, (1,), lambda *args: 1),
    lambda: pt.global_e_primitive_packet(1, 1, 1, 1, 1, (0,), lambda *args: 1),
    lambda: pt.global_e_primitive_packet(1, 1, 1, 1, 1, (1, 1), lambda *args: 1),
    lambda: pt.primitive_resonant_rows(4, 1, 1, 10),
    lambda: pt.primitive_resonant_rows(2, 0, 1, 10),
    lambda: pt.primitive_band_rows(2, 1, 1, 1, -1),
])
def test_invalid_finite_domains_are_rejected(call):
    with pytest.raises(ValueError):
        call()
