"""GU finite identities and physical exponent guards, not a full gate test."""

import cmath
from fractions import Fraction as F
from math import gcd, pi

import pytest

from scripts import mwkf_physical_type_ramanujan as pt
from scripts.mwkf_mobius_type_identity import divisors, mobius


def radical(n):
    value = 1
    for p in divisors(n):
        if p > 1 and len(divisors(p)) == 2:
            value *= p
    return value


@pytest.mark.parametrize("A,e,q,B", [
    (6, 5, 8, 7), (35, 6, 25, 11), (30, 7, 12, 11),
    (7, 1, 1, 6), (1, 6, 25, 7), (6, 2, 5, 7),
    (7, 3, 9, 2), (6, 5, 2, 10), (4, 3, 2, 5), (5, 4, 3, 7),
])
def test_general_unit_packet_keeps_shared_q_primes_and_literal_original_masks(A, e, q, B):
    ns, j, k, l = tuple(n for n in range(-9, 10) if n), -2, 3, -5
    weight = lambda a, n: complex(F(a+n, a+1), F(n*n, 17))
    row = pt.general_unit_type_ii_packet(A, e, q, B, j, k, l, ns, weight)
    modulus = radical(A*e*q)
    expected = 0j
    if gcd(e, A*q) == gcd(B, A*e*q) == 1:
        for v in divisors(A*e*q):
            if not mobius(v):
                continue
            for n in ns:
                if n % (modulus//v) == 0:
                    phase = F(n*A*k*l, j*B*modulus)
                    expected += F(mobius(e)**2*mobius(A)*mobius(v), B*v*abs(j))*weight(A, n)*cmath.exp(-2j*pi*float(phase))
    assert row["direct"] == pytest.approx(expected)
    assert row["collapsed"] == pytest.approx(expected)
    assert row["L"] == modulus
    assert all(n == (modulus//v)*ell for v, ell, n in row["lifted_labels"])
    if row["active"]:
        assert row["a"]*row["r"] == modulus
        assert gcd(row["a"], row["r"]*B) == 1


def test_general_density_sign_contains_the_e_mobius_factor():
    # A=6,e=5,q=8: g=2,a=3,r=10,L=30, mu(r/g)=-1.
    row = pt.general_unit_type_ii_packet(6, 5, 8, 7, 1, 2, 3, (1, 2, 3, 5, 6, 30), lambda a, n: 1)
    assert (row["g"], row["a"], row["r"], row["L"]) == (2, 3, 10, 30)
    assert row["coefficients"] == {1: F(-1, 210), 2: F(1, 210), 3: F(1, 105),
                                    5: F(2, 105), 6: F(-1, 105), 30: F(4, 105)}


def test_prime_powers_of_q_do_not_change_the_completed_modulus():
    args = (30, 7)
    ns = (-15, 1, 2, 5, 30)
    left = pt.general_unit_type_ii_packet(*args, 6, 11, 2, -1, 3, ns, lambda a, n: n)
    right = pt.general_unit_type_ii_packet(*args, 72, 11, 2, -1, 3, ns, lambda a, n: n)
    assert left["coefficients"] == right["coefficients"]
    assert left["collapsed"] == right["collapsed"]


@pytest.mark.parametrize("r,M", [(1, 0), (1, 17), (6, 6), (30, 41), (210, 13)])
def test_kappa_mass_uses_floor_counts_and_not_a_per_divisor_plus_one(r, M):
    row = pt.radical_kappa_mass(r, M)
    assert row["absolute_mass"] == sum(abs(sum(mobius(d)*d for d in divisors(gcd(r, n))))
                                       for n in range(1, M+1))
    assert row["gcd_floor_mass"] == sum(gcd(r, n) for n in range(1, M+1))
    assert row["absolute_mass"] <= row["gcd_floor_mass"] <= row["divisor_bound"]
    if (r, M) == (6, 6):
        assert tuple(row[key] for key in ("absolute_mass", "gcd_floor_mass", "divisor_bound")) == (8, 15, 24)


@pytest.mark.parametrize("eta,chi,beta,want", [
    (0, 0, F(2, 3), (3, 3, 3)),
    (F(1, 2), 0, F(1, 3), (3, F(5, 2), 3)),
    (F(1, 4), F(1, 2), F(1, 3), (3, F(11, 4), 3)),
    (1, 0, F(2, 3), (3, 3, 4)),
])
def test_entire_e_shell_cost_is_not_confused_with_one_e(eta, chi, beta, want):
    row = pt.general_unit_type_ii_exponents(3, 3, 0, 1, 1, beta, eta, chi)
    assert (row["density_all_e"], row["error_one_e"], row["error_e_shell"]) == want
    assert "covered" not in row


def test_missing_exact_resonance_does_not_imply_a_large_fourier_argument():
    row = pt.type_ii_n_frequency(101, 1011, 1, 10, -1)
    assert row == {"determinant": -1, "frequency": F(-1, 101), "coprime": True}
    # An exact resonance can exist if the unit mask is dropped.
    assert pt.type_ii_n_frequency(1011, 1011, 1, 10, -10)["determinant"] == 0


@pytest.mark.parametrize("call", [
    lambda: pt.general_unit_type_ii_packet(1, 0, 1, 1, 1, 1, 1, (1,), lambda a, n: 1),
    lambda: pt.general_unit_type_ii_packet(1, 1, 1, 1, 0, 1, 1, (1,), lambda a, n: 1),
    lambda: pt.general_unit_type_ii_packet(1, 1, 1, 1, 1, 1, 1, (0,), lambda a, n: 1),
    lambda: pt.general_unit_type_ii_packet(1, 1, 1, 1, 1, 1, 1, (1, 1), lambda a, n: 1),
    lambda: pt.radical_kappa_mass(4, 10),
    lambda: pt.radical_kappa_mass(2, -1),
    lambda: pt.general_unit_type_ii_exponents(3, 3, 0, 1, 1, -1, 0, 0),
    lambda: pt.type_ii_n_frequency(0, 1, 1, 1, 1),
])
def test_invalid_finite_domains_are_rejected(call):
    with pytest.raises(ValueError):
        call()
