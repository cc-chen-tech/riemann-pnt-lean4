"""General-q all-e finite signs and masks; no claim of a full operator bound."""

import cmath
from fractions import Fraction as F
from math import ceil, exp, gcd, lcm, pi

import pytest

from scripts import mwkf_physical_type_ramanujan as pt
from scripts.mwkf_mobius_type_identity import divisors, mobius


@pytest.mark.parametrize("M,B,q", [(6, 15, 4), (6, 35, 12), (35, 77, 12), (6, 30, 1), (6, 10, 9), (1, 7, 12), (4, 5, 3), (6, 4, 5)])
def test_packet_matches_original_allocation_with_all_q_shared_primes(M, B, q):
    ns = tuple(n for n in range(-12, 13) if n)
    j, k, l = -2, 3, -5
    weight = lambda m, b, n: complex(F(m, b+1)+n/7, n*n/23)
    row = pt.global_e_q_packet(M, B, q, j, k, l, ns, weight)
    expected = 0j
    allocations = []
    for e in range(1, min(M, B)+1):
        if M % e or B % e:
            continue
        A, b = M//e, B//e
        if not (mobius(A) and mobius(e) and mobius(b)) or gcd(e, A*q) != 1 or gcd(b, A*e*q) != 1:
            continue
        allocations.append((e, A, b))
        L = max(d for d in divisors(A*e*q) if mobius(d))
        for d in divisors(A*e*q):
            if not mobius(d):
                continue
            for n in ns:
                if n % (L//d) == 0:
                    expected += F(mobius(A)*mobius(b)*mobius(d), B*d*abs(j))*weight(M, B, F(n*M, L))*cmath.exp(-2j*pi*float(F(n*M*k*l, j*B*L)))
    assert row["allocation"] == (allocations[0] if allocations else None)
    assert row["direct"] == pytest.approx(expected, abs=1e-10)
    assert row["fused"] == pytest.approx(expected, abs=1e-10)


def test_mu_v_sign_and_fractional_common_frequency_are_retained():
    row = pt.global_e_q_packet(35, 77, 12, 1, 1, 1, (1, 2, 3, 6), lambda m, b, u: 1)
    assert (row["g"], row["v"], row["L"], row["allocation"]) == (1, 6, 210, (7, 5, 11))
    assert row["coefficients"] == {1: F(1, 16170), 2: F(-1, 16170), 3: F(-2, 16170), 6: F(2, 16170)}
    assert row["scaled_labels"] == ((1, F(1, 6)), (2, F(1, 3)), (3, F(1, 2)), (6, F(1)))
    odd_v = pt.global_e_q_packet(6, 5, 9, 1, 1, 1, (1,), lambda m, b, u: 1)
    # q0=3 divides M: v=1, not q0, so no spurious mu(3) sign.
    assert odd_v["coefficients"] == {1: F(-1, 30)}
    odd_v = pt.global_e_q_packet(7, 5, 9, 1, 1, 1, (1,), lambda m, b, u: 1)
    assert odd_v["coefficients"] == {1: F(1, 105)}


@pytest.mark.parametrize("q", [1, 2, 3, 4, 5, 12, 25, 30])
def test_q_resonance_keeps_exactly_the_B_and_h_units(q):
    row = pt.primitive_q_resonant_j_family(6, 10, 1, 14, 60, q)
    expected = []
    for j in range(1, 14):
        for B in range(1, 61):
            if not mobius(B) or 60 % (j*B):
                continue
            h = -60//(j*B)
            if gcd(B, q) == gcd(h, 6*q) == 1:
                d = gcd(j, 6)
                expected.append((j, B, h, d, j//d, B//(6//d), mobius(6)*mobius(B)))
    assert row["rows"] == tuple(expected)
    assert all(j % gcd(6, q) == 0 for j, *_ in row["rows"])
    assert len(row["rows"]) <= row["divisor_bound"] == 64


@pytest.mark.parametrize("M,B,q,J,j,kl", [(6, 5, 9, 1, 2, 7), (7, 5, 12, 2, 3, 5), (6, 5, 4, 3, -4, -7), (35, 77, 12, 2, 4, 3)])
def test_scaled_Fourier_identity_leaves_only_h_q_unit_mask(M, B, q, J, j, kl):
    q0 = max(d for d in divisors(q) if mobius(d))
    v, L = q0//gcd(M, q0), lcm(M, q0)
    N = ceil(8*B*J*v)
    ns = tuple(n for n in range(-N, N+1) if n)
    psi = lambda m, b, u: float(u/(B*J))**2*exp(-pi*float(u/(B*J))**2)
    row = pt.global_e_q_packet(M, B, q, j, 1, kl, ns, psi)
    hs = pt.primitive_band_rows(M, B, j, kl, F(8, J))
    rhs = F(J*mobius(M)*mobius(B), M*abs(j))*sum(
        (1/(2*pi)-float(J*freq)**2)*exp(-pi*float(J*freq)**2)
        for h, _, freq in hs if gcd(h, q0) == 1)
    assert row["L"] == L
    assert row["fused"] == pytest.approx(rhs, abs=2e-10)


@pytest.mark.parametrize("nu,a,beta,chi,want", [
    (1, F(1, 2), F(4, 5), F(1, 5), (F(33, 10), F(14, 5), 3, 3)),
    (1, 0, F(7, 6), F(1, 2), (4, 3, F(17, 6), 3)),
    (F(9, 10), F(1, 2), F(4, 5), 0, (F(33, 10), F(14, 5), 3, 3)),
    (1, F(1, 2), 1, 1, (4, F(7, 2), F(7, 2), F(7, 2))),
])
def test_complete_q0_cost_is_present_but_not_a_spurious_e_shell_count(nu, a, beta, chi, want):
    row = pt.all_e_q_error_exponents(nu, a, beta, chi)
    assert row["density"] == 3
    assert tuple(row[key] for key in ("uncompleted_error", "interval_error", "integer_error", "best_error")) == want
    assert "covered" not in row


@pytest.mark.parametrize("call", [
    lambda: pt.global_e_q_packet(6, 5, 0, 1, 1, 1, (1,), lambda *args: 1),
    lambda: pt.global_e_q_packet(6, 5, 4, 0, 1, 1, (1,), lambda *args: 1),
    lambda: pt.global_e_q_packet(6, 5, 4, 1, 1, 1, (0,), lambda *args: 1),
    lambda: pt.global_e_q_packet(6, 5, 4, 1, 1, 1, (1, 1), lambda *args: 1),
    lambda: pt.primitive_q_resonant_j_family(6, 10, 1, 14, 60, 0),
    lambda: pt.primitive_q_resonant_j_family(4, 10, 1, 14, 60, 3),
    lambda: pt.all_e_q_error_exponents(1, F(1, 2), 1, -1),
])
def test_invalid_finite_domains_are_rejected(call):
    with pytest.raises(ValueError):
        call()
