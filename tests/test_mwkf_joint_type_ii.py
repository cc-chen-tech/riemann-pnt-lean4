"""Finite JT checks: signs, lifted cutoffs, squarefree masks, and cost ledger.

These checks do not certify the continuous symbol bounds or the full gate.
"""

import cmath
from fractions import Fraction as F
from math import gcd, pi

import pytest

from scripts import mwkf_physical_type_ramanujan as pt
from scripts.mwkf_mobius_type_identity import c_u, divisors, mobius


def chi(t):
    # A piecewise polynomial algebra fixture, not the analytic C-infinity cutoff.
    return min(F(1), max(F(0), t-1))


@pytest.mark.parametrize("U,V,Q", [(1, 1, 1), (3, 2, 5), (4, 7, 6), (7, 1, 2)])
def test_smooth_type_ii_keeps_positive_boundary_and_nonsquarefree_quotients(U, V, Q):
    for n in range(1, 121):
        result = pt.type_ii_smooth_ledger(n, U, V, Q, chi)
        direct = -sum(c_u(a, U)*mobius(n//a) for a in divisors(n)
                      if a > U and n//a > V and gcd(n, Q) == 1)
        assert result["direct"] == direct
        assert result["bulk"]+result["boundary"] == direct


def test_smoothing_boundary_cannot_be_silently_deleted():
    result = pt.type_ii_smooth_ledger(6, 2, 1, 1, chi)
    # Only a=3,b=2 contributes to the sharp II sum: -c_2(3)*mu(2)=1.
    assert result["direct"] == 1
    assert result["bulk"] == F(1, 2)
    assert result["boundary"] == F(1, 2)
    nonsquarefree = pt.type_ii_smooth_ledger(8, 1, 1, 1, chi)
    assert (1, 2, 4, F(1)) in nonsquarefree["bulk_atoms"]


@pytest.mark.parametrize("t,x,eta,sigma", [
    (F(7, 5), F(3, 2), F(2, 3), F(-28, 45)),
    (F(3, 4), F(5, 4), F(3, 5), F(-9, 7)),
    (F(5, 2), F(7, 4), F(4, 5), F(3, 2)),
])
def test_rational_phase_normal_form_has_correct_jacobian_and_carrier(t, x, eta, sigma):
    row = pt.joint_type_ii_normal_coordinates(t, x, eta, sigma)
    assert row["phase"] == t/x-eta*t-sigma*x
    assert row["phase"] == -sigma/eta+row["y"]*row["w"]
    assert row["jacobian"] == x*x
    assert row["t_recovered"] == t
    assert row["x_recovered"] == x


@pytest.mark.parametrize("A,B,j,k,l", [(30, 7, 2, 3, -2), (1, 2, -3, -1, 4),
                                      (35, 6, 1, 2, 3), (12, 5, 2, 1, 1), (6, 9, 1, 1, -1)])
def test_all_v_reassembly_lifts_one_common_n_cutoff_and_retains_masks(A, B, j, k, l):
    ns = tuple(n for n in range(-15, 16) if n)
    amplitude = lambda a, n: complex(F(a+n, a+2), F(n*n+1, a+3))
    row = pt.joint_type_ii_divisor_packet(A, B, j, k, l, ns, amplitude)
    direct = 0j
    if gcd(A, B) == 1:
        for v in divisors(A):
            a0 = A//v
            for n in ns:
                if n % a0 == 0:
                    direct += F(mobius(A)*mobius(v), B*v*abs(j))*amplitude(A, n)*cmath.exp(
                        -2j*pi*float(F(n*k*l, j*B)))
    assert row["divisor_sum"] == pytest.approx(direct)
    assert row["collapsed_sum"] == pytest.approx(direct)
    assert all(n == (A//v)*ell for v, ell, n in row["lifted_labels"])
    if not mobius(A) or gcd(A, B) > 1:
        assert row["collapsed_sum"] == 0


def test_collapsed_coefficients_have_signed_gcd_factor_not_absolute_totient():
    row = pt.joint_type_ii_divisor_packet(30, 7, -2, 3, 1, (-6, 1, 5, 30), lambda a, n: 1)
    assert row["coefficients"] == {-6: F(1, 210), 1: F(1, 420),
                                    5: F(-1, 105), 30: F(-2, 105)}


@pytest.mark.parametrize("X,B,n", [(1, 1, 1), (F(5, 2), 6, -30), (11, 5, 210),
                                  (19, 6, 13), (4, 1, 97)])
def test_squarefree_mean_expansion_keeps_large_divisor_and_unit_conditions(X, B, n):
    # Last case includes d=97>2X: it contributes to the density, not the finite sum.
    profile = lambda x: (x-1)*(2-x) if 1 <= x <= 2 else F(0)
    row = pt.type_ii_squarefree_mean_ledger(X, B, n, profile)
    direct = sum(F(mobius(A)**2, A)*sum(mobius(d)*d for d in divisors(gcd(A, abs(n))))
                 *profile(F(A)/X) for A in range(1, int(2*X)+1) if gcd(A, B) == 1)
    assert row["direct"] == direct
    assert row["divisor_expansion"] == direct


@pytest.mark.parametrize("B,n,want", [(1, 1, F(1)), (1, -6, F(1, 12)),
                                     (6, 30, F(1, 12)), (12, 7, F(1, 16)),
                                     (5, 125, F(5, 6))])
def test_density_euler_factor_keeps_prime_support_not_prime_multiplicity(B, n, want):
    assert pt.type_ii_density_factor(B, n) == want
    # Independent squarefree inclusion sum for c(Bd)/c(1).
    inclusion = F(0)
    for d in divisors(abs(n)):
        if gcd(d, B) == 1:
            primes = [p for p in divisors(B*d) if p > 1 and len(divisors(p)) == 2]
            value = F(mobius(d))
            for p in primes:
                value *= F(p, p+1)
            inclusion += value
    assert inclusion == want


@pytest.mark.parametrize("p,nu,omega,u,want", [
    (F(1, 4), F(1, 4), F(39, 20), F(4, 5), (F(4, 5), F(1, 8), F(117, 40))),
    (1, 1, F(1, 2), F(3, 2), (F(3, 2), F(1, 4), F(17, 4))),
])
def test_type_ii_row_ledger_pays_every_v_in_the_shell(p, nu, omega, u, want):
    row = pt.type_ii_linear_row_exponents(p, nu, omega, u)
    assert (row["row_length"], row["saving"], row["cost"]) == want
    assert "covered" not in row


@pytest.mark.parametrize("call", [
    lambda: pt.type_ii_smooth_ledger(1, 0, 1, 1, chi),
    lambda: pt.joint_type_ii_normal_coordinates(1, 0, 1, -1),
    lambda: pt.joint_type_ii_divisor_packet(3, 1, 0, 1, 1, (1,), lambda a, n: 1),
    lambda: pt.joint_type_ii_divisor_packet(3, 1, 1, 1, 1, (0,), lambda a, n: 1),
    lambda: pt.joint_type_ii_divisor_packet(3, 1, 1, 1, 1, (1, 1), lambda a, n: 1),
    lambda: pt.type_ii_squarefree_mean_ledger(0, 1, 1, lambda x: x),
    lambda: pt.type_ii_density_factor(1, 0),
    lambda: pt.type_ii_linear_row_exponents(1, 1, 1, 1),
])
def test_invalid_finite_domains_are_rejected(call):
    with pytest.raises(ValueError):
        call()
