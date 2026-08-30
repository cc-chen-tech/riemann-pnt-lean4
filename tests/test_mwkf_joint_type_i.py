"""JQ finite normalization/exponent guards; no analytic gate is certified."""

import cmath
from fractions import Fraction as F
from math import comb, pi, sin

import pytest

from scripts import mwkf_physical_type_ramanujan as pt
from scripts.mwkf_mobius_type_identity import divisors, mobius


def cubic(x):
    if not 1 < x < 2:
        return 0.0
    y = 4*(x-1)
    return 2/3*sum((-1)**j*comb(4, j)*max(y-j, 0)**3 for j in range(5))


def cubic_hat(xi):
    sinc = sin(pi*xi/4)/(pi*xi/4) if xi else 1
    return cmath.exp(-3j*pi*xi)*sinc**4


@pytest.mark.parametrize("K,D,B,Q,z0", [
    (F(5, 2), 17, 2, 3, F(7)), (F(7), 31, 5, 6, F(-11)),
    (F(4), 5, 3, 12, F(3, 2)), (F(3), 11, 1, 1, F(-5, 2)),
])
def test_joint_poisson_keeps_K_over_Bv_and_both_signed_frequency_axes(K, D, B, Q, z0):
    # Deliberately cancel the phase to get an exact known Fourier pair.
    # This C2 fixture does NOT certify the uniform smooth physical hypothesis.
    amplitude = lambda t, x: cubic(t)*cubic(x)*cmath.exp(-2j*pi*float(z0*t/x))
    dual_hat = lambda j, xi: cubic_hat(j*K)*cubic_hat(xi)
    jcut, ellcut = 40, 80
    result = pt.joint_type_i_unit_packet(K, D, B, Q, z0, amplitude, dual_hat, jcut, ellcut)
    assert result["direct"] == pytest.approx(result["divisor_sum"])
    # Independent product-tail majorant; zeta(4)<2, with all v|Q retained.
    tail = 0
    jtail = 2*(4/pi)**4/(3*float(K)**4*jcut**3)
    jtotal = 1+4*(4/(pi*float(K)))**4
    for v in divisors(Q):
        M = D/(B*v)
        ltail = 2*(4/pi)**4/(3*M**4*ellcut**3)
        ltotal = 1+4*(4/(pi*M))**4
        tail += abs(mobius(v))*float(K)/(B*v)*(jtail*ltotal+jtotal*ltail)
    assert abs(result["direct"]-result["dual_truncated"]) <= tail+2e-10
    assert result["dual_truncated"] == pytest.approx(result["zero_ell"]+result["nonzero_ell"])


def test_zero_ell_is_not_zero_j_or_a_discardable_mode():
    K, z0 = F(4), F(5)
    amplitude = lambda t, x: cubic(t)*cubic(x)*cmath.exp(-2j*pi*float(z0*t/x))
    result = pt.joint_type_i_unit_packet(
        K, 17, 2, 3, z0, amplitude, lambda j, xi: cubic_hat(j*K)*cubic_hat(xi), 12, 30)
    # sum_k cubic(k/4)=4, phi(3)/(2*3)=1/3, integral cubic=1.
    assert result["zero_ell"] == pytest.approx(F(4, 3))


def test_joint_finite_entry_keeps_literal_endpoints_and_unit_mask():
    # A finite discontinuous fixture only; no Poisson identity is asserted.
    result = pt.joint_type_i_unit_packet(1, 2, 1, 2, 0, lambda t, x: 1,
                                       lambda j, xi: 0, 1, 1)
    # kappa=1,2,3 and m=2,3,4; only m=3 is a unit. Each weighs 1/D.
    assert result["direct"] == F(3, 2)
    assert result["divisor_sum"] == F(3, 2)


def test_zero_ell_reassembles_every_j_not_only_j_zero():
    K, z0 = F(5, 2), F(-3)
    amplitude = lambda t, x: cubic(t)*cubic(x)*cmath.exp(-2j*pi*float(z0*t/x))
    result = pt.joint_type_i_unit_packet(
        K, 17, 2, 3, z0, amplitude, lambda j, xi: cubic_hat(j*K)*cubic_hat(xi), 80, 2)
    # kappa=3,4 give cubic samples 128/375 and 808/375; multiply by 1/3.
    assert result["zero_ell"] == pytest.approx(F(104, 125), abs=1e-8)
    assert abs(result["zero_ell"]-F(5, 6)) > 1e-3  # j=0 alone is K/3.


@pytest.mark.parametrize("s,rho,z,k,beta,eta,want", [
    (3, 0, 1, 1, 0, 0, (6, F(7, 2), 3, F(7, 2), 3)),
    (3, F(-1, 4), F(3, 4), F(3, 4), F(1, 4), 0,
     (F(23, 4), F(27, 8), 3, F(27, 8), 3)),
    (3, F(-1, 4), F(3, 4), F(3, 4), F(1, 4), 1,
     (F(19, 4), F(19, 8), 2, F(27, 8), 3)),
    (3, 0, 1, F(1, 4), 0, 0, (6, F(7, 2), F(15, 4), F(7, 2), F(15, 4))),
    (3, -1, 0, F(1, 2), 0, 0, (5, 2, F(3, 2), 2, F(3, 2))),
])
def test_exponent_ledger_counts_all_e_and_does_not_multiply_the_two_savings(s, rho, z, k, beta, eta, want):
    result = pt.joint_type_i_cost_exponents(s, rho, z, k, beta, eta)
    assert tuple(result[key] for key in ("density_shell", "stationary_one_e", "joint_one_e",
                                        "stationary_shell", "joint_shell")) == want
    assert result["best_alias_shell"] == min(want[-2:])
    # For z=0 the density is not rapidly small; this ledger never declares coverage.
    assert "covered" not in result


@pytest.mark.parametrize("callback", [
    lambda: pt.joint_type_i_unit_packet(0, 3, 1, 1, 2, lambda t, x: 0, lambda j, xi: 0, 1, 1),
    lambda: pt.joint_type_i_unit_packet(1, 3, 0, 1, 2, lambda t, x: 0, lambda j, xi: 0, 1, 1),
    lambda: pt.joint_type_i_unit_packet(1, 3, 1, 1, 2, lambda t, x: 0, lambda j, xi: 0, 0, 1),
    lambda: pt.joint_type_i_cost_exponents(3, 0, 1, 1, -1, 0),
    lambda: pt.joint_type_i_cost_exponents(3, 0, 1, 1, 0, 4),
])
def test_invalid_finite_contracts_are_rejected(callback):
    with pytest.raises(ValueError):
        callback()
