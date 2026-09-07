"""Finite guards for inverse-c Poisson, endpoint reassembly and power costs.

These tests do not prove a uniform analytic Mobius estimate or the gate.
"""

import cmath
from fractions import Fraction as F
from math import ceil, comb, floor, pi, sin

import pytest

from scripts import mwkf_physical_type_ramanujan as pt
from scripts.mwkf_mobius_type_identity import mobius


def _compact_cubic(x):
    """Density of 1 plus four independent uniforms on [0,1/4]."""
    if not 1 < x < 2:
        return 0.0
    u = 4*(x-1)
    return 2/3*sum((-1)**j*comb(4, j)*max(u-j, 0)**3 for j in range(5))


def _compact_cubic_hat(xi):
    sinc = sin(pi*xi/4)/(pi*xi/4) if xi else 1.0
    return cmath.exp(-3j*pi*xi)*sinc**4


@pytest.mark.parametrize("R,A,e,d,Z", [
    (9, 2, 1, 5, 6), (9, 2, 3, 5, -6), (3, 2, 3, 7, 0),
    (7, 3, 2, 5, 11), (1, 2, 1, 3, -1),
])
def test_inverse_c_has_positive_finite_support_and_correct_jacobian(R, A, e, d, Z):
    # A wrong Fourier sign or missing Ae/R fails the nonreal fixtures.
    actual = pt.inverse_c_lattice(R, A, e, d, Z, _compact_cubic)
    cutoff = 5000
    shift, spacing = Z/d, R/(A*e)
    frequency_sum = sum(_compact_cubic_hat(spacing*(c-shift))
                        for c in range(ceil(shift-cutoff), floor(shift+cutoff)+1))
    tail = 2*(4/(pi*spacing))**4/(3*(cutoff-1)**3)
    assert abs(actual["value"]-frequency_sum) <= tail+2e-12
    assert all(k >= 1 and 1 <= x <= 2 for k, x in actual["samples"])
    assert actual["jacobian"] == F(A*e, R)


def test_integer_endpoints_are_not_dropped_from_the_sample_ledger():
    # The profile is deliberately discontinuous: only the finite support
    # ledger is asserted here, not a Poisson identity for this profile.
    actual = pt.inverse_c_lattice(6, 2, 3, 5, 0, lambda x: 1)
    assert actual["samples"] == ((1, F(1)), (2, F(2)))
    assert actual["value"] == 2


@pytest.mark.parametrize("r,s,q,bulk,endpoint,residual,physical", [
    (1, 6, 5, 1, 1, 0, F(0)),
    (2, 3, 1, 0, -1, 1, F(1, 3)),
    (2, 3, 2, 0, 0, 0, F(0)),
    (4, 3, 1, 0, 0, 0, F(0)),
    (6, 6, 5, 0, 0, 0, F(0)),
    (6, 5, 7, 0, 1, -1, F(-1, 5)),
])
def test_signed_bulk_and_integer_one_endpoint(r, s, q, bulk, endpoint, residual, physical):
    actual = pt.inverse_c_allocation_ledger(r, s, q)
    assert actual["bulk"] == bulk
    assert actual["endpoint"] == endpoint
    assert actual["residual"] == residual
    assert actual["physical_coefficient"] == physical


def test_cutting_the_kappa_one_block_destroys_exact_bulk_cancellation():
    actual = pt.inverse_c_allocation_ledger(2, 6, 5)
    # Tuples are (e,A,kappa,weight). Neither a positive row nor one block
    # represents the fully reassembled original coefficient.
    assert actual["terms"] == ((1, 1, 2, 1), (2, 1, 1, -1))
    assert sum(w for e, A, k, w in actual["terms"] if k > 1) == 1
    assert actual["bulk"] == 0


def test_full_finite_roundtrip_keeps_q_gcd_and_nonsquarefree_cancellation():
    # Independent original coefficient, not the allocation formula.
    from math import gcd
    for s in (1, 2, 3, 6, 10, 15):
        for q in (1, 7, 11):
            for r in range(1, 85):
                actual = pt.inverse_c_allocation_ledger(r, s, q)
                want = F(mobius(s), s)*(mobius(r)*int(gcd(r, s*q) == 1)-int(r == 1))
                assert actual["physical_coefficient"] == want


@pytest.mark.parametrize("X,Z,t,sign,denominator", [
    (1000, 10, 1, 1, 100), (1000, 10, 6, -1, 17),
    (25, 2, 1, 1, 13), (100, 25, 2, 1, 2),
])
def test_nearest_reciprocal_is_a_reduced_admissible_approximation(X, Z, t, sign, denominator):
    actual = pt.nearest_reciprocal_approximation(X, Z, t, sign)
    assert actual["denominator"] == denominator
    assert actual["approximant"] == F(sign, denominator)
    assert abs(actual["alpha"]-actual["approximant"]) <= F(1, denominator**2)


@pytest.mark.parametrize("x,z,saving", [
    (3, 1, F(1, 2)), (3, F(3, 5), F(3, 10)),
    (3, F(5, 2), F(1, 4)), (2, 0, F(0)),
    (3, F(3, 2), F(3, 5)),
])
def test_row_exponents_sum_smooth_divisors_with_their_actual_weights(x, z, saving):
    assert pt.small_linear_row_saving(x, z) == saving


def test_single_row_gain_does_not_cover_the_physical_balanced_packet():
    saving = pt.small_linear_row_saving(3, 1)
    # HL/R * #(k,l) * R = S^2; the desired physical target is S.
    assert 2*3-saving == F(11, 2)
    assert 2*3-saving-3 == F(5, 2)


@pytest.mark.parametrize("callback", [
    lambda: pt.inverse_c_lattice(0, 1, 1, 1, 0, lambda x: 1),
    lambda: pt.inverse_c_allocation_ledger(2, 4, 1),
    lambda: pt.inverse_c_allocation_ledger(2, 6, 3),
    lambda: pt.nearest_reciprocal_approximation(10, 4, 2),
    lambda: pt.small_linear_row_saving(3, 3),
])
def test_outside_the_stated_finite_contract_is_rejected(callback):
    with pytest.raises(ValueError):
        callback()
