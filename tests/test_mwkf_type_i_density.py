"""Finite guards for Type-I density/aliases, not an analytic gate proof."""

import cmath
from fractions import Fraction as F
from math import comb, gcd, pi, sin

import pytest

from scripts import mwkf_physical_type_ramanujan as pt
from scripts.mwkf_mobius_type_identity import mobius


@pytest.mark.parametrize("n,U,V,Q,direct,completed,endpoint", [
    (1, 2, 3, 1, 0, -1, 1), (2, 2, 3, 1, 0, 1, -1),
    (6, 2, 2, 1, 1, 1, 0), (8, 2, 2, 1, 0, 0, 0),
    (6, 2, 2, 3, 0, 0, 0),
])
def test_exact_type_i_completion_keeps_the_small_endpoint(n, U, V, Q, direct, completed, endpoint):
    result = pt.type_i_quotient_ledger(n, U, V, Q)
    assert result["direct"] == direct
    assert result["completed"] == completed
    assert result["endpoint"] == endpoint
    assert result["completed"]+result["endpoint"] == direct


def test_type_i_identity_and_unit_masks_on_all_small_parents():
    for n in range(1, 61):
        for U, V, Q in ((2, 5, 1), (5, 3, 6), (8, 11, 10)):
            actual = pt.type_i_quotient_ledger(n, U, V, Q)
            assert actual["direct"] == actual["completed"]+actual["endpoint"]


def test_nonsquarefree_unsigned_quotient_is_not_filtered_out():
    result = pt.type_i_quotient_ledger(8, 2, 2, 1)
    assert (1, 1, 8, -1) in result["atoms"]
    assert (1, 2, 4, 1) in result["atoms"]
    assert result["completed"] == 0


def compact_cubic(x):
    if not 1 < x < 2:
        return 0.0
    y = 4*(x-1)
    return 2/3*sum((-1)**j*comb(4, j)*max(y-j, 0)**3 for j in range(5))


def compact_cubic_hat(xi):
    sinc = sin(pi*xi/4)/(pi*xi/4) if xi else 1.0
    return cmath.exp(-3j*pi*xi)*sinc**4


@pytest.mark.parametrize("B,Q,D,density", [
    (1, 1, 9, F(1)), (2, 3, 17, F(1, 3)), (3, 10, 19, F(2, 15)),
    (5, 6, 31, F(1, 15)), (3, 12, 5, F(1, 9)),
])
def test_unit_quotient_poisson_has_one_over_Bv_and_a_controlled_tail(B, Q, D, density):
    cutoff = 200
    actual = pt.type_i_unit_completion(B, Q, D, compact_cubic, compact_cubic_hat, cutoff)
    # Independent tail integral; the test profile is C2, not C-infinity.
    tail = sum(2/(3*cutoff**3*B*v)*(4*B*v/(pi*D))**4
               for v in range(1, Q+1) if Q % v == 0 and mobius(v))
    assert actual["density"] == pytest.approx(density)
    assert actual["direct"] == pytest.approx(actual["divisor_sum"])
    assert abs(actual["direct"]-actual["dual_truncated"]) <= tail+1e-11
    assert actual["dual_truncated"] == pytest.approx(actual["density"]+actual["aliases"])


def test_discrete_aliases_are_not_forced_zero_by_the_continuous_mean():
    actual = pt.type_i_unit_completion(3, 12, 5, compact_cubic, compact_cubic_hat, 300)
    # The only interior sample has m=2, excluded by (m,12)=1.
    assert actual["direct"] == 0
    assert actual["density"] == pytest.approx(F(1, 9))
    assert actual["aliases"] == pytest.approx(-F(1, 9), abs=2e-6)


def test_stationary_alias_support_preserves_sign_and_both_support_endpoints():
    # z=8,D=16,B=1. v=2 has ell=-1 at x=1; v=6 also has x=1 at ell=-3.
    result = pt.type_i_stationary_aliases(1, 6, 16, 8)
    assert result == ((2, -1, F(1)), (3, -1, F(3, 2)),
                      (6, -3, F(1)), (6, -2, F(3, 2)), (6, -1, F(3)))
    assert pt.type_i_stationary_aliases(1, 2, 16, 2) == ()
    assert pt.type_i_stationary_aliases(1, 1, 2, 8) == (
        (1, -4, F(1)), (1, -3, F(4, 3)), (1, -2, F(2)), (1, -1, F(4)))


@pytest.mark.parametrize("z", [F(7), F(-7), F(3, 2), F(-11, 3)])
def test_alias_stationary_points_solve_the_literal_phase_derivative(z):
    for B in (1, 2, 7):
        rows = pt.type_i_stationary_aliases(B, 30, 19, z)
        expected = tuple((v, ell, -z*B*v/(ell*19))
                         for v in (1, 2, 3, 5, 6, 10, 15, 30)
                         for ell in range(-100, 101) if ell*z < 0 and 1 <= -z*B*v/(ell*19) <= 4)
        assert rows == expected
        for v, ell, x_squared in rows:
            assert -z/x_squared-F(ell*19, B*v) == 0


def test_large_divisor_alias_fuses_the_existing_A_mobius_sign():
    A, B = 30, 7
    rows = pt.type_i_stationary_aliases(B, A, 630, 21)
    assert rows
    for v, ell, x_squared in rows:
        assert v >= F(630, 21*B)
        assert mobius(A)*mobius(v) == mobius(A//v)
        assert gcd(A//v, v) == 1


def test_type_i_BV_cost_keeps_the_whole_UV_and_physical_scale():
    scales = pt.smooth_kappa_scales(1000, 1000, 100, 1000, 10, 2, 2, 5)
    result = pt.type_i_density_cost(scales, 2, 3)
    assert result == {"density_scale": F(250000), "alias_scale": F(33000)}


@pytest.mark.parametrize("callback", [
    lambda: pt.type_i_quotient_ledger(3, 0, 1, 1),
    lambda: pt.type_i_unit_completion(0, 1, 2, lambda x: 0, lambda x: 0, 2),
    lambda: pt.type_i_stationary_aliases(1, 2, 3, 0),
    lambda: pt.type_i_density_cost({"D": 3, "Z": 2, "rho": 1}, 0, 2),
])
def test_invalid_finite_contracts_are_rejected(callback):
    with pytest.raises(ValueError):
        callback()
