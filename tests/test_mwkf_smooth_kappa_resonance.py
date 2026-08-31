"""Finite signed/endpoint guards for SK; not a coupled-kernel proof."""

import cmath
from fractions import Fraction as F
from itertools import product
from math import ceil, comb, floor, gcd, pi, sin

import pytest

from scripts import mwkf_physical_type_ramanujan as pt
from scripts.mwkf_mobius_type_identity import mobius


def compact_cubic(x):
    # Density of 1 plus four uniforms on [0,1/4]; C2, not a C-infinity claim.
    if not 1 < x < 2:
        return 0.0
    u = 4*(x-1)
    return 2/3*sum((-1)**j*comb(4, j)*max(u-j, 0)**3 for j in range(5))


def compact_cubic_hat(xi):
    sinc = sin(pi*xi/4)/(pi*xi/4) if xi else 1.0
    return cmath.exp(-3j*pi*xi)*sinc**4


@pytest.mark.parametrize("K,alpha", [
    (F(5, 2), F(3, 7)), (F(7), F(-5, 3)), (F(3), F(0)),
    (F(16), F(1, 5)), (F(31), F(9, 7)),
])
def test_smooth_kappa_poisson_sign_jacobian_and_explicit_tail(K, alpha):
    radius = 300
    actual = pt.smooth_kappa_packet(K, alpha, compact_cubic, compact_cubic_hat, radius)
    # |hat V(xi)| <= (4/(pi |xi|))^4, summing the omitted two tails.
    tail = 2*(4/pi)**4/(3*float(K)**3*(radius-1)**3)
    assert abs(actual["direct"]-actual["dual_truncated"]) <= tail+3e-11
    assert actual["dual_truncated"] == pytest.approx(actual["zero"]+actual["nonzero"])


def test_kappa_one_endpoint_is_not_lost_in_the_finite_support():
    actual = pt.smooth_kappa_packet(F(1, 2), F(1, 4), lambda t: 1, lambda t: 0, 2)
    # Only a finite support fixture: discontinuous profile does not assert Poisson.
    assert actual["samples"] == ((1, F(2)),)
    assert actual["direct"] == pytest.approx(1j)


@pytest.mark.parametrize("alpha", [F(2, 7), F(-8, 5), F(0)])
def test_integer_phase_shifts_change_j_labels_but_not_the_kappa_sum(alpha):
    a = pt.smooth_kappa_packet(5, alpha, compact_cubic, compact_cubic_hat, 50)
    b = pt.smooth_kappa_packet(5, alpha+3, compact_cubic, compact_cubic_hat, 50)
    assert a["direct"] == pytest.approx(b["direct"])
    assert a["dual_truncated"] == pytest.approx(b["dual_truncated"])


def direct_rows(As, ds, ks, ls, width, e=1, q=1):
    rows = []
    for A, d, k, l in product(As, ds, ks, ls):
        if gcd(e, A*q) != 1 or gcd(d, A*e*q) != 1:
            continue
        n = A*k*l
        for j in range(ceil(F(n-width)/d), floor(F(n+width)/d)+1):
            if j:
                rows.append((A, d, k, l, j, j*d-n))
    return tuple(sorted(rows))


def test_resonance_divisor_band_keeps_both_closed_endpoints_and_negative_products():
    rows = pt.kappa_resonance_band((2,), (5,), (1,), (3, -3), 1)
    assert rows == ((2, 5, 1, -3, -1, 1), (2, 5, 1, 3, 1, -1))


def test_zero_residual_can_survive_a_subunit_width():
    assert pt.kappa_resonance_band((2,), (5,), (1,), (5,), F(1, 3)) == (
        (2, 5, 1, 5, 2, 0),)


def test_n_plus_residual_zero_is_excluded_not_factored_as_an_integer():
    assert pt.kappa_resonance_band((1,), (5,), (1,), (1,), 1) == ()


@pytest.mark.parametrize("e,q,width", [
    (1, 1, 0), (1, 1, F(1, 2)), (1, 1, 3), (2, 3, 5), (3, 2, F(7, 2)),
])
def test_divisor_reassembly_equals_literal_shifted_equations(e, q, width):
    values = (range(1, 7), range(2, 12), (-2, 1, 3), (-2, 1, 4))
    assert pt.kappa_resonance_band(*values, width, e=e, q=q) == direct_rows(*values, width, e, q)


def test_coprimality_excludes_zero_residual_when_d_exceeds_the_dual_product():
    rows = pt.kappa_resonance_band(range(1, 9), range(10, 16), (1, 2), (-3, 1, 3), 20)
    assert rows and all(r != 0 for A, d, k, l, j, r in rows)


@pytest.mark.parametrize("cutoffs_a,cutoffs_d", [((1, 2), (1, 2)), ((2, 3), (4, 2)), ((20, 3), (20, 4))])
def test_all_nine_type_sectors_keep_signed_kernel_and_two_independent_cutoffs(cutoffs_a, cutoffs_d):
    rows = pt.kappa_resonance_band(range(1, 10), range(2, 14), (1, -2), (1, 3), F(5, 2), q=5)
    weight = lambda row: (1+2j)*(row[2]-row[3])+F(row[5], row[0]+row[1])
    actual = pt.kappa_resonance_type_totals(rows, weight, cutoffs_a, cutoffs_d)
    want = sum(mobius(A)*mobius(d)*weight((A, d, k, l, j, r))/d
               for A, d, k, l, j, r in rows)
    assert actual["direct"] == pytest.approx(want)
    assert sum(actual["sectors"].values()) == pytest.approx(want)
    assert len(actual["sectors"]) == 9


def test_type_weights_preserve_rational_arithmetic_and_small_endpoints():
    rows = ((1, 5, 1, 1, 1, 4), (2, 5, 1, 3, 1, -1))
    actual = pt.kappa_resonance_type_totals(rows, lambda row: F(row[5]), (1, 2), (2, 2))
    assert actual["direct"] == F(-1)
    assert sum(actual["sectors"].values()) == F(-1)
    assert any(key.startswith("small/") and value for key, value in actual["sectors"].items())


@pytest.mark.parametrize("K,e,want", [(10, 1, F(101000)), (100, 1, F(11000)), (10, 2, F(25500))])
def test_literal_physical_cost_includes_integer_boundary_and_not_an_extra_inverse_S(K, e, want):
    actual = pt.smooth_kappa_scales(1000, 1000, 100, 1000, K, e, 2, 5)
    assert actual["nonzero_bound_scale"] == want
    assert actual["Z"] == 10
    assert actual["nonzero_bound_scale"] == actual["C"]*K/actual["D"]*actual["X"]*10*(1+actual["D"]/K)


@pytest.mark.parametrize("callback", [
    lambda: pt.smooth_kappa_packet(0, 1, lambda t: 0, lambda t: 0, 2),
    lambda: pt.kappa_resonance_band((1,), (0,), (1,), (1,), 1),
    lambda: pt.kappa_resonance_band((1,), (2,), (0,), (1,), 1),
    lambda: pt.kappa_resonance_band((1,), (2,), (1,), (1,), -1),
    lambda: pt.kappa_resonance_type_totals((), lambda t: 0, (0, 2), (2, 2)),
    lambda: pt.smooth_kappa_scales(1, 2, 3, 4, 5, 6, 7, 8),
])
def test_invalid_finite_contract_is_rejected(callback):
    with pytest.raises(ValueError):
        callback()
