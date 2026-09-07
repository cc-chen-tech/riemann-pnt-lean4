"""Finite phase and axis checks, not proofs of continuous Poisson or a saving."""

import cmath
import importlib
import importlib.util
from fractions import Fraction as F
from math import gcd, pi

import pytest


def adapter():
    name = "scripts.mwkf_shifted_frequency_adapter"
    assert importlib.util.find_spec(name) is not None, "missing finite frequency adapter"
    return importlib.import_module(name)


def e(x):
    return cmath.exp(2j * pi * float(x % 1))


@pytest.mark.parametrize("r,s", [(5, 2), (2, 5), (8, 3), (3, 8), (2, 1), (1, 2), (1, 6)])
def test_signed_completion_matches_direct_gauss_sum_including_unit_modulus(r, s):
    # Changing b to abs(b) in either phase fails the negative-b fixtures.
    b, m = r-s, abs(r-s)
    beta = pow(s, -1, m) if m > 1 else 0
    for nu, omega in [(-3, 2), (0, 0), (2, -5), (1, 1)]:
        row = adapter().completion_frequency_transport(r, s, nu, omega)
        direct = sum(e(F(beta*a*c, b)+F(nu*a+omega*c, m))
                     for a in range(m) for c in range(m))
        assert direct == pytest.approx(m*e(row["gauss_phase"]), abs=1e-10)
        assert row["jacobian"] == s*m
        assert row["combined_constant_phase"] == 0
        assert row["shift"] == (-nu if b > 0 else nu)
        assert row["lattice_frequency"] == (omega if b > 0 else -omega)


@pytest.mark.parametrize("r,s", [(5, 2), (2, 5), (2, 1), (1, 2), (1, 6)])
def test_reciprocity_preserves_original_h_delta_phase(r, s):
    row = adapter().completion_frequency_transport(r, s, 1, -2)
    inverse = pow(r, -1, s) if s > 1 else 0
    for h, delta in [(-5, 3), (0, 7), (2, -4), (1, 1)]:
        original = F(-h*delta*inverse, s) % 1
        split = (F(row["beta"]*h*delta, r-s)-F(h*delta, (r-s)*s)) % 1
        assert original == split


@pytest.mark.parametrize("r,s", [(5, 2), (2, 5), (2, 1), (1, 2), (8, 3)])
def test_finite_completion_retains_both_deleted_axes_and_the_origin(r, s):
    # Omitting +origin, or folding a literal zero axis into residue-zero, fails.
    weights = {(0, 0): 2-3j, (0, 2): -7, (3, 0): 5j,
               (-2, 1): F(3, 2), (4, -3): -2+1j, (3, 3): 11}
    row = adapter().finite_completion_axis_sides(r, s, weights)
    b, m = r-s, abs(r-s)
    beta = pow(s, -1, m) if m > 1 else 0
    direct = sum(value*e(F(beta*h*delta, b))
                 for (h, delta), value in weights.items() if h and delta)
    assert row["h_axis"] == -5-3j
    assert row["delta_axis"] == 2+2j
    assert row["origin"] == 2-3j
    assert row["nonaxes_direct"] == pytest.approx(direct, abs=1e-10)
    assert row["nonaxes_completed"] == pytest.approx(direct, abs=1e-10)
    assert row["completed"] == pytest.approx(row["direct"], abs=1e-10)


def test_finite_lattice_equal_zeta_and_original_afe_diagonal_are_distinct():
    # (n,m1)=(2,3) is AFE-diagonal for r=3,s=2, but is not equal-zeta.
    weights = {(1, 1): F(2), (2, 2): F(5), (2, 3): F(7), (3, 1): F(11)}
    row = adapter().integer_shift_axis_partition(3, 2, weights)
    assert row["shift_sums"] == {0: 7, 1: 7, -2: 11}
    assert row["equal_zeta"] == 7
    assert row["afe_diagonal"] == 7
    assert row["axis_intersection"] == 0
    assert row["off_both_axes"] == 11
    # Equal diagonal totals above do not imply equal axes.
    assert row["afe_points"] == ((2, 3),)
    assert row["equal_zeta_points"] == ((1, 1), (2, 2))


def test_equal_mollifier_indices_use_r_s_one_without_dividing_by_zero():
    row = adapter().integer_shift_axis_partition(1, 1, {(1, 1): 3, (1, 2): 7})
    assert row["afe_diagonal"] == row["equal_zeta"] == row["axis_intersection"] == 3
    assert row["off_both_axes"] == 7
    assert row["full"] == sum(row["shift_sums"].values()) == 10


@pytest.mark.parametrize("r,s", [(0, 1), (2, 2), (4, 2), (F(3, 2), 1), (True, 2)])
def test_invalid_short_modulus_is_rejected(r, s):
    with pytest.raises(ValueError):
        adapter().completion_frequency_transport(r, s, 0, 0)


def test_physical_lattice_rejects_nonpositive_zeta_variables():
    with pytest.raises(ValueError):
        adapter().integer_shift_axis_partition(3, 2, {(0, 1): 1})


def test_all_small_coprime_lattices_keep_exact_axis_inclusion_exclusion():
    weights = {(n, m): F(n+2*m, n*m) for n in range(1, 6) for m in range(1, 6)}
    for r in range(1, 6):
        for s in range(1, 6):
            if gcd(r, s) != 1:
                continue
            row = adapter().integer_shift_axis_partition(r, s, weights)
            assert row["full"] == (row["off_both_axes"]+row["afe_diagonal"]
                                   +row["equal_zeta"]-row["axis_intersection"])
            assert row["full"] == sum(row["shift_sums"].values())
