"""Finite scale/boundary checks, never an analytic gate certificate."""

import cmath
import importlib
import importlib.util
import math
from fractions import Fraction as F

import pytest


def adapter():
    name = "scripts.mwkf_reciprocal_scale_adapter"
    assert importlib.util.find_spec(name) is not None, "physical reciprocal scale adapter missing"
    return importlib.import_module(name)


def test_unbalanced_scale_changes_jacobian_and_critical_cutoff_together():
    out = adapter().reciprocal_scales(100, 1000, 75, 1, 1, -1, 6)
    assert out["M"] == 750
    assert out["D"] == out["X"] == 1000
    assert out["ratio"] == 10
    assert out["mode_scale"] == F(4, 3)
    assert out["lambda"] == -F(3, 4)
    assert out["phase_numerator"] == 450
    assert out["poisson_prefactor"] == 750
    assert out["outer_per_mode"] == F(1, 100)
    # A/D < 1/2 but M/D >= 1/2: the old subcritical classification is wrong.
    assert F(75, 1000) < F(1, 2) <= out["M"] / out["D"]


def test_two_cofactors_and_phase_sign_survive_normalization():
    out = adapter().reciprocal_scales(60, 180, 15, 3, 2, 2, -5)
    assert out["M"] == 45
    assert out["D"] == 60
    assert out["X"] == 30
    assert out["lambda"] == F(3, 2)
    assert out["phase_numerator"] == 75
    assert out["poisson_prefactor"] == F(5, 4)
    assert out["outer_per_mode"] == F(1, 360)


@pytest.mark.parametrize("values", [(0, 10, 2, 1, 1, 0, 1),
                                     (10, 5, 2, 1, 1, 0, 1),
                                     (5, 10, 2, 0, 1, 0, 1),
                                     (5, 10, 2, 1, 0, 0, 1)])
def test_invalid_oriented_scales_are_rejected(values):
    with pytest.raises(ValueError):
        adapter().reciprocal_scales(*values)


def test_discrete_zero_width_support_requires_the_endpoint_term():
    out = adapter().complementary_interval_ledger(5, 1, 0, 30)
    assert out["pair_count"] == 3  # (n,c)=(5,6),(6,5),(10,3)
    assert out["weighted_count"] == F(7, 15)
    assert out["continuous_part"] == 0
    assert out["boundary_part"] == F(12, 5)


@pytest.mark.parametrize("D,r,M,Z", [(5, 1, 1, 30), (5, 2, 3, -17),
                                       (7, 3, 2, 0), (10, 2, 1, 2),
                                       (F(9, 2), 3, F(1, 2), 12)])
def test_boundary_ledger_matches_independent_finite_pair_enumeration(D, r, M, Z):
    out = adapter().complementary_interval_ledger(D, r, M, Z)
    pairs = [(n, c) for n in range(1, 40) for c in range(-50, 51)
             if D <= r*n <= 2*D and c != 0 and abs(r*n*c-Z) <= M]
    assert out["pair_count"] == len(pairs)
    assert out["weighted_count"] == sum((F(1, r*n) for n, _ in pairs), F(0))
    assert out["weighted_count"] <= out["continuous_part"] + out["boundary_part"]


def test_all_small_boundary_boxes_keep_the_zero_c_exclusion():
    function = adapter().complementary_interval_ledger
    for D in range(1, 9):
        for r in range(1, 5):
            for M in (0, 1, 3):
                for Z in range(-12, 13):
                    out = function(D, r, M, Z)
                    pairs = [(n, c) for n in range(1, 17) for c in range(-20, 21)
                             if D <= r*n <= 2*D and c != 0 and abs(r*n*c-Z) <= M]
                    assert out["pair_count"] == len(pairs)
                    assert out["weighted_count"] == sum((F(1, r*n) for n, _ in pairs), F(0))
                    assert out["weighted_count"] <= out["continuous_part"] + out["boundary_part"]


@pytest.mark.parametrize("u,a,want", [(F(1, 2), 0, F(3938033, 12500000)),
                                      (3, 0, F(23855533, 12500000)),
                                      (3, 5, F(86355533, 12500000))])
def test_cubic_window_margin_survives_the_corrected_scale(u, a, want):
    assert adapter().cubic_window_margin(u, a) == want


def test_mr_stt_window_hypotheses_are_not_extended_below_the_polytope():
    with pytest.raises(ValueError):
        adapter().cubic_window_margin(F(1, 4), 0)


@pytest.mark.parametrize("j_sign", [-1, 1])
def test_scaled_poisson_gaussian_checks_the_phase_and_jacobian(j_sign):
    # Fourier transform of exp(-pi*y*y) is itself; finite tails are <1e-30.
    out = adapter().reciprocal_scales(4, 12, 2, 1, 1, j_sign, 5)
    n = 13
    M = float(out["M"])
    direct = sum(math.exp(-math.pi*((n*c-10)/M)**2) for c in range(-20, 21)) / n
    modes = sum(math.exp(-math.pi*(j*M/n)**2) * cmath.exp(-2j*math.pi*j*10/n)
                for j in range(-40, 41)) * float(out["poisson_prefactor"]) / n**2
    assert direct == pytest.approx(modes.real, abs=2e-15)
    assert abs(modes.imag) < 2e-15
    # A single nonsymmetric mode detects the sign that the real total cannot.
    assert cmath.exp(2j*math.pi*float(out["phase_numerator"])/n) == pytest.approx(
        cmath.exp(-2j*math.pi*j_sign*10/n), abs=2e-15)
