"""Finite arithmetic guards, not a proof of the coupled-kernel estimate."""

import cmath
from fractions import Fraction as F
from math import gcd, lcm, pi

import pytest

from scripts import mwkf_physical_type_ramanujan as pt


def test_lcm_unit_density_diagonalizes_with_the_correct_totient_weights():
    value = pt.unit_density_squares((2, 3, 6), (F(1), F(2), F(-1)))
    assert value["quadratic"] == F(17, 6)
    assert value["squares"] == {1: F(9, 4), 2: F(1, 36), 3: F(1, 2), 6: F(1, 18)}
    assert value["square_sum"] == F(17, 6)


@pytest.mark.parametrize("moduli,coeff", [
    ((1, 1), (1, -1)), ((4, 8, 12), (F(1, 2), -2, 3)),
    ((6, 10, 15), (1+2j, 3-1j, -2j)), ((5, 5, 10), (1j, -1j, 2)),
])
def test_density_squares_equal_an_independent_complete_unit_average(moduli, coeff):
    period = lcm(*moduli)
    actual = pt.unit_density_squares(moduli, coeff)
    # Characterization catches omitted common primes and wrong conjugation.
    want = sum(abs(sum(c for d, c in zip(moduli, coeff) if gcd(a, d) == 1))**2
               for a in range(1, period+1))/period
    assert actual["quadratic"] == pytest.approx(want)
    assert actual["square_sum"] == pytest.approx(want)


def test_nonzero_unit_alias_is_not_the_zero_determinant_or_density_mode():
    actual = pt.unit_interval_ledger(6, 0, 6, F(1, 6))
    assert actual["direct"] == pytest.approx(1)
    assert actual["density"] == pytest.approx(0, abs=1e-14)
    assert actual["alias"] == pytest.approx(1)
    assert actual["divisor_sum"] == pytest.approx(1)


def test_unit_alias_is_signed_not_a_positive_remainder():
    actual = pt.unit_interval_ledger(2, 1, 2, 0)
    assert actual["direct"] == 0
    assert actual["density"] == F(1, 2)
    assert actual["alias"] == F(-1, 2)


def test_distinct_frequencies_can_cancel_despite_positive_resonant_mass():
    # X/d=1. A uniformly smooth phase in the second profile cancels
    # the first frequency. Resonant energy is not a lower bound.
    for u in (0.5, 0.75, 1.0, 1.5, 2.0):
        z1 = cmath.exp(2j*pi*u)
        z2 = -cmath.exp(-2j*pi*u)*cmath.exp(4j*pi*u)
        whole = pt.unit_density_squares((5, 5), (z1, z2))["square_sum"]
        res = sum(pt.unit_density_squares((5,), (z,))["square_sum"] for z in (z1, z2))
        assert whole == pytest.approx(0, abs=1e-25)
        assert res == pytest.approx(F(8, 5))


@pytest.mark.parametrize("Q,left,right,alpha", [
    (1, 2, 7, F(0)), (6, 0, 6, F(0)), (30, 1, 19, F(-2, 7)),
    (210, 3, 8, F(1, 100)), (12, 2, 21, F(7, 3)),
])
def test_unit_completion_retains_all_divisors_and_interval_endpoints(Q, left, right, alpha):
    actual = pt.unit_interval_ledger(Q, left, right, alpha)
    want = sum(cmath.exp(2j*pi*float(alpha*n)) for n in range(left+1, right+1)
               if gcd(n, Q) == 1)
    assert actual["direct"] == pytest.approx(want)
    assert actual["divisor_sum"] == pytest.approx(want)
    assert actual["direct"] == pytest.approx(actual["density"]+actual["alias"])
    assert abs(actual["alias"]) <= actual["variation_bound"]+1e-12


def test_kappa_product_collapse_sums_coefficients_before_squaring():
    records = [(5, 1, 2, 2, 1j), (5, 2, 2, 1, -1j),
               (7, 2, 1, -2, 3), (7, 1, 1, -4, -1)]
    assert pt.collapse_triple_rows(records) == {(5, 4): 0j, (7, -4): 2}


@pytest.mark.parametrize("M,D,want", [(1, 1, 1), (2, 2, 6), (2, 3, 6),
                                      (3, 3, 15), (2, 4, 10)])
def test_primitive_ratio_collision_count_has_literal_endpoint_values(M, D, want):
    assert pt.ratio_collision_count(M, D) == want


def test_ratio_collision_count_matches_unrestricted_four_integer_condition():
    for M in range(1, 8):
        for D in range(1, 8):
            rows = [(n, d) for n in range(M, 2*M) for d in range(D, 2*D)]
            want = sum(n*b == a*d for n, d in rows for a, b in rows)
            assert pt.ratio_collision_count(M, D) == want


@pytest.mark.parametrize("nu,res,density,aliases", [
    (0, F(4), F(11, 2), F(5)), (1, F(7, 2), F(11, 2), F(11, 2)),
    (2, F(3), F(11, 2), F(6)), (3, F(5, 2), F(11, 2), F(13, 2)),
])
def test_whole_kappa_block_cost_not_a_fixed_kappa_cost(nu, res, density, aliases):
    actual = pt.joint_gram_cost_exponents(3-nu, 3, 1+nu, 2)
    assert actual == {"resonant": res, "density": density, "aliases": aliases}


@pytest.mark.parametrize("callback", [
    lambda: pt.unit_density_squares((0,), (1,)),
    lambda: pt.unit_density_squares((2,), (1, 2)),
    lambda: pt.unit_interval_ledger(0, 0, 2, 0),
    lambda: pt.collapse_triple_rows([(3, 1, 0, 1, 1)]),
    lambda: pt.ratio_collision_count(0, 3),
    lambda: pt.joint_gram_cost_exponents(-1, 3, 1, 2),
])
def test_outside_the_finite_contract_is_rejected(callback):
    with pytest.raises(ValueError):
        callback()
