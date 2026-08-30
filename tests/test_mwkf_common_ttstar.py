"""Catch lost intermediate units, mixed zero terms, and short-shift endpoints.

These are finite algebra checks, not a proof of a physical saving.
"""

from collections import Counter
from fractions import Fraction as F
from math import gcd, sqrt

import numpy as np
import pytest

from scripts import mwkf_common_phase_adapter as common
from scripts.mwkf_mobius_type_identity import mobius


def gram(g, a, b, left=1, right=-1):
    function = getattr(common, "common_frequency_gram_kernel", None)
    assert callable(function), "common-frequency TT* with unit holes is missing"
    return function(common_modulus=g, left_shift=a, right_shift=b,
                    left_phase=left, right_phase=right)


@pytest.mark.parametrize("g,a,b", [(2, 1, 1), (3, 1, 2), (5, 1, 2),
                                    (5, 0, 2), (6, 1, 2), (15, 3, 5),
                                    (21, 7, 7), (30, 1, 11)])
def test_all_four_gram_terms_match_independent_fourier_composition(g, a, b):
    result = gram(g, a, b)
    # Both edges have the SAME intermediate phase: it must cancel.
    first = common.joint_common_frequency_kernel(
        common_modulus=g, left_phase=1, right_phase=-1, shift=a)
    second = common.joint_common_frequency_kernel(
        common_modulus=g, left_phase=-1, right_phase=-1, shift=b)
    f1, z1, n1 = map(np.array, (first.full, first.zero, first.nonzero))
    f2, z2, n2 = map(np.array, (second.full, second.zero, second.nonzero))
    for name, expected in [
        ("full", f1 @ f2.conjugate().T),
        ("full_zero", f1 @ z2.conjugate().T),
        ("zero_full", z1 @ f2.conjugate().T),
        ("zero_zero", z1 @ z2.conjugate().T),
        ("nonzero", n1 @ n2.conjugate().T),
    ]:
        assert np.allclose(getattr(result, name), expected, atol=5e-13)


def test_intermediate_zero_cannot_be_replaced_by_a_unit_translation():
    result = gram(5, 1, 2)
    i, j = result.units.index(1), result.units.index(2)
    # z1-z2 = a-b, but the only intermediate w is zero.
    assert result.full[i][j] == 0
    assert abs(result.zero_zero[i][j]) == pytest.approx(4 / 25)
    assert abs(result.nonzero[i][j]) == pytest.approx(4 / 25)
    assert result.full_zero[i][j] == result.zero_full[i][j] == 0


def test_even_empty_edges_still_have_a_nonzero_complement_gram():
    result = gram(2, 1, 1, left=1, right=1)
    assert result.full == ((0j,),)
    assert result.nonzero == ((0.25 + 0j,),)


@pytest.mark.parametrize("p1,p2,q,g,d", [(11, 17, 3, 5, 1),
                                         (17, 11, 3, 7, -2),
                                         (11, 41, 5, 6, 1)])
def test_induced_determinant_replaces_the_common_and_active_shifts(p1, p2, q, g, d):
    j = (p2 - p1) // q
    assert p2 - p1 == j * q
    a, b = (d * pow(p * q, -1, g) % g for p in (p1, p2))
    result = gram(g, a, b)
    assert result.shift_difference == d * j * pow(p1 * p2, -1, g) % g
    assert d * pow(q, -1, p1) % p1 == d * j * pow(p2, -1, p1) % p1
    assert d * pow(q, -1, p2) % p2 == -d * j * pow(p1, -1, p2) % p2


@pytest.mark.parametrize("part", ["full", "zero", "nonzero"])
def test_centered_fiber_energy_keeps_offshift_density_and_complex_weights(part):
    function = getattr(common, "centered_common_fiber_energy", None)
    assert callable(function), "joint-frequency centered fiber energy is missing"
    rows = {11: (1+2j, -1j, 3, -2), 17: (-2j, 4, 1-1j, 3j),
            19: (2, -3j, 0, 1+1j)}
    weights = {11: -2+1j, 17: 3j, 19: 1-2j}
    result = function(common_modulus=5, short_prime=3, determinant=1,
                      profiles=rows, phases={11: 1, 17: 2, 19: 3},
                      weights=weights, part=part)
    assert result["direct_energy"] == pytest.approx(result["expanded_energy"], abs=1e-10)
    assert result["direct_energy"] == pytest.approx(
        result["diagonal"] + result["incident_offdiagonal"] - result["density"],
        abs=1e-10)
    assert set(result["nonzero_shifts"]) == {-2, 2}
    assert result["density"] > 1e-4
    assert not result["physical_saving_proved"]


@pytest.mark.parametrize("g,d,jmax", [(1, 1, 0), (1, -2, 7), (6, 2, 5),
                                      (30, 6, 31), (210, 15, 100), (35, 0, 9)])
def test_gcd_histogram_has_exact_divisor_floors_including_empty_interval(g, d, jmax):
    function = getattr(common, "induced_shift_gcd_histogram", None)
    assert callable(function), "induced gcd divisor ledger is missing"
    result = function(common_modulus=g, determinant=d, shift_cutoff=jmax)
    assert result["counts"] == dict(Counter(gcd(g, d*j) for j in range(1, jmax+1)))
    actual = sum(count * sqrt(divisor) for divisor, count in result["counts"].items())
    assert actual <= result["euler_upper_bound"] + 1e-10
    assert sum(result["counts"].values()) == jmax


@pytest.mark.parametrize("g,d,jmax", [(0, 1, 2), (4, 1, 2), (6, 1, -1)])
def test_gcd_ledger_rejects_invalid_modulus_or_cutoff(g, d, jmax):
    function = getattr(common, "induced_shift_gcd_histogram", None)
    assert callable(function)
    with pytest.raises(ValueError):
        function(common_modulus=g, determinant=d, shift_cutoff=jmax)


@pytest.mark.parametrize("g,left,right", [(4, 1, 1), (1, 1, 1), (6, 2, 1)])
def test_gram_requires_squarefree_common_modulus_and_unit_phases(g, left, right):
    with pytest.raises(ValueError):
        gram(g, 1, 2, left, right)


@pytest.mark.parametrize("g,a,b", [(7, 1, 2), (11, 2, 3), (17, 5, 8)])
def test_intermediate_unit_mask_does_not_create_a_dense_operator_saving(g, a, b):
    result = gram(g, a, b)
    singular = np.linalg.svd(np.array(result.nonzero), compute_uv=False)
    assert np.allclose(singular[:g-5], 1, atol=1e-12)
    assert singular[0] <= 1 + 1e-12


def test_actual_product_mobius_rows_keep_type_signs_and_zero_cross_terms():
    g, q, d = 5, 3, 1
    primes, units = (11, 17, 19), (1, 2, 3, 4)
    hweights, deltaweights = {-2: F(1), 1: F(2), 3: F(-1)}, {-1: F(1), 2: F(3)}

    def make_rows(coefficients):
        return {p: tuple(complex(sum((hw * dw * coefficient
                     * (F(int((q*h*delta+d*n) % p == 0)) - F(1, p-1))
                     for h, hw in hweights.items() for delta, dw in deltaweights.items()
                     for n, coefficient in coefficients.items()
                     if gcd(h*delta*n, g*p) == 1 and (h*delta+p*z*n) % g == 0), F(0)))
                     for z in units) for p in primes}

    rows = make_rows({n: F(mobius(n), n) for n in range(1, 12)})
    blocks = [make_rows({n: F(int(n == 1), n) for n in range(1, 12)}),
              make_rows({n: F(-int(n > 1), n) for n in range(1, 12)}),
              make_rows({n: F((1+mobius(n))*int(n > 1), n) for n in range(1, 12)})]
    for p in primes:
        assert np.allclose(sum(np.array(block[p]) for block in blocks), rows[p])

    def energy(profiles, part):
        return common.centered_common_fiber_energy(
            common_modulus=g, short_prime=q, determinant=d, profiles=profiles,
            phases={p: pow(p*p, -1, g) for p in primes},
            weights={p: complex(mobius(p), 1/p) for p in primes}, part=part)

    values = {part: energy(rows, part) for part in ("full", "zero", "nonzero")}
    for value in values.values():
        assert value["direct_energy"] == pytest.approx(value["expanded_energy"], abs=1e-10)
    assert abs(values["full"]["direct_energy"] - values["zero"]["direct_energy"]
               - values["nonzero"]["direct_energy"]) > 1e-4
    assert abs(values["nonzero"]["direct_energy"]
               - sum(energy(block, "nonzero")["direct_energy"] for block in blocks)) > 1e-4


def test_empty_fiber_support_has_no_spurious_density_or_shift():
    result = common.centered_common_fiber_energy(
        common_modulus=5, short_prime=3, determinant=1,
        profiles={}, phases={}, weights={}, part="nonzero")
    assert result["direct_energy"] == result["expanded_energy"] == 0
    assert result["nonzero_shifts"] == ()
