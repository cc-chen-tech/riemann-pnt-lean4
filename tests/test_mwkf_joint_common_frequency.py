"""Finite checks, not a proof of the physical coupled-kernel estimate."""

from cmath import exp
from fractions import Fraction as F
from math import gcd, pi, sqrt

import numpy as np
import pytest

from scripts import mwkf_common_phase_adapter as common
from scripts.mwkf_mobius_type_identity import mobius


def kernel(g, a, b, shift):
    function = getattr(common, "joint_common_frequency_kernel", None)
    assert callable(function), "joint all/zero/nonzero common kernel is missing"
    return function(common_modulus=g, left_phase=a, right_phase=b, shift=shift)


@pytest.mark.parametrize("g,shift", [(2, 1), (3, 1), (5, 0), (5, 2),
                                     (6, 1), (6, 2), (15, 3), (15, 4)])
def test_common_fourier_reassembly_retains_zero_and_unit_holes(g, shift):
    result = kernel(g, 1, -1, shift)
    full, zero, nonzero = map(np.array, (result.full, result.zero, result.nonzero))
    assert np.allclose(full, zero + nonzero, atol=2e-13)
    for i, z in enumerate(result.units):
        for j, w in enumerate(result.units):
            expected = (exp(2j * pi * ((pow(z, -1, g) + pow(w, -1, g)) % g) / g)
                        if (z - w - shift) % g == 0 else 0)
            assert abs(full[i, j] - expected) < 2e-13
    assert np.linalg.norm(nonzero, 2) <= 1 + 2e-13


def test_empty_even_unit_shift_has_nonzero_zero_and_complement_that_cancel():
    result = kernel(2, 1, 1, 1)
    assert result.full == ((0j,),)
    assert result.zero == ((0.5 + 0j,),)
    assert abs(result.nonzero[0][0] + 0.5) < 1e-14


@pytest.mark.parametrize("g", [3, 5, 7, 11, 17])
@pytest.mark.parametrize("a,b", [(1, 1), (2, -1)])
def test_nonzero_frequency_singular_values_do_not_give_a_generic_power(g, a, b):
    result = kernel(g, a, b, 2)
    singular = np.linalg.svd(np.array(result.nonzero), compute_uv=False)
    expected = sorted([1.] * (g - 3)
                      + [(sqrt(1 + 4 * g) + 1) / (2 * g),
                         (sqrt(1 + 4 * g) - 1) / (2 * g)], reverse=True)
    assert np.allclose(singular, expected, atol=3e-13)


@pytest.mark.parametrize("g", [7, 11, 17, 23])
def test_deleting_both_common_principal_characters_still_has_norm_one(g):
    result = kernel(g, 2, -1, 3)
    projection = np.eye(g - 1) - np.ones((g - 1, g - 1)) / (g - 1)
    centered = projection @ np.array(result.nonzero) @ projection
    singular = np.linalg.svd(centered, compute_uv=False)
    assert np.allclose(singular[:g - 5], 1, atol=3e-13)


@pytest.mark.parametrize("gamma,exception,left,right,required,gain,covered", [
    (F(1), F(0), F(0), F(0), F(1, 4), F(1, 2), True),
    (F(1), F(0), F(1, 4), F(1, 4), F(1, 4), F(1, 4), True),
    (F(1), F(0), F(1, 4), F(1, 3), F(1, 4), F(5, 24), False),
    (F(1), F(0), F(1), F(1), F(1, 4), F(0), False),
    (F(1), F(1, 2), F(0), F(0), F(1, 4), F(1, 4), True),
    (F(1, 4), F(0), F(0), F(0), F(1, 4), F(1, 8), False),
    (F(0), F(0), F(0), F(0), F(0), F(0), True),
])
def test_common_support_coverage_keeps_exceptional_gcd_and_cardinality_cost(
    gamma, exception, left, right, required, gain, covered
):
    function = getattr(common, "common_character_support_polytope", None)
    assert callable(function), "common character support exponent audit is missing"
    result = function(common_exponent=gamma, exceptional_gcd_exponent=exception,
                      left_support_exponent=left, right_support_exponent=right,
                      required_linear_gain=required)
    assert result["additional_linear_gain"] == gain
    assert result["selected_sector_exponent_sufficient"] is covered
    assert result["nonzero_common_frequency_complement_included"]
    assert not result["unrestricted_common_character_family_covered"]
    assert not result["coupled_kernel_gate_closed"]


@pytest.mark.parametrize("key,value", [
    ("common_exponent", F(-1)),
    ("exceptional_gcd_exponent", F(2)),
    ("left_support_exponent", F(2)),
    ("right_support_exponent", F(-1)),
    ("required_linear_gain", F(-1)),
])
def test_common_support_audit_rejects_nonphysical_exponents(key, value):
    function = getattr(common, "common_character_support_polytope", None)
    assert callable(function)
    args = dict(common_exponent=F(1), exceptional_gcd_exponent=F(0),
                left_support_exponent=F(0), right_support_exponent=F(0),
                required_linear_gain=F(1, 4))
    args[key] = value
    with pytest.raises(ValueError):
        function(**args)


@pytest.mark.parametrize("g,a,b", [(1, 1, 1), (4, 1, 1), (6, 2, 1), (5, 1, 0)])
def test_joint_kernel_requires_squarefree_modulus_and_unit_phases(g, a, b):
    with pytest.raises(ValueError):
        kernel(g, a, b, 1)


def test_original_two_mobius_product_rows_match_joint_nonzero_kernel():
    g, p, q, determinant = 5, 7, 11, 2
    h_weights = {-2: F(1), 1: F(2), 3: F(-1)}
    delta_weights = {-1: F(1), 2: F(3)}
    left_type = {n: F(mobius(n)) for n in range(1, 9)}
    right_type = {n: F(mobius(n), n) for n in range(1, 10)}
    left_x = determinant * pow(q, -1, p) % p
    right_x = -determinant * pow(p, -1, q) % q
    roots = [exp(2j * pi * k / g) for k in range(g)]

    def evaluate(poly):
        return sum(float(value) * roots[k] for k, value in enumerate(poly))

    def profile(active, phase, frequency, coefficients, residue):
        return evaluate(common.common_frequency_profile(
            common_modulus=g, active_prime=active, phase_label=phase,
            frequency=frequency, h_weights=h_weights, delta_weights=delta_weights,
            type_weights=coefficients).centered[residue])

    frequency_sum = sum(
        profile(p, 3, nu, left_type, left_x)
        * profile(q, 2, nu, right_type, right_x).conjugate()
        * roots[nu * determinant * pow(p * q, -1, g) % g] / g
        for nu in range(1, g)
    )

    def unphased_row(active, coefficients, residue):
        return np.array([
            float(sum((hw * dw * weight
                       * (F(int((h * delta + residue * n) % active == 0))
                          - F(1, active - 1))
                       for h, hw in h_weights.items()
                       for delta, dw in delta_weights.items()
                       for n, weight in coefficients.items()
                       if gcd(h * delta * n, g * active) == 1
                       and (h * delta + active * z * n) % g == 0), F(0)))
            for z in range(1, g)
        ])

    left = unphased_row(p, left_type, left_x)
    right = unphased_row(q, right_type, right_x)
    result = kernel(g, 3 * pow(p * p, -1, g), 2 * pow(q * q, -1, g),
                    determinant * pow(p * q, -1, g))
    joint = left @ np.array(result.nonzero) @ right.conjugate()
    assert abs(frequency_sum - joint) < 1e-11
    assert abs(joint) > 1e-4

    # U=V=1: the small endpoint is n=1, I=-1 for n>1, and
    # II=mu(n)+1 for n>1. In particular squareful n cannot be deleted
    # from each Type block before their signed reassembly.
    def multiplier(n, block):
        if block == 0:
            return int(n == 1)
        if n == 1:
            return 0
        return -1 if block == 1 else 1 + mobius(n)

    left_blocks = [unphased_row(p, {n: F(multiplier(n, block))
                                   for n in left_type}, left_x)
                   for block in range(3)]
    right_blocks = [unphased_row(q, {n: F(multiplier(n, block), n)
                                    for n in right_type}, right_x)
                    for block in range(3)]
    nine_terms = [x @ np.array(result.nonzero) @ y.conjugate()
                  for x in left_blocks for y in right_blocks]
    assert abs(sum(nine_terms) - frequency_sum) < 1e-11
    assert sum(abs(term) for term in nine_terms) > abs(frequency_sum) + 1e-4


@pytest.mark.parametrize("g,generator", [(7, 3), (11, 2), (23, 5)])
def test_small_common_matrix_entries_do_not_imply_small_dense_norm(g, generator):
    result = kernel(g, 1, 2, 1)
    logs = {pow(generator, exponent, g): exponent for exponent in range(g - 1)}
    basis = np.array([[exp(2j * pi * index * logs[z] / (g - 1)) / sqrt(g - 1)
                       for index in range(g - 1)] for z in result.units])
    assert np.allclose(basis.conjugate().T @ basis, np.eye(g - 1), atol=1e-13)
    matrix = basis.T @ np.array(result.full) @ basis.conjugate()
    zero = basis.T @ np.array(result.zero) @ basis.conjugate()
    assert np.max(np.abs(matrix)) <= 4 * sqrt(g) / (g - 1) + 1e-13
    assert np.max(np.abs(zero)) <= 1 / (g - 1) + 1e-13
    assert abs(np.linalg.norm(matrix, 2) - 1) < 1e-13

    # Character pairing convention is a.T M conjugate(b), not a* M b.
    a = np.array([complex(index, 1 - index) for index in range(g - 1)])
    b = np.array([complex(2 - index, index / 2) for index in range(g - 1)])
    actual = (basis @ a).T @ np.array(result.full) @ (basis @ b).conjugate()
    assert abs(actual - a.T @ matrix @ b.conjugate()) < 1e-10
