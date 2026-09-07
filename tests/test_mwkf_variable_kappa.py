"""Finite GP scale/sign/endpoint guards, not a proof of the analytic gate."""

import cmath
from fractions import Fraction as F
from math import ceil, exp, gcd, pi

import pytest

from scripts import mwkf_physical_type_ramanujan as pt
from scripts.mwkf_mobius_type_identity import divisors, mobius


@pytest.mark.parametrize("M,want", [
    (256, (8, 1, -1)), (384, (12, F(2, 3), F(-4, 9))),
])
def test_normal_coordinates_keep_both_compact_scale_ratios(M, want):
    row = pt.variable_kappa_parameters(512, 2, 8, M, 3, -12, 4, 8)
    assert (row["X"], row["J"], row["n_scale"]) == (256, 4, 12)
    assert tuple(row[key] for key in ("z0", "eta", "sigma")) == want
    assert row["eta"] == F(4, row["J"])*F(row["X"], M)
    assert row["sigma"] == -F(row["X"], M)**2


def test_signed_parameters_do_not_insert_critical_support_or_absorb_product_ratio():
    row = pt.variable_kappa_parameters(512, 2, 8, 256, 3, 12, -4, -16)
    assert (row["z0"], row["eta"], row["sigma"]) == (-16, F(1, 2), F(-1, 2))
    outside = pt.variable_kappa_parameters(512, 2, 8, 256, 3, 12, 4, -16)
    assert outside["eta"] < 0
    assert "critical" not in outside


@pytest.mark.parametrize("nu,a,beta,want", [
    (F(9, 10), F(1, 2), F(4, 5), (F(33, 10), F(14, 5), 3, 3)),
    (F(4, 5), 0, F(6, 5), (4, 3, F(14, 5), 3)),
    (F(3, 5), F(1, 2), F(2, 5), (3, F(5, 2), F(31, 10), 3)),
    (1, F(1, 2), 3, (F(13, 2), 6, 4, 6)),
    (F(1, 5), F(1, 2), F(1, 5), (F(31, 10), F(13, 5), F(17, 5), F(31, 10))),
])
def test_entire_frequency_mass_and_best_error_are_charged(nu, a, beta, want):
    row = pt.variable_kappa_error_exponents(nu, a, beta)
    assert row["density"] == 3
    assert tuple(row[key] for key in ("uncompleted_error", "interval_error", "integer_error", "best_error")) == want
    assert "covered" not in row


@pytest.mark.parametrize("a,beta", [(0, F(4, 3)), (F(1, 4), F(7, 6)), (F(1, 2), 1)])
def test_top_kappa_face_recovers_the_existing_slope_ledger(a, beta):
    row = pt.variable_kappa_error_exponents(1, a, beta)
    assert {key: row[key] for key in pt.global_slope_error_exponents(a, beta)} == pt.global_slope_error_exponents(a, beta)


@pytest.mark.parametrize("scale", [2, 7, 31])
def test_B_sampling_depends_on_n_over_j_not_the_length_of_the_j_family(scale):
    for n, j in [(15, 2), (-15, -2), (-15, 2)]:
        assert pt.slope_b_sampling(8, scale*n, 3, scale*j, 11, F(3, 2)) == pt.slope_b_sampling(8, n, 3, j, 11, F(3, 2))


@pytest.mark.parametrize("M,kl,lo,hi,Bmax", [
    (6, 10, 2, 5, 100), (6, -10, 2, 5, 100),
    (30, 35, 1, 30, 250), (7, -12, 3, 21, 250),
    (1, 12, 1, 15, 50), (6, 10, 2, 5, 0),
    (6, 10, 2, 3, 6), (6, 10, 3, 4, 100),
])
def test_joint_j_resonance_divisor_family_matches_exhaustive_integer_equation(M, kl, lo, hi, Bmax):
    row = pt.primitive_resonant_j_family(M, kl, lo, hi, Bmax)
    expected = []
    for abs_j in range(lo, hi):
        j = abs_j if kl > 0 else -abs_j
        d = gcd(abs_j, M)
        for B in range(1, Bmax+1):
            if not mobius(B) or (M*kl) % (j*B):
                continue
            h = -(M*kl)//(j*B)
            if gcd(h, M) == 1:
                expected.append((j, B, h, d, j//d, B//(M//d), mobius(M)*mobius(B)))
    assert row["rows"] == tuple(sorted(expected))
    assert len(row["rows"]) <= row["divisor_bound"] == len(divisors(M))*len(divisors(abs(kl)))**2


def test_shared_j_primes_and_two_different_j_resonances_are_not_erased():
    row = pt.primitive_resonant_j_family(6, 10, 2, 5, 100)
    assert row["rows"] == (
        (2, 6, -5, 2, 1, 2, 1), (2, 30, -1, 2, 1, 10, -1),
        (4, 3, -5, 2, 2, 1, -1), (4, 15, -1, 2, 2, 5, 1),
    )


@pytest.mark.parametrize("M,B,j,kl", [(1, 3, 2, 1), (6, 3, 4, 10), (7, 2, -3, -5), (10, 6, 5, 3)])
@pytest.mark.parametrize("J", [1, 2, 4])
def test_primitive_fourier_J_jacobian_with_a_schwartz_zero_at_origin(M, B, j, kl, J):
    # Numerical identity check with Psi(x)=x^2 exp(-pi*x^2), not the physical
    # compact symbol or a tail proof. A missing J on the right fails this test.
    scales = pt.variable_kappa_parameters(512, 2, 2*J, 256, B, 1, j, kl)
    n_scale = scales["n_scale"]
    N = ceil(8*n_scale)
    lhs = sum(sum(mobius(d)*d for d in divisors(gcd(M, abs(n))))
              *float(F(n, n_scale))**2*exp(-pi*float(F(n, n_scale))**2)
              *cmath.exp(-2j*pi*float(F(n*kl, j*B)))
              for n in range(-N, N+1))/B
    rows = pt.primitive_band_rows(M, B, j, kl, F(8, J))
    rhs = J*mobius(M)*sum((1/(2*pi)-float(J*freq)**2)*exp(-pi*float(J*freq)**2)
                         for _, _, freq in rows)
    assert lhs == pytest.approx(rhs, abs=2e-10)


@pytest.mark.parametrize("call", [
    lambda: pt.variable_kappa_parameters(0, 2, 8, 256, 3, 1, 4, 8),
    lambda: pt.variable_kappa_parameters(512, 2, 8, 256, 3, 0, 4, 8),
    lambda: pt.variable_kappa_parameters(512, 2, 8, 256, 3, 1, 0, 8),
    lambda: pt.variable_kappa_parameters(512, 2, 8, 256, 3, 1, 4, 0),
    lambda: pt.variable_kappa_error_exponents(0, F(1, 2), 1),
    lambda: pt.variable_kappa_error_exponents(F(11, 10), 0, 1),
    lambda: pt.variable_kappa_error_exponents(1, F(3, 4), 1),
    lambda: pt.variable_kappa_error_exponents(1, 0, -1),
    lambda: pt.primitive_resonant_j_family(4, 10, 2, 5, 100),
    lambda: pt.primitive_resonant_j_family(6, 0, 2, 5, 100),
    lambda: pt.primitive_resonant_j_family(6, 10, 0, 5, 100),
    lambda: pt.primitive_resonant_j_family(6, 10, 5, 5, 100),
    lambda: pt.primitive_resonant_j_family(6, 10, 2, 5, -1),
])
def test_invalid_domains_are_rejected(call):
    with pytest.raises(ValueError):
        call()
