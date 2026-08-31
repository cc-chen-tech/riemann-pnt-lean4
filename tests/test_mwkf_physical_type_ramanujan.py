"""End-to-end finite coefficients, not a continuous transform or gate proof."""

import cmath
import importlib
import importlib.util
import math
from fractions import Fraction as F

import pytest


def adapter():
    name = "scripts.mwkf_physical_type_ramanujan"
    assert importlib.util.find_spec(name) is not None, "physical Type/Ramanujan adapter missing"
    return importlib.import_module(name)


@pytest.mark.parametrize("n,q,want", [(1, 12, 1), (2, 6, 0), (5, 6, -1),
                                     (6, 5, 1), (6, 2, 0), (12, 5, 0)])
def test_endpoint_type_identity_keeps_q_coprimality_and_nonsquarefree_cancellation(n, q, want):
    out = adapter().restricted_type_ledger(n, q)
    assert out["direct"] == out["reassembled"] == want


def test_nonsquarefree_parent_has_nonzero_allocations_that_must_cancel():
    out = adapter().restricted_type_ledger(4, 3)
    assert out["terms"] == ((1, 4, -1), (2, 2, 1))
    assert out["reassembled"] == 0


@pytest.mark.parametrize("Q", [1, 2, 6, 12, 30, 77])
def test_restricted_mobius_convolution_retains_prime_power_smooth_cofactors(Q):
    from scripts.mwkf_mobius_type_identity import mobius

    for n in range(1, 81):
        out = adapter().restricted_smooth_ledger(n, Q)
        assert out["sum"] == mobius(n)*int(math.gcd(n, Q) == 1)
    if Q == 2:
        assert adapter().restricted_smooth_ledger(8, 2)["terms"] == (
            (1, 8, 0), (2, 4, 0), (4, 2, -1), (8, 1, 1))


@pytest.mark.parametrize("D,r,M", [(F(7, 2), 7, 0), (10, 3, 2), (3, 8, 1),
                                   (F(9, 2), 2, F(3, 2))])
def test_long_smooth_cofactor_harmonic_bound_keeps_integer_endpoints(D, r, M):
    out = adapter().cofactor_count_bound(D, r, M)
    direct = sum((F(1, r*n) for n in range(1, 30) if D <= r*n <= 2*D), F(0))
    assert out["harmonic_sum"] == direct
    assert direct <= out["harmonic_bound"]
    assert out["all_c_bound"] == out["harmonic_bound"]*(1+2*F(M)/D)


def fixture(s=5, q=2, weights=None):
    return adapter().finite_type_ramanujan(
        s, q, {1: 1-2j, 4: 2, 5: 1j, 6: -1+2j, 7: 3, 8: -2j}
        if weights is None else weights,
        {-2: 1j, 1: 2, 3: -1}, {-1: 3-1j, 2: -2}, R=4, S=s, H=2, L=3)


@pytest.mark.parametrize("s,q", [(5, 2), (6, 5), (7, 3), (10, 3), (5, 5)])
def test_three_finite_transforms_match_the_original_signed_h_delta_sum(s, q):
    out = fixture(s, q)
    from scripts.mwkf_mobius_type_identity import mobius

    entry = {1: 1-2j, 4: 2, 5: 1j, 6: -1+2j, 7: 3, 8: -2j}
    direct = sum(
        mobius(s)*mobius(n)*w*u*v*cmath.exp(-2j*math.pi*((h*d*pow(n, -1, s)) % s)/s)
        for n, w in entry.items() if math.gcd(n, s*q) == 1 and math.gcd(s, q) == 1
        for h, u in {-2: 1j, 1: 2, 3: -1}.items()
        for d, v in {-1: 3-1j, 2: -2}.items())
    assert out["direct"] == pytest.approx(direct, abs=1e-9)
    for key in ("type_sum", "kloosterman_sum", "ramanujan_sum", "divisor_sum"):
        assert out[key] == pytest.approx(direct, abs=1e-9), key


def test_the_unaveraged_physical_prefactor_is_HL_not_HL_over_S():
    out = fixture(weights={5: 1})
    # q=2, s=5: this parent is not a unit, so use a nonzero unit fixture below.
    assert out["direct"] == 0
    out = adapter().finite_type_ramanujan(
        3, 1, {2: 1}, {1: 1}, {1: 1}, R=2, S=3, H=1, L=1)
    # mu(2)mu(3)=1 and inverse(2) mod 3 is 2.
    want = complex(-0.5, math.sqrt(3)/2)
    assert out["direct"] == pytest.approx(want, abs=1e-12)
    assert out["divisor_sum"] == pytest.approx(want, abs=1e-12)
    assert out["extra_inverse_S"] == pytest.approx(want/3, abs=1e-12)
    assert abs(out["direct"] - out["extra_inverse_S"]) > 0.6


def test_continuous_double_poisson_has_the_same_prefactor_with_both_primal_axes_zero():
    coefficient = getattr(adapter(), "ramanujan_divisor_coefficient", None)
    assert callable(coefficient), "unaveraged Ramanujan divisor coefficient missing"
    s, A, m, H, L = 5, 2, 3, 2.1, 1.7

    def weight(x):
        return x*math.exp(-math.pi*x*x)

    def transform(x):
        return -1j*x*math.exp(-math.pi*x*x)

    def phase(x):
        return cmath.exp(2j*math.pi*(x % s)/s)

    direct = -sum(
        weight(h/H)*weight(d/L)*sum(phase(pow(A, -1, s)*m*x-h*d*pow(x, -1, s))
                                  for x in range(1, s))
        for h in range(-20, 21) for d in range(-20, 21))/s
    dual = H*L*sum(transform(k*H/s)*transform(l*L/s)*coefficient(s, A, m, k, l)
                   for k in range(-40, 41) for l in range(-40, 41))
    assert direct == pytest.approx(0.06575795602712471, abs=1e-13)
    assert dual == pytest.approx(direct, abs=1e-13)
    assert abs(dual/s - direct) > 0.05


@pytest.mark.parametrize("s,q", [(4, 1), (0, 1), (5, 0)])
def test_invalid_squarefree_modulus_or_q_is_rejected(s, q):
    with pytest.raises(ValueError):
        fixture(s, q)
