"""Finite global B regrouping; no assertion of an analytic power saving."""

from fractions import Fraction as F
from math import gcd

import pytest

from scripts import mwkf_physical_type_ramanujan as pt
from scripts.mwkf_mobius_type_identity import mobius


@pytest.mark.parametrize("M,q", [(1, 1), (1, 6), (6, 1), (6, 2), (30, 6), (30, 49), (12, 18)])
def test_complete_product_coefficient_keeps_prime_powers_and_both_unit_masks(M, q):
    for r in range(1, 81):
        direct = sum(mobius(B) for B in range(1, r+1)
                     if r % B == 0 and gcd(B, q) == gcd(r//B, M*q) == 1)
        assert pt.primitive_product_coefficient(M, q, r) == direct
        assert direct == (mobius(r) if M % r == 0 and gcd(r, q) == 1 else 0)


@pytest.mark.parametrize("M,q,bound", [(6, 1, 18), (6, 2, 18), (30, 6, 32), (5, 49, 21)])
def test_finite_global_product_sum_preserves_signed_h_and_closed_product_endpoint(M, q, bound):
    weight = lambda r: F(2*r*r+3*r-1, 1+abs(r))
    direct = sum(mobius(B)*weight(B*h)
                 for B in range(1, bound+1)
                 for h in range(-bound, bound+1)
                 if h and abs(B*h) <= bound and gcd(B, q) == gcd(h, M*q) == 1)
    row = pt.primitive_product_packet(M, q, bound, weight)
    assert row["direct"] == row["collapsed"] == direct
    assert "power_saving" not in row


def test_a_partial_B_shell_does_not_have_the_complete_divisor_cancellation():
    M, q, r = 6, 1, 35
    assert pt.primitive_product_coefficient(M, q, r) == 0
    short = sum(mobius(B) for B in range(1, 6) if r % B == 0 and gcd(r//B, M*q) == 1)
    middle = sum(mobius(B) for B in range(6, 8) if r % B == 0 and gcd(r//B, M*q) == 1)
    assert short == 0 and middle == -1


@pytest.mark.parametrize("M,s,q", [(6, 10, 1), (6, 10, 2), (6, 10, 3), (30, 42, 5), (12, 10, 1), (6, 12, 1), (1, 1, 6)])
def test_unsplit_all_e_fusion_does_not_insert_M_q_or_M_s_coprimality(M, s, q):
    direct = F(0)
    for e in range(1, min(M, s)+1):
        if M % e or s % e:
            continue
        A, d = M//e, s//e
        if gcd(e, A*q) == gcd(d, A*e*q) == 1:
            direct += F(mobius(A)*mobius(e)**2*mobius(d), e*d)
    assert pt.unsplit_all_e_coefficient(M, s, q) == direct
    assert direct == (F(mobius(M)*mobius(s), s) if gcd(s, q) == 1 else 0)


def test_literal_h_zero_is_not_covered_by_the_positive_product_identity():
    assert gcd(0, 1) == 1
    with pytest.raises(ValueError, match="h=0"):
        pt.primitive_product_packet(1, 1, 10, lambda r: r)
    # q>1 excludes h=0 even at M=1; the finite identity remains valid.
    assert pt.primitive_product_packet(1, 2, 10, lambda r: F(1)) == {"direct": 2, "collapsed": 2}


@pytest.mark.parametrize("args", [(0, 1, 1), (1, 0, 1), (1, 1, 0), (1, 1, -1), (F(3, 2), 1, 2)])
def test_product_identity_rejects_nonpositive_or_noninteger_inputs(args):
    with pytest.raises(ValueError):
        pt.primitive_product_coefficient(*args)


def test_primitive_packet_rejects_nonpositive_product_cutoff():
    with pytest.raises(ValueError):
        pt.primitive_product_packet(6, 1, 0, lambda r: r)


def test_unsplit_coefficient_rejects_zero_parent():
    with pytest.raises(ValueError):
        pt.unsplit_all_e_coefficient(0, 6, 1)
