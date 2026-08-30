"""Exact slope-alias sampling and cost ledger, not an analytic gate test."""

from fractions import Fraction as F

import pytest

from scripts import mwkf_physical_type_ramanujan as pt


@pytest.mark.parametrize("Y,n,k,j,K2,width", [
    (10, 13, 3, 1, 7, 1), (10, -13, 3, 1, 7, 1),
    (10, 13, -3, -2, 7, F(1, 2)), (1, 1, 1, 1, 1, 0),
    (4, 5, 2, -1, 3, 2), (7, 12, 4, 2, 9, F(3, 2)),
])
def test_all_B_aliases_match_direct_integer_sampling_without_coprimality_mask(Y, n, k, j, K2, width):
    row = pt.slope_b_sampling(Y, n, k, j, K2, width)
    expected = tuple((B, nu, K2*(nu+F(n*k, j*B)))
                     for B in range(Y, 2*Y) for nu in range(-100, 101)
                     if abs(K2*(nu+F(n*k, j*B))) <= width)
    assert row["rows"] == expected
    for nu, interval in row["intervals"].items():
        Bs = [B for B, v, _ in expected if v == nu]
        assert interval == (min(Bs), max(Bs))


@pytest.mark.parametrize("nu,width,want", [
    (-1, 0, (10, 10)), (-1, F(1, 4), (10, 13)),
    (0, F(1, 2), None), (0, 1, (10, 19)), (1, 0, None),
])
def test_monotone_interval_preserves_closed_frequency_and_half_open_B_endpoints(nu, width, want):
    assert pt.slope_b_interval(10, 10, 1, 1, nu, 1, width) == want


def test_integer_plus_one_cannot_be_discarded_when_continuous_interval_is_tiny():
    row = pt.slope_b_sampling(10, 10, 1, 1, 10000, 0)
    assert row["rows"] == ((10, -1, F(0)),)
    assert F(10, 10000) < len(row["rows"])


def test_sampling_sum_keeps_every_B_in_a_shell_before_absolute_values():
    row = pt.slope_b_sampling(12, 12, 2, 1, 1000, 0)
    assert row["rows"] == ((12, -2, F(0)),)
    # The non-coprime B=12 is an actual alias, not an invalid parent.
    assert row["intervals"] == {-2: (12, 12)}


@pytest.mark.parametrize("a,beta,want", [
    (F(1, 2), F(2, 3), (3, F(5, 2), F(17, 6), 3)),
    (F(1, 2), 1, (3, 3, 3, F(7, 2))),
    (F(1, 2), F(4, 3), (3, F(7, 2), F(19, 6), 4)),
    (0, F(4, 3), (3, 3, F(8, 3), 4)),
    (F(1, 4), F(7, 6), (3, 3, F(17, 6), F(15, 4))),
    (F(1, 2), 3, (3, 6, 4, F(13, 2))),
])
def test_new_error_ledger_pays_both_sampling_terms_and_does_not_claim_full_coverage(a, beta, want):
    row = pt.global_slope_error_exponents(a, beta)
    assert tuple(row[key] for key in ("density", "interval_error", "integer_error", "uncompleted_error")) == want
    assert "covered" not in row


@pytest.mark.parametrize("call", [
    lambda: pt.slope_b_interval(0, 1, 1, 1, 1, 1, 1),
    lambda: pt.slope_b_interval(1, 0, 1, 1, 1, 1, 1),
    lambda: pt.slope_b_interval(1, 1, 1, 0, 1, 1, 1),
    lambda: pt.slope_b_interval(1, 1, 1, 1, F(1, 2), 1, 1),
    lambda: pt.slope_b_sampling(1, 1, 1, 1, 0, 1),
    lambda: pt.slope_b_sampling(1, 1, 1, 1, 1, -1),
    lambda: pt.global_slope_error_exponents(-1, 1),
    lambda: pt.global_slope_error_exponents(F(3, 4), 1),
    lambda: pt.global_slope_error_exponents(F(1, 2), -1),
])
def test_invalid_domains_are_rejected(call):
    with pytest.raises(ValueError):
        call()
