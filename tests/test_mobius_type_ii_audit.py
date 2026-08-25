from fractions import Fraction as F
import sys
from pathlib import Path


sys.path.insert(0, str(Path(__file__).parents[1]))

from scripts.audit_mobius_type_ii import (
    WrightFactorSavings,
    c_coefficient,
    mobius_geometric_value,
    wright_factor_covers,
    wright_factor_savings,
)
from scripts.audit_mwkf_ranges import boundary_witnesses


def naive_mobius(n: int) -> int:
    value = 1
    prime = 2
    remaining = n
    while prime * prime <= remaining:
        if remaining % prime == 0:
            remaining //= prime
            value = -value
            if remaining % prime == 0:
                return 0
            while remaining % prime == 0:
                remaining //= prime
        prime += 1
    if remaining > 1:
        value = -value
    return value


def least_depth(cutoff: int, limit: int) -> int:
    depth = 1
    power = cutoff
    while power < limit:
        depth += 1
        power *= cutoff
    return depth


def test_finite_mobius_geometric_identity_through_cutoff_power() -> None:
    limit = 200
    for cutoff in (2, 3, 5):
        depth = least_depth(cutoff, limit)
        for n in range(1, limit + 1):
            assert mobius_geometric_value(n, cutoff, depth) == naive_mobius(n)


def test_c_coefficient_has_the_required_initial_support_gap() -> None:
    for cutoff in (2, 3, 5, 11):
        assert [c_coefficient(n, cutoff) for n in range(1, cutoff + 1)] == [
            0
        ] * cutoff


def test_balanced_wright_factor_savings_are_literal_fractions() -> None:
    box = boundary_witnesses()["balanced_max_a"]
    assert wright_factor_savings(box, F(0)) == WrightFactorSavings(
        first=F(-37, 8),
        second=F(-37, 8),
        third=F(-23, 5),
        fourth=F(-41, 10),
        fifth=F(-37, 8),
    )
    assert wright_factor_savings(box, F(1)) == WrightFactorSavings(
        first=F(-5),
        second=F(-39, 8),
        third=F(-97, 20),
        fourth=F(-21, 5),
        fifth=F(-9, 2),
    )


def test_balanced_box_is_uncovered_for_every_allowed_half_step_factor() -> None:
    box = boundary_witnesses()["balanced_max_a"]
    for tau in (F(0), F(1, 2), F(1), F(3, 2)):
        assert not wright_factor_covers(box, tau)


def test_fixed_factor_never_improves_the_decisive_first_term() -> None:
    for box in boundary_witnesses().values():
        baseline = box.sigma / 8 - box.third_length
        for tau in (F(0), F(1, 4), F(1, 2), F(1)):
            savings = wright_factor_savings(box, tau)
            assert savings.first <= baseline
