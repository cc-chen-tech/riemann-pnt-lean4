from fractions import Fraction as F
import sys
from pathlib import Path


sys.path.insert(0, str(Path(__file__).parents[1]))

from scripts.audit_mobius_type_ii import (
    MQWBlockSavings,
    PascadiFullResidueSavings,
    WrightFactorSavings,
    c_coefficient,
    mqw_block_savings,
    mqw_initial_rectangle_supremal_saving,
    mqw_initial_rectangle_witness,
    mobius_geometric_value,
    pascadi_balanced_gap,
    pascadi_full_residue_savings,
    pascadi_optimal_delta,
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


def test_pascadi_full_residue_optimum_is_the_exact_intersection() -> None:
    delta = pascadi_optimal_delta()
    assert delta == F(7, 191)
    savings = pascadi_full_residue_savings(delta)
    assert savings == PascadiFullResidueSavings(
        first=F(33, 191),
        second=F(33, 191),
        third=F(257, 764),
        fourth=F(13, 24),
    )
    assert min(savings.values()) == F(33, 191)


def test_pascadi_still_leaves_the_balanced_local_gap() -> None:
    assert pascadi_balanced_gap() == F(856, 191)


def test_mqw_initial_rectangle_has_exact_one_sixteenth_supremum() -> None:
    x, y = mqw_initial_rectangle_witness()
    assert (x, y) == (F(5, 8), F(5, 8))
    assert mqw_block_savings(x, y) == MQWBlockSavings(
        first=F(7, 48),
        second=F(1, 16),
        third=F(1, 16),
    )
    assert mqw_initial_rectangle_supremal_saving() == F(1, 16)


def test_mqw_witness_satisfies_every_size_condition_exactly() -> None:
    x, y = mqw_initial_rectangle_witness()
    assert x <= y + F(1, 4)
    assert F(7, 5) * x + y == F(3, 2)
    assert x + y <= F(5, 4)


def test_mqw_third_term_certifies_global_one_sixteenth_ceiling() -> None:
    # The theorem assumes x+y <= 5/4, so its third saving is always
    # at most 3(5/4)/16 - 11/64 = 1/16.  This is a certificate, not
    # a numerical grid search.
    ceiling = F(3, 16) * F(5, 4) - F(11, 64)
    assert ceiling == F(1, 16)
