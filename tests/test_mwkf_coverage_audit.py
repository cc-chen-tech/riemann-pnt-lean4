from fractions import Fraction as F
import sys
from pathlib import Path


sys.path.insert(0, str(Path(__file__).parents[1]))

from scripts.audit_mobius_offdiagonal_coverage import (
    BettinChandeeSavings,
    bettin_chandee_covers,
    bettin_chandee_savings,
    classify_box,
    completion_covers,
    completion_exponents,
    joint_completion_covers,
    joint_completion_loss,
    wright_direct_applicability,
)
from scripts.audit_mwkf_ranges import ExponentBox, boundary_witnesses


def test_bc_savings_are_the_two_hand_derived_exponents() -> None:
    balanced = boundary_witnesses()["balanced_max_a"]
    assert bettin_chandee_savings(balanced) == BettinChandeeSavings(
        first=F(-41, 10), second=F(-37, 8)
    )
    short = ExponentBox(F(1), F(1), F(0), F(0), F(0), F(0), F(0))
    assert bettin_chandee_savings(short) == BettinChandeeSavings(
        first=F(1, 20), second=F(1, 8)
    )


def test_bc_requires_both_terms_to_meet_the_local_target() -> None:
    covered = ExponentBox(
        F(1), F(1), F(0), F(0), F(0), F(0), F(0)
    )
    second_term_fails = ExponentBox(
        F(1), F(1), F(0), F(0), F(1, 4), F(0), F(0)
    )
    assert bettin_chandee_covers(covered)
    assert not bettin_chandee_covers(second_term_fails)


def test_completion_records_boundary_and_trivial_losses() -> None:
    box = boundary_witnesses()["balanced_max_a"]
    assert completion_exponents(box) == (F(5), F(3), F(3))
    assert not completion_covers(box)
    unit_a = ExponentBox(F(2), F(1), F(0), F(1), F(0), F(0), F(0))
    assert completion_covers(unit_a)


def test_joint_completion_uses_the_shorter_h_delta_factor() -> None:
    one_delta = boundary_witnesses()["large_q_endpoint"]
    assert joint_completion_loss(one_delta) == F(0)
    assert joint_completion_covers(one_delta)

    balanced = boundary_witnesses()["balanced_max_a"]
    assert joint_completion_loss(balanced) == F(5, 2)
    assert not joint_completion_covers(balanced)


def test_wright_has_no_direct_fixed_factor_in_the_original_s_sum() -> None:
    box = boundary_witnesses()["r_long"]
    result = wright_direct_applicability(box, fixed_denominator_factor=F(0))
    assert not result.improves_bc
    assert result.reason == (
        "R0=1 recovers BC equation (7.2), so gives no improvement"
    )


def test_positive_wright_factor_requires_structured_factorization() -> None:
    box = boundary_witnesses()["r_long"]
    result = wright_direct_applicability(box, fixed_denominator_factor=F(1))
    assert not result.improves_bc
    assert "prior factorization of s" in result.reason


def test_residual_witnesses_use_the_sharpened_completion_route() -> None:
    results = {
        name: classify_box(box) for name, box in boundary_witnesses().items()
    }
    assert results["balanced_max_a"].route == "D"
    assert results["r_long"].route == "D"
    assert results["s_long"].route == "D"
    assert results["large_q_endpoint"].route == "B"


def test_zero_third_length_uses_the_elementary_route_when_bc_fails() -> None:
    box = ExponentBox(F(2), F(1), F(0), F(1), F(0), F(0), F(0))
    assert not bettin_chandee_covers(box)
    assert classify_box(box).route == "B"
