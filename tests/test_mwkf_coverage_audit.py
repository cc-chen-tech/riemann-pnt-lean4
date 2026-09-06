import sys
from fractions import Fraction as F
from math import gcd
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).parents[1]))

from scripts import audit_mobius_offdiagonal_coverage as coverage_audit
from scripts.audit_mobius_offdiagonal_coverage import (
    BettinChandeeSavings,
    PublishedCoverageCell,
    bettin_chandee_covers,
    bettin_chandee_savings,
    classify_box,
    completion_covers,
    completion_exponents,
    dyadic_gcd_sum,
    inverse_product_max_multiplicity,
    joint_completion_covers,
    joint_completion_loss,
    published_coverage_cell,
    published_coverage_witnesses,
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


def test_bc_coverage_uses_the_strict_one_over_thousand_gate() -> None:
    positive_but_too_small = ExponentBox(
        F(1), F(1), F(0), F(0), F(0), F(99, 1700), F(0)
    )
    savings = bettin_chandee_savings(positive_but_too_small)
    assert savings.first == F(1, 2000)
    assert savings.second > F(1, 1000)
    assert not bettin_chandee_covers(positive_but_too_small)


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


def test_published_coverage_cells_partition_the_polytope_exactly() -> None:
    bcr = ExponentBox(F(1), F(1), F(0), F(0), F(0), F(0), F(0))
    h_zero = ExponentBox(F(2), F(1), F(0), F(1), F(1), F(0), F(0))
    cells = {
        "bcr": published_coverage_cell(bcr),
        "ell_zero": published_coverage_cell(
            boundary_witnesses()["large_q_endpoint"]
        ),
        "h_zero": published_coverage_cell(h_zero),
        "balanced": published_coverage_cell(
            boundary_witnesses()["balanced_max_a"]
        ),
        "s_long": published_coverage_cell(boundary_witnesses()["s_long"]),
    }

    assert cells["bcr"] == PublishedCoverageCell(
        name="A_rho_ge_sigma",
        route="A",
        covered=True,
        decisive_saving=F(1, 20),
        target_saving=F(1, 1000),
        reason="both Bettin--Chandee terms beat the strict target",
    )
    assert cells["ell_zero"].name == "B_ell_zero"
    assert cells["ell_zero"].covered
    assert cells["h_zero"].name == "B_h_zero"
    assert cells["h_zero"].covered
    assert cells["balanced"].name == "D_rho_ge_sigma"
    assert not cells["balanced"].covered
    assert cells["s_long"].name == "D_sigma_gt_rho"
    assert not cells["s_long"].covered


def test_every_symbolic_coverage_cell_has_an_exact_rational_witness() -> None:
    witnesses = published_coverage_witnesses()
    assert set(witnesses) == {
        "A_rho_ge_sigma",
        "A_sigma_gt_rho",
        "B_ell_zero",
        "B_h_zero",
        "D_rho_ge_sigma",
        "D_sigma_gt_rho",
    }
    for expected_cell, box in witnesses.items():
        assert published_coverage_cell(box).name == expected_cell


def test_only_residual_cells_route_to_the_exact_double_mobius_split() -> None:
    route = getattr(coverage_audit, "residual_type_i_ii_ledger", None)
    assert route is not None, "residual Type-I/II ledger is missing"

    balanced = route(boundary_witnesses()["balanced_max_a"])
    assert balanced.coverage_cell == "D_rho_ge_sigma"
    assert balanced.product_frequency_exponent == F(5)
    assert balanced.r_scales.u_exp == F(1)
    assert balanced.s_scales.u_exp == F(1)
    assert balanced.sectors == ("I/I", "I/II", "II/I", "II/II")
    assert balanced.preserves_product_frequency
    assert balanced.preserves_two_mobius_weights
    assert not balanced.proves_residual_estimate

    with pytest.raises(ValueError, match="only residual D cells"):
        route(boundary_witnesses()["large_q_endpoint"])


def test_residual_finite_certificate_keeps_h_delta_before_estimation() -> None:
    adapter = getattr(
        coverage_audit,
        "residual_coupled_type_certificate",
        None,
    )
    assert adapter is not None, "residual finite certificate adapter is missing"

    certificate = adapter(
        boundary_witnesses()["balanced_max_a"],
        r=30,
        s=77,
        h=3,
        delta=-5,
        r_cutoff_u=3,
        r_cutoff_v=5,
        s_cutoff_u=4,
        s_cutoff_v=6,
    )
    assert certificate.product_frequency == -15
    assert certificate.phase_mod_one == F(39, 77)
    assert certificate.two_mobius_sides_preserved
    assert certificate.recombination_identity_verified


def test_drappeau_double_quotient_has_the_three_exact_k_squared_terms() -> None:
    adapter = getattr(
        coverage_audit,
        "drappeau_double_quotient_audit",
        None,
    )
    assert adapter is not None, "Drappeau double-quotient audit is missing"

    hard = boundary_witnesses()["balanced_max_a"]
    audit = adapter(
        hard,
        r_smooth_quotient_exponent=F(3),
        s_smooth_quotient_exponent=F(5, 2),
    )

    assert audit.r_coefficient_exponent == F(0)
    assert audit.s_coefficient_exponent == F(1, 2)
    assert audit.coefficient_l2_exponent == F(11, 4)
    assert audit.k_squared_first_exponent == F(11)
    assert audit.k_squared_second_exponent == F(11)
    assert audit.k_squared_third_exponent == F(21, 2)
    assert audit.bound_exponent == F(33, 4)
    assert audit.target_exponent == F(5999, 1000)
    assert audit.target_deficit == F(2251, 1000)
    assert not audit.analytic_size_covers
    assert not audit.sharp_hyperbola_adapter_verified
    assert not audit.published_coverage


def test_drappeau_size_cell_is_not_coverage_before_boundary_adapter() -> None:
    adapter = getattr(
        coverage_audit,
        "drappeau_double_quotient_audit",
        None,
    )
    assert adapter is not None, "Drappeau double-quotient audit is missing"

    short_product = ExponentBox(
        F(3), F(3), F(1, 2), F(1, 2), F(1, 4), F(1, 4), F(0)
    )
    audit = adapter(
        short_product,
        r_smooth_quotient_exponent=F(3),
        s_smooth_quotient_exponent=F(5, 2),
    )

    assert published_coverage_cell(short_product).route == "D"
    assert audit.bound_exponent == F(39, 8)
    assert audit.analytic_size_covers
    assert not audit.sharp_hyperbola_adapter_verified
    assert not audit.published_coverage


def test_drappeau_hard_box_optimum_is_exactly_thirty_three_over_four() -> None:
    optimum = getattr(
        coverage_audit,
        "drappeau_balanced_hard_optimum",
        None,
    )
    assert optimum is not None, "Drappeau hard-box optimum is missing"

    audit = optimum()
    assert audit.minimum_bound_exponent == F(33, 4)
    assert audit.r_smooth_quotient_exponent == F(3)
    assert audit.s_smooth_quotient_min_exponent == F(5, 2)
    assert audit.s_smooth_quotient_max_exponent == F(3)
    assert audit.target_deficit == F(2251, 1000)
    assert audit.lower_bound_proved_by_two_piece_max


def test_drappeau_strict_type_subcell_has_a_boundary_safe_adapter() -> None:
    adapter = getattr(
        coverage_audit,
        "drappeau_type_subcell_audit",
        None,
    )
    assert adapter is not None, "refined Drappeau Type audit is missing"

    short_product = ExponentBox(
        F(3), F(3), F(1, 2), F(1, 2), F(1, 4), F(1, 4), F(0)
    )
    audit = adapter(
        short_product,
        r_truncated_divisor_exponent=F(0),
        r_smooth_quotient_exponent=F(3),
        s_truncated_divisor_exponent=F(0),
        s_smooth_quotient_exponent=F(5, 2),
        r_cutoff_exponent=F(1),
        s_cutoff_exponent=F(1),
    )

    assert audit.r_short_mobius_exponent == F(0)
    assert audit.s_short_mobius_exponent == F(1, 2)
    assert audit.r_hyperbola_relation == "strict_far"
    assert audit.s_hyperbola_relation == "strict_far"
    assert audit.sharp_hyperbola_adapter_verified
    assert audit.base.analytic_size_covers
    assert audit.published_coverage


def test_drappeau_boundary_type_subcell_stays_residual() -> None:
    adapter = getattr(
        coverage_audit,
        "drappeau_type_subcell_audit",
        None,
    )
    assert adapter is not None, "refined Drappeau Type audit is missing"

    short_product = ExponentBox(
        F(3), F(3), F(1, 2), F(1, 2), F(1, 4), F(1, 4), F(0)
    )
    audit = adapter(
        short_product,
        r_truncated_divisor_exponent=F(1),
        r_smooth_quotient_exponent=F(0),
        s_truncated_divisor_exponent=F(0),
        s_smooth_quotient_exponent=F(5, 2),
        r_cutoff_exponent=F(1),
        s_cutoff_exponent=F(1),
    )

    assert audit.r_short_mobius_exponent == F(2)
    assert audit.r_hyperbola_relation == "boundary"
    assert audit.s_hyperbola_relation == "strict_far"
    assert not audit.sharp_hyperbola_adapter_verified
    assert not audit.published_coverage


def test_drappeau_truncated_divisor_cutoff_equality_is_a_boundary() -> None:
    adapter = getattr(
        coverage_audit,
        "drappeau_type_subcell_audit",
        None,
    )
    assert adapter is not None, "refined Drappeau Type audit is missing"

    short_product = ExponentBox(
        F(3), F(3), F(1, 2), F(1, 2), F(1, 4), F(1, 4), F(0)
    )
    audit = adapter(
        short_product,
        r_truncated_divisor_exponent=F(1),
        r_smooth_quotient_exponent=F(1),
        s_truncated_divisor_exponent=F(0),
        s_smooth_quotient_exponent=F(5, 2),
        r_cutoff_exponent=F(1),
        s_cutoff_exponent=F(1),
    )

    assert audit.r_hyperbola_relation == "boundary"
    assert audit.s_hyperbola_relation == "strict_far"
    assert not audit.sharp_hyperbola_adapter_verified
    assert not audit.published_coverage


def test_drappeau_type_subcell_detects_empty_hyperbola_scale() -> None:
    adapter = getattr(
        coverage_audit,
        "drappeau_type_subcell_audit",
        None,
    )
    assert adapter is not None, "refined Drappeau Type audit is missing"

    short_product = ExponentBox(
        F(3), F(3), F(1, 2), F(1, 2), F(1, 4), F(1, 4), F(0)
    )
    audit = adapter(
        short_product,
        r_truncated_divisor_exponent=F(0),
        r_smooth_quotient_exponent=F(1, 2),
        s_truncated_divisor_exponent=F(0),
        s_smooth_quotient_exponent=F(5, 2),
        r_cutoff_exponent=F(1),
        s_cutoff_exponent=F(1),
    )

    assert audit.r_hyperbola_relation == "empty"
    assert audit.asymptotically_empty
    assert not audit.published_coverage


def test_drappeau_refinement_still_cannot_cover_the_hard_box() -> None:
    adapter = getattr(
        coverage_audit,
        "drappeau_type_subcell_audit",
        None,
    )
    assert adapter is not None, "refined Drappeau Type audit is missing"

    audit = adapter(
        boundary_witnesses()["balanced_max_a"],
        r_truncated_divisor_exponent=F(0),
        r_smooth_quotient_exponent=F(3),
        s_truncated_divisor_exponent=F(0),
        s_smooth_quotient_exponent=F(5, 2),
        r_cutoff_exponent=F(1),
        s_cutoff_exponent=F(1),
    )

    assert audit.sharp_hyperbola_adapter_verified
    assert audit.base.bound_exponent == F(33, 4)
    assert not audit.base.analytic_size_covers
    assert not audit.published_coverage


def test_zero_third_length_uses_the_elementary_route_when_bc_fails() -> None:
    box = ExponentBox(F(2), F(1), F(0), F(1), F(0), F(0), F(0))
    assert not bettin_chandee_covers(box)
    assert classify_box(box).route == "B"


def test_inverse_product_fibres_are_bounded_by_the_gcd() -> None:
    for modulus in range(2, 80):
        for delta in range(1, 2 * modulus + 1):
            assert inverse_product_max_multiplicity(modulus, delta) <= gcd(
                modulus, delta
            )


def test_dyadic_gcd_sum_has_the_boundary_safe_divisor_bound() -> None:
    for modulus in range(1, 100):
        divisor_count = sum(modulus % d == 0 for d in range(1, modulus + 1))
        for length in range(1, 40):
            assert dyadic_gcd_sum(modulus, length) <= (
                6 * length * divisor_count
            )
