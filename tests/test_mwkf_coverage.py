from fractions import Fraction as F
from math import gcd
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).parents[1]))

from scripts import audit_mwkf_coverage as coverage_audit
from scripts.audit_mwkf_coverage import (
    TARGET_SAVING,
    bcr_adapter,
    completion_dual_exponent,
    dual_cell_isolation_scales,
    farey_critical_scales,
    farey_completion_scales,
    farey_trilinear_adapter,
    h_completion_adapter,
    h_poisson_shifted_scales,
    h_poisson_subbox_scales,
    joint_phase_scales,
    mobius_trace_function_audit,
    route_box,
    wright_fixed_factor_adapter,
)
from scripts.audit_mwkf_ranges import ExponentBox, boundary_witnesses


COVERAGE_NOTE = Path(
    "docs/research/2026-08-24-mwkf-published-coverage.md"
)
ALTERNATIVE_ROUTES_NOTE = Path(
    "docs/research/2026-08-25-mwkf-alternative-routes-spike.md"
)


def test_bcr_covers_a_small_third_variable_box() -> None:
    box = ExponentBox(F(1), F(1), F(0), F(0), F(0), F(0), F(2))
    result = bcr_adapter(box)
    assert result.applicable
    assert result.route == "bcr"
    assert result.saving == F(1, 20)
    assert result.saving >= TARGET_SAVING


def test_balanced_maximal_box_has_exact_bcr_deficit() -> None:
    box = boundary_witnesses()["balanced_max_a"]
    result = bcr_adapter(box)
    assert not result.applicable
    assert result.saving == F(-37, 8)
    assert result.reason == "insufficient_saving"


def test_short_h_poisson_has_half_power_dual_not_a_kinematic_rejection() -> None:
    box = boundary_witnesses()["balanced_max_a"]
    assert completion_dual_exponent(box.h, box.sigma) == F(1, 2)
    result = h_completion_adapter(box)
    assert not result.applicable
    assert result.reason == "no_cited_completed_kernel_bound"
    assert "dual exponent max(0,sigma-h)=1/2" in result.conditions


def test_balanced_h_poisson_reduces_to_exact_critical_shifted_scales() -> None:
    box = boundary_witnesses()["balanced_max_a"]
    scales = h_poisson_shifted_scales(box)
    assert scales.v == F(1, 2)
    assert scales.j == F(1, 2)
    assert scales.shift == F(5, 2)
    assert scales.target == F(7, 2)
    assert scales.gate_target == F(3499, 1000)
    assert scales.volume == F(6)
    assert scales.required_saving == F(2501, 1000)
    assert scales.square_root_margin == F(499, 1000)


def test_determinant_lines_are_affine_mobius_correlations_with_an_exact_gcd_ledger() -> None:
    """Record every scale after j=g*j0, v=g*v0 on rv-js=delta."""
    adapter = getattr(
        coverage_audit,
        "determinant_line_mobius_audit",
        None,
    )
    assert adapter is not None, "determinant-line Möbius audit is missing"
    box = boundary_witnesses()["balanced_max_a"]

    expected = {
        F(0): (F(1, 2), F(5, 2), F(5, 2), F(6), F(2501, 1000)),
        F(1, 4): (F(1, 4), F(9, 4), F(11, 4), F(23, 4), F(2251, 1000)),
        F(1, 2): (F(0), F(2), F(3), F(11, 2), F(2001, 1000)),
    }
    for gamma, want in expected.items():
        audit = adapter(box, gcd_exponent=gamma)
        assert audit.dual_j_exponent == F(1, 2)
        assert audit.dual_v_exponent == F(1, 2)
        assert audit.primitive_j_exponent == want[0]
        assert audit.primitive_v_exponent == want[0]
        assert audit.shift_quotient_exponent == want[1]
        assert audit.line_parameter_length_exponent == want[2]
        assert audit.layer_cardinality_exponent == want[3]
        assert audit.global_gate_target_exponent == F(3499, 1000)
        assert audit.required_mobius_saving == want[4]
        assert audit.common_gcd_divides_shift
        assert audit.primitive_slopes_are_coprime
        assert audit.fixed_fiber_is_two_affine_mobius_correlation
        assert audit.coprimality_is_one_residue_per_squarefree_shift_divisor
        assert audit.published_average_supplies_only_logarithmic_saving
        assert not audit.published_uniform_growing_slope_hypothesis_verified
        assert not audit.coupled_weight_hypothesis_verified
        assert not audit.required_positive_power_saving_proved
        assert not audit.published_coverage


def test_two_dimensional_square_root_reduces_the_determinant_residual_to_small_g() -> None:
    """Record the exact gamma-1/1000 margin of the unimodular line box."""
    adapter = getattr(
        coverage_audit,
        "determinant_line_square_root_audit",
        None,
    )
    assert adapter is not None, "determinant-line square-root audit is missing"
    box = boundary_witnesses()["balanced_max_a"]

    zero = adapter(box, gcd_exponent=F(0))
    assert zero.shift_quotient_exponent == F(5, 2)
    assert zero.line_parameter_length_exponent == F(5, 2)
    assert zero.inner_area_exponent == F(5)
    assert zero.two_dimensional_square_root_saving == F(5, 2)
    assert zero.required_mobius_saving == F(2501, 1000)
    assert zero.square_root_margin == F(-1, 1000)
    assert zero.small_g_residual_saving == F(1, 1000)
    assert not zero.square_root_has_power_slack
    assert not zero.critical_layer_needs_only_log_saving

    critical = adapter(box, gcd_exponent=F(1, 1000))
    assert critical.square_root_margin == F(0)
    assert critical.small_g_residual_saving == F(0)
    assert not critical.square_root_has_power_slack
    assert critical.critical_layer_needs_only_log_saving

    large = adapter(box, gcd_exponent=F(1, 2))
    assert large.shift_quotient_exponent == F(2)
    assert large.line_parameter_length_exponent == F(3)
    assert large.inner_area_exponent == F(5)
    assert large.required_mobius_saving == F(2001, 1000)
    assert large.square_root_margin == F(499, 1000)
    assert large.square_root_has_power_slack
    assert not large.critical_layer_needs_only_log_saving

    for audit in (zero, critical, large):
        assert audit.bezout_change_of_variables_is_unimodular
        assert audit.square_root_bound_proved is False
        assert audit.published_coverage is False


def test_published_mobius_progression_variance_has_the_wrong_modulus_range() -> None:
    """Catch applying large-modulus Davenport--Halberstam at Q=X^(1/6)."""
    adapter = getattr(
        coverage_audit,
        "mobius_progression_variance_audit",
        None,
    )
    assert adapter is not None, "Möbius progression-variance audit is missing"
    box = boundary_witnesses()["balanced_max_a"]

    zero = adapter(box, gcd_exponent=F(0))
    assert zero.sequence_length_exponent == F(3)
    assert zero.progression_modulus_exponent == F(1, 2)
    assert zero.dh_asymptotic_min_modulus_exponent == F(3)
    assert zero.dh_modulus_range_deficit == F(5, 2)
    assert zero.dh_variance_main_exponent == F(7, 2)
    assert zero.dh_error_exponent == F(6)
    assert zero.dh_error_over_main_deficit == F(5, 2)
    assert not zero.dh_asymptotic_range_verified
    assert zero.dh_small_modulus_upper_bound_exponent == F(6)
    assert zero.dh_small_modulus_arbitrary_log_saving
    assert zero.dh_small_modulus_bound_uses_positive_monotonicity
    assert zero.gs_bv_level_margin == F(1)
    assert zero.gs_bv_lower_range_verified
    assert zero.gs_bv_level_verified
    assert zero.gs_bv_saves_only_logarithms
    assert zero.one_mobius_progression_discrepancy_only
    assert not zero.second_mobius_coupled_weight_allowed
    assert not zero.query_dependent_smooth_weight_allowed
    assert not zero.published_coverage

    endpoint = adapter(box, gcd_exponent=F(1, 2))
    assert endpoint.progression_modulus_exponent == F(0)
    assert endpoint.dh_modulus_range_deficit == F(3)
    assert endpoint.dh_variance_main_exponent == F(3)
    assert endpoint.dh_error_over_main_deficit == F(3)
    assert endpoint.gs_bv_level_margin == F(3, 2)
    assert not endpoint.gs_bv_lower_range_verified
    assert not endpoint.gs_bv_level_verified
    assert not endpoint.published_coverage


def test_endpoint_determinant_slope_square_function_stays_at_its_positive_diagonal() -> None:
    """Use endpoint tapers without asking a positive square to beat its diagonal."""
    adapter = getattr(
        coverage_audit,
        "determinant_slope_square_function_audit",
        None,
    )
    assert adapter is not None, "determinant slope square-function audit is missing"
    box = boundary_witnesses()["balanced_max_a"]

    expected = {
        F(0): (F(1), F(1, 2), F(6)),
        F(1, 4): (F(1, 2), F(1, 4), F(11, 2)),
        F(1, 2): (F(0), F(0), F(5)),
    }
    for gamma, (slope_pair, cauchy_cost, diagonal) in expected.items():
        audit = adapter(
            box,
            gcd_exponent=gamma,
            endpoint_taper_factors=F(2),
            endpoint_aggregation_log_loss=F(1),
            endpoint_conditions_verified=True,
        )
        assert audit.g_layer_cardinality_exponent == gamma
        assert audit.primitive_slope_pair_exponent == slope_pair
        assert audit.slope_cauchy_cost_exponent == cauchy_cost
        assert audit.raw_identity_diagonal_exponent == diagonal
        assert audit.coarse_square_function_squared_exponent == F(6)
        assert audit.coarse_square_function_norm_exponent == F(3)
        assert audit.aggregated_bound_exponent == F(7, 2)
        assert audit.logarithmic_gate_target_exponent == F(7, 2)
        assert audit.power_margin == F(0)
        assert audit.endpoint_taper_amplitude_log_saving == F(2)
        assert audit.endpoint_taper_squared_log_saving == F(4)
        assert audit.proposed_square_function_squared_log_saving == F(4)
        assert audit.aggregated_amplitude_log_saving == F(2)
        assert audit.endpoint_aggregation_log_loss == F(1)
        assert audit.net_log_saving == F(1)
        assert audit.dh_error_exponent_matches_square_function_power
        assert audit.one_mobius_dh_scale_available
        assert audit.fixed_power_deficit_removed_by_logarithmic_gate
        assert audit.signed_slope_square_function_required
        assert audit.endpoint_conditions_verified
        assert audit.endpoint_diagonal_scale_compatible
        assert not audit.arbitrary_log_saving_below_diagonal_requested
        assert audit.endpoint_bound_produces_little_o
        assert not audit.second_mobius_coupled_dh_theorem_available
        assert not audit.coupled_transform_weight_hypothesis_verified
        assert not audit.square_function_estimate_proved
        assert not audit.published_coverage


def test_endpoint_slope_square_offdiagonal_has_a_half_power_random_margin() -> None:
    """Reduce EDSSF to one nonzero cross-determinant four-Möbius sum."""
    adapter = getattr(
        coverage_audit,
        "endpoint_slope_offdiagonal_audit",
        None,
    )
    assert adapter is not None, "endpoint slope off-diagonal audit is missing"
    box = boundary_witnesses()["balanced_max_a"]

    expected = {
        F(0): (F(11), F(5), F(11, 2), F(1, 2)),
        F(1, 4): (F(21, 2), F(9, 2), F(21, 4), F(3, 4)),
        F(1, 2): (F(10), F(4), F(5), F(1)),
    }
    for gamma, want in expected.items():
        audit = adapter(box, gcd_exponent=gamma)
        assert audit.inner_delta_n_area_exponent == F(5)
        assert audit.expanded_offdiagonal_cardinality_exponent == want[0]
        assert audit.coarse_endpoint_target_exponent == F(6)
        assert audit.required_offdiagonal_saving == want[1]
        assert audit.full_square_root_bound_exponent == want[2]
        assert audit.full_square_root_target_margin == want[3]
        assert audit.cross_determinant_max_exponent == F(5)
        assert audit.endpoint_taper_log_saving_in_square == F(4)
        assert audit.zero_cross_determinant_is_identity_diagonal
        assert audit.nonzero_cross_determinant_recovers_unique_slope
        assert audit.full_square_root_has_power_slack
        assert audit.signed_four_mobius_offdiagonal_required
        assert not audit.published_four_mobius_spectral_bound_available
        assert not audit.offdiagonal_estimate_proved
        assert not audit.published_coverage


def test_endpoint_cokernel_has_one_character_dimension_not_two() -> None:
    """A primitive 2x2 determinant lattice has cyclic cokernel of order Delta."""
    adapter = getattr(
        coverage_audit,
        "endpoint_cokernel_character_audit",
        None,
    )
    assert adapter is not None, "endpoint cokernel character audit is missing"
    box = boundary_witnesses()["balanced_max_a"]

    expected_residual = {
        F(0): F(5, 2),
        F(1, 4): F(2),
        F(1, 2): F(3, 2),
    }
    for gamma, residual in expected_residual.items():
        audit = adapter(
            box,
            gcd_exponent=gamma,
            determinant_exponent=F(5),
        )
        assert audit.smith_first_invariant_exponent == F(0)
        assert audit.smith_second_invariant_exponent == F(5)
        assert audit.cokernel_character_family_exponent == F(5)
        assert audit.orthogonality_normalization_saving == F(5)
        assert audit.naive_two_congruence_character_exponent == F(10)
        assert audit.character_square_root_saving == F(5, 2)
        assert audit.remaining_saving_after_character_square_root == residual
        assert audit.primitive_rows_force_cyclic_cokernel
        assert audit.two_cramer_congruences_are_independent is False
        assert audit.single_finite_character_family_is_exact
        assert audit.four_mobius_entry_cancellation_still_required
        assert not audit.hybrid_character_entry_estimate_proved
        assert not audit.published_coverage


def test_large_q_bounded_zeta_endpoint_is_covered_after_unpoisson() -> None:
    """Regroup all h before absolute values and spend the two endpoint tapers."""
    adapter = getattr(
        coverage_audit,
        "large_q_endpoint_unpoisson_audit",
        None,
    )
    assert adapter is not None, "large-q endpoint un-Poisson audit is missing"
    box = boundary_witnesses()["large_q_endpoint"]
    audit = adapter(box, shift_log_depth=F(0))

    assert audit.reduced_length_exponent == F(1)
    assert audit.shifted_solution_exponent == F(1)
    assert audit.height_integral_exponent == F(1)
    assert audit.pre_poisson_denominator_exponent == F(3)
    assert audit.per_q_contribution_exponent == F(-1)
    assert audit.q_family_cardinality_exponent == F(2)
    assert audit.aggregated_remainder_exponent == F(1)
    assert audit.endpoint_taper_log_saving == F(2)
    assert audit.shift_log_depth == F(0)
    assert audit.net_log_saving == F(2)
    assert audit.all_nonzero_h_boxes_regrouped_before_absolute_value
    assert audit.poisson_zero_mode_has_same_bound
    assert audit.mobius_cancellation_used is False
    assert audit.unconditional_coverage

    direct_route = coverage_audit.endpoint_unpoisson_adapter(
        box,
        shift_log_depth=F(0),
    )
    assert direct_route.route == "endpoint_unpoisson"
    assert direct_route.applicable
    assert direct_route.reason == "covered_by_endpoint_unpoisson"

    critical = adapter(box, shift_log_depth=F(2))
    assert critical.net_log_saving == F(0)
    assert not critical.unconditional_coverage

    # ExponentBox does not encode the polylogarithmic shift depth, so the
    # global router must not promote the whole exponent cell.
    route = route_box(box)
    assert route.route == "mobius_farey_trilinear"
    assert not route.applicable


def test_q_first_factorization_does_not_drop_the_full_height_phase() -> None:
    """The Euler density is exact, but untwisted Menon is not an adapter."""
    adapter = getattr(
        coverage_audit,
        "large_q_endpoint_critical_shift_audit",
        None,
    )
    assert adapter is not None, "large-q critical-shift audit is missing"
    box = boundary_witnesses()["large_q_endpoint"]
    audit = adapter(
        box,
        shift_log_depth=F(2),
        zeta_scales_fixed=True,
    )

    assert audit.shift_log_depth == F(2)
    assert audit.endpoint_taper_log_saving == F(2)
    assert audit.power_remainder_exponent == F(1)
    assert audit.q_mellin_error_power_saving == F(1, 2)
    assert audit.coprimality_divisor_volume_decay == F(2)
    assert audit.fixed_zeta_scales_required
    assert audit.fixed_zeta_scales_supplied
    assert audit.q_summed_density_is_multiplicative
    assert audit.q_restriction_removed_before_correlation
    assert audit.density_weight_has_absolutely_convergent_convolution
    assert audit.fixed_truncation_has_only_fixed_linear_slopes
    assert not audit.menon_shift_average_tends_to_zero
    assert audit.full_height_phase_must_remain_in_correlation
    assert audit.two_limit_tail_tends_to_zero
    assert not audit.critical_shift_subface_covered
    assert not audit.above_critical_subface_covered
    assert not audit.unconditional_coverage

    growing_zeta = adapter(
        box,
        shift_log_depth=F(2),
        zeta_scales_fixed=False,
    )
    assert not growing_zeta.critical_shift_subface_covered
    assert not growing_zeta.unconditional_coverage

    above = adapter(
        box,
        shift_log_depth=F(2001, 1000),
        zeta_scales_fixed=True,
    )
    assert not above.critical_shift_subface_covered
    assert not above.unconditional_coverage


def test_large_q_growing_zeta_face_reduces_to_one_centered_product_energy() -> None:
    """Keep delta divisibility before lifting m*s to one product variable."""
    adapter = getattr(
        coverage_audit,
        "large_q_growing_zeta_product_lift_audit",
        None,
    )
    assert adapter is not None, "growing-zeta product-lift audit is missing"
    audit = adapter(
        boundary_witnesses()["large_q_endpoint"],
        shift_log_depth=F(2),
    )

    assert audit.shift_log_depth == F(2)
    assert audit.endpoint_taper_log_saving == F(2)
    assert audit.absolute_shift_volume_log_exponent == F(2)
    assert audit.absolute_power_exponent == F(1)
    assert audit.gcd_divisibility_removes_spurious_log_loss
    assert audit.product_lift_identity_is_exact
    assert audit.zero_shift_is_explicit_diagonal
    assert audit.required_centered_energy_power_exponent == F(1)
    assert audit.required_centered_energy_log_exponent == F(2)
    assert audit.requires_little_oh_of_local_scale
    assert not audit.published_short_interval_variance_applies
    assert not audit.centered_product_energy_estimate_proved
    assert not audit.unconditional_coverage


def test_height_phase_closes_zeta_depth_strictly_below_shift() -> None:
    """The retained t-phase decays by arbitrary powers of L/M."""
    adapter = getattr(
        coverage_audit,
        "large_q_height_phase_audit",
        None,
    )
    assert adapter is not None, "large-q height-phase audit is missing"
    box = boundary_witnesses()["large_q_endpoint"]
    audit = adapter(
        box,
        shift_log_depth=F(2),
        zeta_log_depth=F(3, 2),
    )

    assert audit.phase_ratio_log_depth == F(1, 2)
    assert audit.absolute_before_phase_log_exponent == F(0)
    assert audit.height_kernel_has_arbitrary_decay
    assert audit.full_height_phase_retained
    assert audit.strict_phase_separation
    assert audit.strict_subface_covered
    assert audit.unconditional_coverage

    boundary = adapter(
        box,
        shift_log_depth=F(2),
        zeta_log_depth=F(2),
    )
    assert boundary.phase_ratio_log_depth == F(0)
    assert not boundary.strict_phase_separation
    assert not boundary.strict_subface_covered
    assert not boundary.unconditional_coverage


def test_boundary_completion_forces_prime_main_and_isolates_reflected_tail() -> None:
    """Complete the endpoint divisor sum before estimating the pi=2 face."""
    adapter = getattr(
        coverage_audit,
        "large_q_boundary_reflection_audit",
        None,
    )
    assert adapter is not None, "large-q boundary reflection audit is missing"
    audit = adapter(
        boundary_witnesses()["large_q_endpoint"],
        shift_log_depth=F(2),
        zeta_log_depth=F(2),
    )

    assert audit.full_q_restricted_divisor_identity_is_exact
    assert audit.full_mass_supported_on_q_smooth_part
    assert audit.full_log_term_supported_on_q_free_prime_powers
    assert audit.squarefree_reduced_variable_forces_prime
    assert audit.sparse_main_main_has_two_prime_sieve_savings
    assert audit.sparse_main_tail_has_one_prime_sieve_saving
    assert audit.formal_terms_with_sparse_main_have_sieve_saving
    assert audit.dyadic_reduced_scale_prevents_direct_completion
    assert audit.afe_weight_prevents_exact_full_divisor_completion
    assert not audit.cross_scale_aggregation_proved
    assert audit.reflected_tail_has_moving_product_threshold
    assert not audit.reflected_tail_phase_separated_at_boundary
    assert audit.formal_remaining_terms == ("reflected_tail", "reflected_tail")
    assert not audit.reflected_tail_energy_estimate_proved
    assert not audit.unconditional_coverage


def test_subcritical_afe_residue_does_not_complete_missing_divisor_scales() -> None:
    """The local residue error is small, but completion changes zeta scale."""
    adapter = getattr(
        coverage_audit,
        "large_q_subcritical_afe_completion_audit",
        None,
    )
    assert adapter is not None, "subcritical AFE completion audit is missing"
    audit = adapter(
        boundary_witnesses()["large_q_endpoint"],
        afe_product_gap=F(1, 10),
        mellin_left_shift=F(1, 8),
    )

    assert audit.afe_product_upper_exponent == F(9, 10)
    assert audit.mellin_residue_is_one
    assert audit.mellin_remainder_power_saving == F(1, 80)
    assert audit.local_shifted_line_absolute_power_exponent == F(1)
    assert audit.short_side_reciprocity_removes_boundary_loss
    assert audit.mellin_remainder_aggregates_to_little_oh
    assert audit.local_endpoint_afe_weight_replaced_by_residue
    assert not audit.all_reduced_dyadic_scales_regrouped_before_absolute_values
    assert not audit.restricted_divisor_completion_applies_to_endpoint_residue_kernel
    assert not audit.subcritical_cross_scale_aggregation_proved
    assert audit.full_divisor_completion_crosses_afe_transition
    assert not audit.full_endpoint_cross_scale_aggregation_proved
    assert not audit.unconditional_coverage


def test_transition_afe_rejects_nonconvergent_left_line_energy() -> None:
    """The right-line Euler identity cannot be shifted term by term."""
    adapter = getattr(
        coverage_audit,
        "large_q_transition_mellin_divisor_audit",
        None,
    )
    assert adapter is not None, "transition Mellin-divisor audit is missing"
    audit = adapter(boundary_witnesses()["large_q_endpoint"])

    assert audit.common_mellin_variable_retained
    assert audit.right_line_product_weight_separates_exactly
    assert audit.right_line_product_energy_is_absolutely_convergent
    assert audit.q_restricted_twisted_euler_product_is_exact
    assert audit.zero_mellin_frequency_recovers_von_mangoldt
    assert audit.nonzero_mellin_frequency_loses_prime_power_support
    assert audit.gaussian_mellin_tail_is_absolutely_summable
    assert not audit.left_line_product_energy_is_absolutely_convergent
    assert not audit.transition_cutoff_preserves_one_sided_divisor_completion
    assert not audit.transition_reduced_to_one_twisted_divisor_energy
    assert not audit.twisted_divisor_energy_estimate_proved
    assert not audit.unconditional_coverage


def test_transition_band_has_exact_zero_line_mellin_energy() -> None:
    """Compact product support permits scale-stable Mellin separation."""
    adapter = getattr(
        coverage_audit,
        "large_q_transition_compact_mellin_audit",
        None,
    )
    assert adapter is not None, "compact transition Mellin audit is missing"
    transition_box = ExponentBox(
        F(1), F(1), F(1, 2), F(1, 2),
        F(1, 2), F(1, 2), F(2),
    )
    audit = adapter(transition_box)

    assert audit.afe_product_band_is_compact
    assert audit.mellin_separation_line == F(0)
    assert audit.mellin_inversion_is_exact
    assert audit.mellin_transform_has_arbitrary_polynomial_decay
    assert audit.product_coefficients_have_no_real_power_growth
    assert audit.q_restricted_twisted_divisor_coefficient_is_exact
    assert audit.coprimality_coupling_is_retained
    assert audit.reflected_tail_coefficient_is_retained
    assert audit.transition_reduced_to_compact_mellin_energy
    assert audit.product_variable_exponent == F(3, 2)
    assert audit.shift_exponent == F(1, 2)
    assert audit.absolute_global_exponent == F(3, 2)
    assert audit.asymptotic_target_exponent == F(1)
    assert audit.critical_power_saving == F(1, 2)
    assert audit.fixed_power_gate_saving == F(501, 1000)
    assert not audit.compact_mellin_energy_estimate_proved
    assert not audit.unconditional_coverage


def test_transition_type_ii_diagonal_has_uniform_power_slack() -> None:
    """Unlike the hard box, the transition Type-II diagonal is harmless."""
    adapter = getattr(coverage_audit, "type_ii_cauchy_diagonal_audit")
    transition_box = ExponentBox(
        F(1), F(1), F(1, 2), F(1, 2),
        F(1, 2), F(1, 2), F(2),
    )
    left = adapter(transition_box, b_exponent=F(1, 3))
    right = adapter(transition_box, b_exponent=F(2, 3))

    assert left.identity_diagonal_exponent == F(3)
    assert right.identity_diagonal_exponent == F(3)
    assert left.spectral_target_margin == F(497, 750)
    assert right.spectral_target_margin == F(247, 750)
    assert left.separate_diagonal_majorant_closes
    assert right.separate_diagonal_majorant_closes
    assert not left.dispersion_subtraction_required
    assert not right.dispersion_subtraction_required
    assert not left.published_coverage
    assert not right.published_coverage


def test_kim_average_shifted_convolution_still_misses_transition_gate() -> None:
    """Even optimistic short-interval exponents leave a 1003/3000 gap."""
    adapter = getattr(
        coverage_audit,
        "transition_kim_average_shifted_convolution_audit",
        None,
    )
    assert adapter is not None, "Kim transition adapter is missing"
    transition_box = ExponentBox(
        F(1), F(1), F(1, 2), F(1, 2),
        F(1, 2), F(1, 2), F(2),
    )
    audit = adapter(
        transition_box,
        left_short_interval_exponent=F(1),
        right_short_interval_exponent=F(1),
    )

    assert audit.correlation_length_exponent == F(3, 2)
    assert audit.shift_average_exponent == F(1, 2)
    assert audit.theorem_h_power == F(2, 3)
    assert audit.optimistic_theorem_bound_exponent == F(11, 6)
    assert audit.fixed_gate_target_exponent == F(1499, 1000)
    assert audit.remaining_power_deficit == F(1003, 3000)
    assert not audit.localized_mobius_divisor_coefficient_is_multiplicative
    assert not audit.uniform_common_mellin_twist_hypothesis_verified
    assert not audit.theorem_applicable
    assert not audit.published_coverage


def test_transition_type_ii_full_zero_ray_closes_but_b_completion_fails() -> None:
    """Audit the full proportional ray and the nonzero determinant modulus."""
    adapter = getattr(
        coverage_audit,
        "transition_type_ii_determinant_audit",
        None,
    )
    assert adapter is not None, "transition determinant adapter is missing"
    transition_box = ExponentBox(
        F(1), F(1), F(1, 2), F(1, 2),
        F(1, 2), F(1, 2), F(2),
    )

    left = adapter(transition_box, b_exponent=F(1, 3))
    right = adapter(transition_box, b_exponent=F(2, 3))

    assert left.numerator_product_exponent == F(1)
    assert left.factorized_y_exponent == F(5, 3)
    assert left.full_zero_determinant_exponent == F(3)
    assert left.square_target_exponent == F(2747, 750)
    assert left.full_zero_determinant_margin == F(497, 750)
    assert left.nonzero_determinant_max_exponent == F(8, 3)
    assert left.reciprocalized_y_modulus_exponent == F(10, 3)
    assert left.y_modulus_square_root_exponent == F(5, 3)
    assert left.b_below_y_modulus_square_root_gap == F(4, 3)
    assert left.y_modulus_completed_dual_length_exponent == F(3)

    assert right.factorized_y_exponent == F(4, 3)
    assert right.full_zero_determinant_exponent == F(3)
    assert right.square_target_exponent == F(2497, 750)
    assert right.full_zero_determinant_margin == F(247, 750)
    assert right.nonzero_determinant_max_exponent == F(7, 3)
    assert right.reciprocalized_y_modulus_exponent == F(8, 3)
    assert right.y_modulus_square_root_exponent == F(4, 3)
    assert right.b_below_y_modulus_square_root_gap == F(2, 3)
    assert right.y_modulus_completed_dual_length_exponent == F(2)

    for audit in (left, right):
        assert audit.full_zero_determinant_separate_majorant_closes
        assert audit.y_modulus_fixed_b_interval_reaches_square_root is False
        assert audit.y_modulus_single_completion_supplies_saving is False
        assert audit.nonzero_determinant_gate_required
        assert not audit.nonzero_determinant_estimate_proved
        assert not audit.published_coverage


def test_transition_type_ii_uses_the_minimal_lcm_b_conductor() -> None:
    """The y1*y2 reciprocity modulus is not the primitive b-conductor."""
    adapter = getattr(
        coverage_audit,
        "transition_type_ii_lcm_completion_audit",
        None,
    )
    assert adapter is not None, "transition lcm-completion adapter is missing"
    transition_box = ExponentBox(
        F(1), F(1), F(1, 2), F(1, 2),
        F(1, 2), F(1, 2), F(2),
    )

    generic = adapter(
        transition_box,
        b_exponent=F(2, 3),
        gcd_s_exponent=F(0),
    )
    assert generic.lcm_modulus_exponent == F(2)
    assert generic.modulus_square_root_exponent == F(1)
    assert generic.b_below_square_root_gap == F(1, 3)
    assert generic.b_above_square_root_surplus == 0
    assert generic.completed_dual_length_exponent == F(4, 3)
    assert generic.nonzero_cardinality_exponent == F(16, 3)
    assert generic.required_total_saving == F(501, 250)
    assert generic.single_b_weil_saving == 0
    assert (
        generic.remaining_saving_after_single_b_completion
        == F(501, 250)
    )
    assert not generic.fixed_b_completion_has_kinematic_saving
    assert not generic.fixed_b_completion_closes_square_target
    assert generic.blomer_pascadi_dimensionless_loss == F(1, 2)

    high_gcd = adapter(
        transition_box,
        b_exponent=F(2, 3),
        gcd_s_exponent=F(3, 4),
    )
    assert high_gcd.lcm_modulus_exponent == F(5, 4)
    assert high_gcd.modulus_square_root_exponent == F(5, 8)
    assert high_gcd.b_below_square_root_gap == 0
    assert high_gcd.b_above_square_root_surplus == F(1, 24)
    assert high_gcd.completed_dual_length_exponent == F(7, 12)
    assert high_gcd.nonzero_cardinality_exponent == F(55, 12)
    assert high_gcd.required_total_saving == F(627, 500)
    assert high_gcd.single_b_weil_saving == F(1, 24)
    assert (
        high_gcd.remaining_saving_after_single_b_completion
        == F(3637, 3000)
    )
    assert high_gcd.fixed_b_completion_has_kinematic_saving
    assert not high_gcd.fixed_b_completion_closes_square_target
    assert high_gcd.blomer_pascadi_dimensionless_loss == F(5, 16)

    for audit in (generic, high_gcd):
        assert audit.original_phase_compresses_to_lcm
        assert not audit.squarefree_coprime_b_weight_is_smooth
        assert not audit.blomer_pascadi_adapter_closes
        assert not audit.published_coverage


def test_long_cutoff_mobius_trace_route_keeps_a_positive_power_gap() -> None:
    """Two optimistic logarithmic trace savings cannot replace T^(501/500)."""
    adapter = getattr(
        coverage_audit,
        "transition_long_cutoff_mobius_trace_audit",
        None,
    )
    assert adapter is not None, "long-cutoff trace adapter is missing"
    transition_box = ExponentBox(
        F(1), F(1), F(1, 2), F(1, 2),
        F(1, 2), F(1, 2), F(2),
    )
    audit = adapter(
        transition_box,
        cutoff_gap_exponent=F(1, 10),
        b_exponent=F(1, 20),
    )

    assert audit.cutoff_exponent == F(9, 10)
    assert audit.a_exponent == F(19, 20)
    assert audit.short_reflected_divisor_exponent == F(1, 20)
    assert audit.trace_length_over_sqrt_modulus_margin == F(9, 20)
    assert audit.ambient_unsquared_exponent == F(3)
    assert audit.fixed_type_ii_target_exponent == F(999, 500)
    assert audit.remaining_power_deficit_after_two_log_savings == F(501, 500)
    assert audit.squarefree_reflection_identity_exact
    assert audit.published_theorem_requires_prime_modulus
    assert not audit.all_actual_moduli_are_prime
    assert not audit.nonexceptional_trace_hypothesis_uniform
    assert not audit.two_logarithmic_savings_close_power_target
    assert not audit.published_coverage


def test_transition_reciprocity_clusters_close_the_sqrt_difference_union() -> None:
    """Endpoint tapers turn the D<=T^(1/2) large-sieve barrier into o(T)."""
    adapter = getattr(
        coverage_audit,
        "transition_reciprocal_cluster_closure_audit",
        None,
    )
    assert adapter is not None, "transition cluster-closure adapter is missing"
    transition_box = ExponentBox(
        F(1), F(1), F(1, 2), F(1, 2),
        F(1, 2), F(1, 2), F(2),
    )
    audit = adapter(transition_box, distance_max=F(1, 2))

    assert audit.numerator_product_exponent == F(1)
    assert audit.clustered_large_sieve_exponent == F(2)
    assert audit.raw_gate_exponent == F(2)
    assert audit.remaining_power_deficit == 0
    assert audit.endpoint_taper_log_saving == F(2)
    assert audit.product_coefficient_l2_log_loss == F(1, 2)
    assert audit.dyadic_distance_log_loss == F(1)
    assert audit.net_log_saving == F(1, 2)
    assert audit.dimensionless_kernel_log_loss == 0
    assert audit.global_remainder_power_exponent == F(1)
    assert audit.reciprocity_cluster_identity_exact
    assert audit.product_coefficient_energy_bound_proved
    assert audit.fixed_transition_kernel_has_uniform_seminorms
    assert audit.low_difference_union_covered
    assert not audit.whole_transition_face_covered
    assert audit.residual_distance_open_interval == (F(1, 2), F(1))
    assert audit.residual_required_saving_at_top == F(1, 2)


def test_transition_far_shell_is_one_explicit_two_mobius_gate() -> None:
    """The top shell retains 421/1000 even after two optimistic FKM uses."""
    adapter = getattr(
        coverage_audit,
        "transition_far_shell_mobius_gate_audit",
        None,
    )
    assert adapter is not None, "transition far-shell gate adapter is missing"
    transition_box = ExponentBox(
        F(1), F(1), F(1, 2), F(1, 2),
        F(1, 2), F(1, 2), F(2),
    )
    top = adapter(
        transition_box,
        distance=F(1),
        fkm_eta=F(1, 25),
        optimistic_fkm_applications=2,
    )

    assert top.current_cluster_bound_exponent == F(5, 2)
    assert top.fixed_gate_target_exponent == F(1999, 1000)
    assert top.required_new_mobius_saving == F(501, 1000)
    assert top.optimistic_fkm_total_saving == F(2, 25)
    assert top.residual_after_optimistic_fkm == F(421, 1000)
    assert top.shifted_variable_exponent == F(1)
    assert top.modulus_exponent == F(1)
    assert top.product_frequency_exponent == F(1)
    assert top.left_mobius_weight_retained
    assert top.right_mobius_weight_retained
    assert top.coupled_kernel_retained
    assert not top.uniform_prime_factor_hypothesis
    assert not top.nonzero_prime_frequency_uniform
    assert not top.joint_cofactor_hypothesis
    assert top.new_joint_two_mobius_estimate_required
    assert not top.estimate_proved
    assert not top.published_coverage


def test_transition_far_shell_type_ii_diagonal_has_uniform_margin() -> None:
    """The final factor boxes leave only a nonzero joint Gram estimate."""
    adapter = getattr(
        coverage_audit,
        "transition_far_shell_factor_box_audit",
        None,
    )
    assert adapter is not None, "transition factor-box adapter is missing"
    transition_box = ExponentBox(
        F(1), F(1), F(1, 2), F(1, 2),
        F(1, 2), F(1, 2), F(2),
    )
    worst = adapter(
        transition_box,
        distance=F(1),
        b_exponent=F(2, 3),
    )

    assert worst.mobius_cutoff_exponent == F(1, 3)
    assert worst.type_split_exponent == F(1, 3)
    assert worst.b_exponent_range == (F(0), F(2, 3))
    assert worst.a_exponent == F(1, 3)
    assert worst.shifted_equation_is_exact
    assert worst.reciprocal_phase_reindexed_exactly
    assert worst.unsquared_cluster_bound_exponent == F(5, 2)
    assert worst.unsquared_fixed_target_exponent == F(999, 500)
    assert worst.unsquared_required_saving == F(251, 500)
    assert worst.identity_diagonal_exponent == F(3)
    assert worst.type_ii_square_target_exponent == F(2497, 750)
    assert worst.identity_diagonal_margin == F(247, 750)
    assert worst.identity_diagonal_closes
    assert worst.nonzero_joint_gram_estimate_required
    assert not worst.nonzero_joint_gram_estimate_proved
    assert not worst.published_coverage


def test_transition_factor_square_full_zero_geometry_closes() -> None:
    """Coprimality makes Gamma=0 primitive; cluster L2 closes all n-pairs."""
    adapter = getattr(
        coverage_audit,
        "transition_factor_square_geometry_audit",
        None,
    )
    assert adapter is not None, "transition square-geometry adapter is missing"
    transition_box = ExponentBox(
        F(1), F(1), F(1, 2), F(1, 2),
        F(1, 2), F(1, 2), F(2),
    )
    worst = adapter(
        transition_box,
        distance=F(1),
        b_exponent=F(2, 3),
    )

    assert worst.geometric_determinant_max_exponent == F(4, 3)
    assert worst.full_zero_geometry_exponent == F(3)
    assert worst.type_ii_square_target_exponent == F(2497, 750)
    assert worst.full_zero_geometry_margin == F(247, 750)
    assert worst.common_b_cross_relation_exact
    assert worst.zero_determinant_primitive_pairs_identical
    assert worst.product_frequency_offdiagonal_retained
    assert worst.reciprocal_cluster_l2_applied_before_absolute_n_pairs
    assert worst.full_zero_geometry_closes
    assert worst.nonzero_geometric_determinant_gate_required
    assert not worst.nonzero_geometric_determinant_gate_proved
    assert not worst.published_coverage


def test_transition_nonzero_gamma_shell_has_exact_orbit_and_gate() -> None:
    """The last Gram gate has an exact determinant orbit and power ledger."""
    adapter = getattr(
        coverage_audit,
        "transition_nonzero_gamma_shell_audit",
        None,
    )
    orbit = getattr(
        coverage_audit,
        "factor_determinant_orbit_parameter",
        None,
    )
    reciprocity = getattr(
        coverage_audit,
        "signed_reciprocity_phase_identity",
        None,
    )
    assert adapter is not None, "nonzero-Gamma shell adapter is missing"
    assert orbit is not None, "factor determinant-orbit helper is missing"
    assert reciprocity is not None, "signed reciprocity helper is missing"

    # Both pairs have determinant 7 for (a1,a2)=(6,9).  Their
    # difference is one primitive step (2,3).
    assert orbit(
        a1=6,
        a2=9,
        s1=5,
        s2=11,
        other_s1=7,
        other_s2=14,
    ) == 1
    assert orbit(
        a1=6,
        a2=9,
        s1=5,
        s2=11,
        other_s1=9,
        other_s2=17,
    ) == 2
    assert orbit(
        a1=6,
        a2=9,
        s1=5,
        s2=11,
        other_s1=6,
        other_s2=12,
    ) is None
    for w, s, n in ((3, 11, 7), (-3, 11, 7), (8, 13, -5)):
        assert reciprocity(w=w, s=s, n=n)

    transition_box = ExponentBox(
        F(1), F(1), F(1, 2), F(1, 2),
        F(1, 2), F(1, 2), F(2),
    )
    generic_top = adapter(
        transition_box,
        distance=F(1),
        b_exponent=F(2, 3),
        determinant_exponent=F(4, 3),
        s_gcd_exponent=F(0),
        a_gcd_exponent=F(0),
    )

    assert generic_top.determinant_exponent_range == (F(0), F(4, 3))
    assert generic_top.s_gcd_divides_determinant
    assert generic_top.a_gcd_divides_determinant
    assert generic_top.lcm_modulus_exponent == F(2)
    assert generic_top.b_completion_dual_exponent == F(4, 3)
    assert generic_top.primitive_a_step_exponent == F(1, 3)
    assert generic_top.determinant_orbit_length_exponent == F(2, 3)
    assert generic_top.current_cluster_square_bound_exponent == F(13, 3)
    assert not generic_top.cluster_square_bound_independently_proved
    assert generic_top.type_ii_square_target_exponent == F(2497, 750)
    assert generic_top.required_joint_saving_exponent == F(251, 250)
    assert generic_top.reciprocity_modulus_exponent == F(1)
    assert not generic_top.reciprocity_strictly_reduces_modulus
    assert generic_top.complete_nonzero_shell_estimate_required
    assert not generic_top.complete_nonzero_shell_estimate_proved
    assert not generic_top.published_coverage


def test_transition_gamma_graph_energy_closes_a_strict_region() -> None:
    """Maximum determinant-fiber degree times cluster L2 closes small xi."""
    adapter = getattr(
        coverage_audit,
        "transition_gamma_graph_energy_audit",
        None,
    )
    assert adapter is not None, "Gamma graph-energy adapter is missing"
    transition_box = ExponentBox(
        F(1), F(1), F(1, 2), F(1, 2),
        F(1, 2), F(1, 2), F(2),
    )

    covered = adapter(
        transition_box,
        distance=F(3, 4),
        b_exponent=F(2, 3),
        determinant_exponent=F(1, 3),
    )
    assert covered.determinant_fiber_exponent == F(0)
    assert covered.maximum_graph_degree_exponent == F(1, 3)
    assert covered.reciprocal_cluster_vertex_energy_exponent == F(11, 4)
    assert covered.graph_energy_bound_exponent == F(37, 12)
    assert covered.type_ii_square_target_exponent == F(2497, 750)
    assert covered.graph_energy_target_margin == F(123, 500)
    assert covered.coverage_threshold == F(249, 250)
    assert covered.maximum_degree_energy_inequality_exact
    assert covered.product_frequency_cluster_l2_used
    assert not covered.mobius_cancellation_used
    assert not covered.phase_cancellation_between_distinct_vertices_used
    assert covered.shell_covered_unconditionally
    assert not covered.published_coverage

    boundary = adapter(
        transition_box,
        distance=F(3, 4),
        b_exponent=F(2, 3),
        determinant_exponent=F(869, 1500),
    )
    assert boundary.coverage_lhs == F(249, 250)
    assert boundary.graph_energy_target_margin == F(0)
    assert boundary.shell_covered_unconditionally

    largest_determinant = adapter(
        transition_box,
        distance=F(3, 4),
        b_exponent=F(2, 3),
        determinant_exponent=F(13, 12),
    )
    assert largest_determinant.determinant_fiber_exponent == F(3, 4)
    assert largest_determinant.graph_energy_target_margin == -F(63, 125)
    assert not largest_determinant.shell_covered_unconditionally

    top_small_determinant = adapter(
        transition_box,
        distance=F(1),
        b_exponent=F(2, 3),
        determinant_exponent=F(1, 3),
    )
    assert top_small_determinant.graph_energy_target_margin == -F(1, 250)
    assert not top_small_determinant.shell_covered_unconditionally


def test_transition_gamma_gcd_graph_energy_closes_top_subshells() -> None:
    """The a- and s-gcd shells reduce graph degree at theta=1."""
    adapter = getattr(
        coverage_audit,
        "transition_gamma_gcd_graph_energy_audit",
        None,
    )
    assert adapter is not None, "gcd-sensitive Gamma graph adapter is missing"
    transition_box = ExponentBox(
        F(1), F(1), F(1, 2), F(1, 2),
        F(1, 2), F(1, 2), F(2),
    )

    high_gcd = adapter(
        transition_box,
        distance=F(1),
        b_exponent=F(2, 3),
        determinant_exponent=F(4, 3),
        s_gcd_exponent=F(1),
        a_gcd_exponent=F(1, 100),
    )
    assert high_gcd.raw_determinant_fiber_exponent == F(1)
    assert high_gcd.gcd_reduced_fiber_exponent == F(0)
    assert high_gcd.maximum_graph_degree_exponent == F(97, 300)
    assert high_gcd.graph_energy_bound_exponent == F(997, 300)
    assert high_gcd.type_ii_square_target_exponent == F(2497, 750)
    assert high_gcd.graph_energy_target_margin == F(3, 500)
    assert high_gcd.coverage_lhs == F(99, 100)
    assert high_gcd.coverage_threshold == F(249, 250)
    assert high_gcd.a_gcd_candidate_reduction_exact
    assert high_gcd.s_gcd_fiber_reduction_exact
    assert high_gcd.shell_covered_unconditionally
    assert not high_gcd.published_coverage

    primitive = adapter(
        transition_box,
        distance=F(1),
        b_exponent=F(2, 3),
        determinant_exponent=F(4, 3),
        s_gcd_exponent=F(0),
        a_gcd_exponent=F(0),
    )
    assert primitive.gcd_reduced_fiber_exponent == F(1)
    assert primitive.maximum_graph_degree_exponent == F(4, 3)
    assert primitive.graph_energy_bound_exponent == F(13, 3)
    assert primitive.graph_energy_target_margin == -F(251, 250)
    assert not primitive.shell_covered_unconditionally


def test_transition_cross_determinant_lattice_closes_top_small_gamma() -> None:
    """The primitive (a,w) lattice has O(Gamma) graph degree."""
    adapter = getattr(
        coverage_audit,
        "transition_cross_determinant_lattice_audit",
        None,
    )
    identity = getattr(
        coverage_audit,
        "factor_cross_determinant_identity",
        None,
    )
    assert adapter is not None, "cross-determinant lattice adapter is missing"
    assert identity is not None, "cross-determinant identity helper is missing"

    for values in (
        dict(a1=5, a2=7, s1=11, s2=13, b=3, k=2),
        dict(a1=8, a2=9, s1=5, s2=7, b=5, k=3),
    ):
        result = identity(**values)
        assert result["cross_relation_exact"]
        assert result["first_entry_gcd_divides_k"]
        assert result["second_entry_gcd_divides_k"]

    transition_box = ExponentBox(
        F(1), F(1), F(1, 2), F(1, 2),
        F(1, 2), F(1, 2), F(2),
    )
    covered = adapter(
        transition_box,
        distance=F(1),
        b_exponent=F(2, 3),
        determinant_exponent=F(1, 4),
    )
    assert covered.maximum_graph_degree_exponent == F(1, 4)
    assert covered.reciprocal_cluster_vertex_energy_exponent == F(3)
    assert covered.graph_energy_bound_exponent == F(13, 4)
    assert covered.type_ii_square_target_exponent == F(2497, 750)
    assert covered.graph_energy_target_margin == F(119, 1500)
    assert covered.coverage_lhs == F(5, 4)
    assert covered.coverage_threshold == F(997, 750)
    assert covered.entry_gcd_bounded_by_fixed_slope
    assert covered.fixed_value_fiber_has_bounded_cardinality
    assert covered.shell_covered_unconditionally
    assert not covered.published_coverage

    boundary = adapter(
        transition_box,
        distance=F(1),
        b_exponent=F(2, 3),
        determinant_exponent=F(247, 750),
    )
    assert boundary.graph_energy_target_margin == F(0)
    assert boundary.shell_covered_unconditionally

    residual = adapter(
        transition_box,
        distance=F(1),
        b_exponent=F(2, 3),
        determinant_exponent=F(1, 3),
    )
    assert residual.graph_energy_target_margin == -F(1, 250)
    assert not residual.shell_covered_unconditionally


def test_transition_farey_hecke_orbit_retains_the_actual_weights() -> None:
    """The residual is an exact determinant orbit, not a free Kuznetsov sum."""
    adapter = getattr(
        coverage_audit,
        "transition_farey_hecke_orbit_audit",
        None,
    )
    identity = getattr(
        coverage_audit,
        "factor_farey_hecke_orbit_identity",
        None,
    )
    assert adapter is not None, "Farey-Hecke orbit adapter is missing"
    assert identity is not None, "Farey-Hecke identity helper is missing"

    for values in (
        dict(a1=5, a2=7, s1=11, s2=13, b=3, k=2, n1=7, n2=-5),
        dict(a1=8, a2=9, s1=5, s2=7, b=3, k=2, n1=-4, n2=9),
    ):
        exact = identity(**values)
        assert exact["hecke_determinant_exact"]
        assert exact["reciprocal_square_phase_exact"]
        assert exact["first_affine_cofactor_exact"]
        assert exact["second_affine_cofactor_exact"]

    transition_box = ExponentBox(
        F(1), F(1), F(1, 2), F(1, 2),
        F(1, 2), F(1, 2), F(2),
    )
    first_residual = adapter(
        transition_box,
        distance=F(1),
        b_exponent=F(2, 3),
        determinant_exponent=F(1, 3),
    )
    assert first_residual.hecke_index_exponent == F(1)
    assert first_residual.entry_exponent == F(1)
    assert first_residual.modulus_exponent == F(1)
    assert first_residual.product_frequency_exponent == F(1)
    assert first_residual.type_ii_square_target_exponent == F(2497, 750)
    assert first_residual.hecke_index_contains_common_b
    assert first_residual.common_b_weight_is_mobius_squared
    assert not first_residual.hecke_index_has_mobius_weight
    assert first_residual.both_entry_mobius_weights_retained
    assert first_residual.affine_cofactor_weights_joint_in_entry_and_modulus
    assert first_residual.archimedean_reciprocity_correction_retained
    assert first_residual.coupled_kernel_retained
    assert not first_residual.classical_kuznetsov_adapter_verified
    assert first_residual.new_entry_weighted_hecke_estimate_required
    assert not first_residual.new_entry_weighted_hecke_estimate_proved
    assert not first_residual.published_coverage

    maximal = adapter(
        transition_box,
        distance=F(1),
        b_exponent=F(2, 3),
        determinant_exponent=F(4, 3),
    )
    assert maximal.hecke_index_exponent == F(2)


def test_transition_entry_mobius_factorization_does_not_reach_wright() -> None:
    """Double reciprocity is exact, but the fixed-factor bound still loses."""
    adapter = getattr(
        coverage_audit,
        "transition_entry_mobius_factorization_audit",
        None,
    )
    identity = getattr(
        coverage_audit,
        "entry_double_reciprocity_identity",
        None,
    )
    assert adapter is not None, "entry Möbius-factor adapter is missing"
    assert identity is not None, "double-reciprocity helper is missing"

    for c, d, modulus, epsilon, n in (
        (5, 7, 11, 1, 9),
        (4, 9, 13, -1, -7),
    ):
        assert identity(
            c=c,
            d=d,
            modulus=modulus,
            epsilon=epsilon,
            n=n,
        )

    transition_box = ExponentBox(
        F(1), F(1), F(1, 2), F(1, 2),
        F(1, 2), F(1, 2), F(2),
    )
    endpoint = adapter(
        transition_box,
        distance=F(1),
        b_exponent=F(2, 3),
        entry_short_factor_exponent=F(2, 3),
    )
    assert endpoint.entry_cutoff_exponent == F(1, 3)
    assert endpoint.entry_long_factor_exponent == F(1, 3)
    assert endpoint.entry_short_factor_exponent == F(2, 3)
    assert endpoint.fixed_denominator_factor_exponent == F(1, 3)
    assert endpoint.wright_size_hypothesis_holds
    assert endpoint.optimistic_wright_saving_exponent == -F(1)
    assert endpoint.factor_box_target_saving_exponent == F(1, 500)
    assert endpoint.optimistic_wright_deficit == F(501, 500)
    assert endpoint.mobius_factorization_exact
    assert endpoint.double_reciprocity_cancels_archimedean_term
    assert endpoint.affine_cofactor_remains_joint
    assert endpoint.shift_window_remains_joint
    assert endpoint.coupled_kernel_remains_joint
    assert not endpoint.actual_wright_coefficient_hypotheses_verified
    assert endpoint.two_entry_type_ii_estimate_required
    assert not endpoint.two_entry_type_ii_estimate_proved
    assert not endpoint.published_coverage

    short = adapter(
        transition_box,
        distance=F(1),
        b_exponent=F(2, 3),
        entry_short_factor_exponent=F(1, 3),
    )
    assert not short.wright_size_hypothesis_holds


def test_transition_cross_gcd_lattice_closes_more_high_determinants() -> None:
    """The a- and w-gcd product reduces the determinant-value count."""
    adapter = getattr(
        coverage_audit,
        "transition_cross_gcd_lattice_audit",
        None,
    )
    divisibility = getattr(
        coverage_audit,
        "factor_cross_gcd_divisibility",
        None,
    )
    assert adapter is not None, "cross-gcd lattice adapter is missing"
    assert divisibility is not None, "cross-gcd divisibility helper is missing"

    for values in (
        dict(a1=5, a2=7, s1=11, s2=13, b=3, k=2),
        dict(a1=8, a2=10, s1=5, s2=7, b=3, k=2),
    ):
        exact = divisibility(**values)
        assert exact["a_w_common_gcd_divides_k"]
        assert exact["combined_gcd_divides_k_gamma"]

    transition_box = ExponentBox(
        F(1), F(1), F(1, 2), F(1, 2),
        F(1, 2), F(1, 2), F(2),
    )
    first_residual = adapter(
        transition_box,
        distance=F(1),
        b_exponent=F(2, 3),
        determinant_exponent=F(1, 3),
        a_gcd_exponent=F(1, 100),
        w_gcd_exponent=F(0),
    )
    assert first_residual.reduced_determinant_value_exponent == F(97, 300)
    assert first_residual.maximum_graph_degree_exponent == F(97, 300)
    assert first_residual.graph_energy_bound_exponent == F(997, 300)
    assert first_residual.graph_energy_target_margin == F(3, 500)
    assert first_residual.coverage_lhs == F(397, 300)
    assert first_residual.coverage_threshold == F(997, 750)
    assert first_residual.a_w_common_gcd_is_slope_bounded
    assert first_residual.combined_gcd_divides_determinant
    assert first_residual.shell_covered_unconditionally
    assert not first_residual.published_coverage

    maximal_high_gcd = adapter(
        transition_box,
        distance=F(1),
        b_exponent=F(2, 3),
        determinant_exponent=F(4, 3),
        a_gcd_exponent=F(1, 3),
        w_gcd_exponent=F(3, 4),
    )
    assert maximal_high_gcd.reduced_determinant_value_exponent == F(1, 4)
    assert maximal_high_gcd.graph_energy_target_margin == F(119, 1500)
    assert maximal_high_gcd.shell_covered_unconditionally

    primitive_maximal = adapter(
        transition_box,
        distance=F(1),
        b_exponent=F(2, 3),
        determinant_exponent=F(4, 3),
        a_gcd_exponent=F(0),
        w_gcd_exponent=F(0),
    )
    assert primitive_maximal.maximum_graph_degree_exponent == F(4, 3)
    assert primitive_maximal.graph_energy_target_margin == -F(251, 250)
    assert not primitive_maximal.shell_covered_unconditionally


def test_transition_triple_gcd_lattice_concentrates_the_core() -> None:
    """All three pairwise gcd shells combine up to the fixed slope."""
    adapter = getattr(
        coverage_audit,
        "transition_triple_gcd_lattice_audit",
        None,
    )
    divisibility = getattr(
        coverage_audit,
        "factor_triple_gcd_divisibility",
        None,
    )
    assert adapter is not None, "triple-gcd lattice adapter is missing"
    assert divisibility is not None, "triple-gcd helper is missing"

    exact = divisibility(
        a1=3,
        a2=6,
        s1=55,
        s2=5,
        b=2,
        k=1,
    )
    assert exact["a_s_gcds_coprime"]
    assert exact["s_w_gcds_coprime"]
    assert exact["a_w_common_gcd_divides_k"]
    assert exact["triple_gcd_divides_k_gamma"]

    transition_box = ExponentBox(
        F(1), F(1), F(1, 2), F(1, 2),
        F(1, 2), F(1, 2), F(2),
    )
    first_residual = adapter(
        transition_box,
        distance=F(1),
        b_exponent=F(2, 3),
        determinant_exponent=F(1, 3),
        a_gcd_exponent=F(0),
        s_gcd_exponent=F(1, 100),
        w_gcd_exponent=F(0),
    )
    assert first_residual.reduced_determinant_value_exponent == F(97, 300)
    assert first_residual.graph_energy_bound_exponent == F(997, 300)
    assert first_residual.graph_energy_target_margin == F(3, 500)
    assert first_residual.shell_covered_unconditionally
    assert not first_residual.published_coverage

    maximal = adapter(
        transition_box,
        distance=F(1),
        b_exponent=F(2, 3),
        determinant_exponent=F(4, 3),
        a_gcd_exponent=F(1, 3),
        s_gcd_exponent=F(1, 3),
        w_gcd_exponent=F(5, 12),
    )
    assert maximal.reduced_determinant_value_exponent == F(1, 4)
    assert maximal.graph_energy_target_margin == F(119, 1500)
    assert maximal.shell_covered_unconditionally

    primitive = adapter(
        transition_box,
        distance=F(1),
        b_exponent=F(2, 3),
        determinant_exponent=F(4, 3),
        a_gcd_exponent=F(0),
        s_gcd_exponent=F(0),
        w_gcd_exponent=F(0),
    )
    assert primitive.reduced_determinant_value_exponent == F(4, 3)
    assert primitive.graph_energy_target_margin == -F(251, 250)
    assert not primitive.shell_covered_unconditionally


def test_transition_final_two_entry_gate_has_only_one_critical_face() -> None:
    """A full two-entry square root has power slack except at one face."""
    adapter = getattr(
        coverage_audit,
        "transition_final_two_entry_gate_audit",
        None,
    )
    assert adapter is not None, "final two-entry gate adapter is missing"
    transition_box = ExponentBox(
        F(1), F(1), F(1, 2), F(1, 2),
        F(1, 2), F(1, 2), F(2),
    )

    critical = adapter(
        transition_box,
        distance=F(1),
        b_exponent=F(2, 3),
        determinant_exponent=F(4, 3),
        a_gcd_exponent=F(0),
        s_gcd_exponent=F(0),
        w_gcd_exponent=F(0),
    )
    assert critical.reduced_determinant_exponent == F(4, 3)
    assert critical.current_graph_bound_exponent == F(13, 3)
    assert critical.two_entry_square_root_saving_exponent == F(1)
    assert critical.required_two_entry_bound_exponent == F(10, 3)
    assert critical.raw_type_ii_square_target_exponent == F(10, 3)
    assert critical.power_margin == F(0)
    assert critical.margin_identity_exact
    assert critical.is_unique_power_critical_face
    assert critical.endpoint_taper_square_log_saving == F(4)
    assert critical.product_energy_log_loss == F(1)
    assert critical.post_cauchy_log_saving == F(3, 2)
    assert critical.beta_box_union_log_loss == F(1)
    assert critical.global_net_log_saving == F(1, 2)
    assert critical.global_remainder_power_exponent == F(1)
    assert critical.two_entry_square_root_gate_required
    assert not critical.two_entry_square_root_gate_proved
    assert not critical.whole_transition_face_covered

    slack = adapter(
        transition_box,
        distance=F(3, 4),
        b_exponent=F(2, 3),
        determinant_exponent=F(13, 12),
        a_gcd_exponent=F(0),
        s_gcd_exponent=F(0),
        w_gcd_exponent=F(0),
    )
    assert slack.required_two_entry_bound_exponent == F(17, 6)
    assert slack.raw_type_ii_square_target_exponent == F(10, 3)
    assert slack.power_margin == F(1, 2)
    assert not slack.is_unique_power_critical_face


def test_transition_h_poisson_line_is_unimodular_in_the_two_mobius_entries() -> None:
    """The critical h-Poisson determinant line has determinant minus one."""
    identity = getattr(
        coverage_audit,
        "transition_h_poisson_line_identity",
        None,
    )
    assert identity is not None, "transition h-Poisson line helper is missing"

    result = identity(
        k=2,
        v0=5,
        j0=3,
        x=2,
        y=-3,
        delta0=7,
        n=11,
    )
    assert result["bezout_identity_exact"]
    assert result["w"] == 47
    assert result["s"] == 76
    assert result["r"] == 199
    assert result["determinant_equation_exact"]
    assert result["mobius_entry_matrix_determinant"] == -1
    assert result["mobius_entry_change_is_unimodular"]


def test_transition_h_poisson_line_gate_has_one_power_critical_layer() -> None:
    """After h-Poisson, inner area T and only theta=1,g=1 is critical."""
    adapter = getattr(
        coverage_audit,
        "transition_h_poisson_line_audit",
        None,
    )
    assert adapter is not None, "transition h-Poisson line audit is missing"

    critical = adapter(distance=F(1), gcd_exponent=F(0))
    assert critical.h_poisson_factor_exponent == F(1, 2)
    assert critical.dual_v_exponent == F(1, 2)
    assert critical.dual_j_exponent == F(1, 2)
    assert critical.primitive_v_exponent == F(1, 2)
    assert critical.primitive_j_exponent == F(1, 2)
    assert critical.shift_quotient_exponent == F(1, 2)
    assert critical.line_parameter_exponent == F(1, 2)
    assert critical.inner_delta_n_area_exponent == F(1)
    assert critical.outer_slope_family_exponent == F(1)
    assert critical.pre_poisson_layer_cardinality_exponent == F(2)
    assert critical.absolute_post_poisson_exponent == F(5, 2)
    assert critical.asymptotic_local_target_exponent == F(2)
    assert critical.required_inner_saving_exponent == F(1, 2)
    assert critical.inner_square_root_saving_exponent == F(1, 2)
    assert critical.square_root_power_margin == F(0)
    assert critical.is_unique_power_critical_layer
    assert critical.mobius_entry_change_is_unimodular
    assert not critical.fixed_slope_square_root_proved
    assert not critical.averaged_slope_square_function_proved
    assert not critical.whole_far_shell_covered

    proper = adapter(distance=F(3, 4), gcd_exponent=F(0))
    assert proper.dual_j_exponent == F(1, 4)
    assert proper.outer_slope_family_exponent == F(3, 4)
    assert proper.absolute_post_poisson_exponent == F(9, 4)
    assert proper.required_inner_saving_exponent == F(1, 4)
    assert proper.square_root_power_margin == F(1, 4)
    assert not proper.is_unique_power_critical_layer

    maximal_gcd = adapter(distance=F(1), gcd_exponent=F(1, 2))
    assert maximal_gcd.primitive_j_exponent == F(0)
    assert maximal_gcd.shift_quotient_exponent == F(0)
    assert maximal_gcd.line_parameter_exponent == F(1)
    assert maximal_gcd.absolute_post_poisson_exponent == F(2)
    assert maximal_gcd.required_inner_saving_exponent == F(0)
    assert maximal_gcd.absolute_count_reaches_power_target
    assert maximal_gcd.maximal_gcd_layer_closes_with_endpoint_tapers


def test_transition_h_poisson_square_cramer_recovers_the_unique_dual_slope() -> None:
    helper = getattr(
        coverage_audit,
        "transition_h_poisson_square_cramer_identity",
        None,
    )
    assert helper is not None, "transition square Cramer helper is missing"

    result = helper(
        k=1,
        s1=5,
        w1=2,
        s2=7,
        w2=4,
        v=3,
        j=1,
    )
    assert result["r1"] == 7
    assert result["r2"] == 11
    assert result["delta1"] == 1
    assert result["delta2"] == 5
    assert result["cross_determinant"] == -6
    assert result["coefficient_determinant"] == 6
    assert result["recovered_v"] == 3
    assert result["recovered_j"] == 1
    assert result["cramer_divisibilities_exact"]
    assert result["dual_slope_recovered_exactly"]


def test_transition_h_poisson_square_has_one_half_entry_saving_after_characters() -> None:
    adapter = getattr(
        coverage_audit,
        "transition_h_poisson_square_offdiagonal_audit",
        None,
    )
    assert adapter is not None, "transition square offdiagonal audit is missing"
    audit = adapter()
    assert audit.primitive_slope_pair_exponent == F(1)
    assert audit.inner_area_exponent == F(1)
    assert audit.expanded_square_cardinality_exponent == F(3)
    assert audit.identity_diagonal_exponent == F(2)
    assert audit.square_function_target_exponent == F(2)
    assert audit.required_offdiagonal_saving_exponent == F(1)
    assert audit.cross_determinant_max_exponent == F(1)
    assert audit.top_cokernel_character_exponent == F(1)
    assert audit.character_square_root_saving_exponent == F(1, 2)
    assert audit.remaining_mobius_entry_saving_exponent == F(1, 2)
    assert audit.zero_cross_determinant_is_identity_diagonal
    assert audit.nonzero_cross_determinant_recovers_unique_slope
    assert audit.cokernel_is_one_cyclic_character_family
    assert audit.signed_four_mobius_hecke_sum_required
    assert not audit.hybrid_mobius_hecke_estimate_proved
    assert not audit.critical_square_function_proved


def test_published_kloosterman_bounds_miss_the_transition_entry_gate() -> None:
    adapter = getattr(
        coverage_audit,
        "transition_published_kloosterman_entry_audit",
        None,
    )
    assert adapter is not None, "published transition Kloosterman audit is missing"
    audit = adapter()
    assert audit.modulus_exponent == F(1)
    assert audit.delta_interval_exponent == F(1, 2)
    assert audit.required_mobius_entry_saving_exponent == F(1, 2)
    assert audit.bp_uniform_saving_exponent == F(1, 32)
    assert audit.bp_uniform_deficit == F(15, 32)
    assert audit.mqw_uniform_saving_exponent == F(1, 100)
    assert audit.mqw_uniform_deficit == F(49, 100)
    assert audit.pascadi_factorable_saving_exponent == F(1, 12)
    assert audit.pascadi_factorable_deficit == F(5, 12)
    assert audit.optimistic_four_bp_applications_saving_exponent == F(1, 8)
    assert audit.optimistic_four_bp_deficit == F(3, 8)
    assert audit.bp_square_root_length_condition_holds
    assert audit.bp_arbitrary_sequences_allowed
    assert not audit.standard_kloosterman_kernel_verified
    assert not audit.coefficients_separate_from_matrix_entries
    assert not audit.fixed_modulus_before_entry_sum_verified
    assert not audit.pascadi_uniform_for_all_moduli
    assert not audit.published_coverage


def test_transition_delta_lattice_poisson_has_exact_dual_pairing() -> None:
    helper = getattr(
        coverage_audit,
        "transition_delta_lattice_dual_identity",
        None,
    )
    assert helper is not None, "transition delta-lattice helper is missing"

    result = helper(
        s1=5,
        w1=2,
        s2=7,
        w2=4,
        v=3,
        j=1,
        m1=2,
        m2=-1,
    )
    assert result["cross_determinant"] == -6
    assert result["coefficient_determinant"] == 6
    assert result["delta1"] == 1
    assert result["delta2"] == 5
    assert result["dual_numerator_1"] == -10
    assert result["dual_numerator_2"] == 8
    assert result["scaled_dual_pairing_numerator"] == 30
    assert result["dual_pairing_integer"] == 5
    assert result["poisson_covolume_exact"]
    assert result["dual_pairing_exact"]


def test_transition_delta_lattice_zero_mode_needs_one_power_on_every_shell() -> None:
    adapter = getattr(
        coverage_audit,
        "transition_delta_lattice_poisson_audit",
        None,
    )
    assert adapter is not None, "transition delta-lattice audit is missing"

    top = adapter(determinant_exponent=F(1))
    assert top.delta_box_area_exponent == F(1)
    assert top.primitive_divisor_exponent == F(0)
    assert top.lattice_covolume_exponent == F(1)
    assert top.zero_mode_density_exponent == F(0)
    assert top.entry_pair_shell_exponent == F(3)
    assert top.zero_mode_absolute_exponent == F(3)
    assert top.square_function_target_exponent == F(2)
    assert top.required_zero_mode_saving_exponent == F(1)
    assert top.longitudinal_dual_spacing_exponent == F(-1, 2)
    assert top.transverse_dual_spacing_exponent == F(1, 2)
    assert top.active_longitudinal_frequency_exponent == F(1, 2)
    assert top.active_transverse_frequency_exponent == F(0)
    assert top.weighted_active_longitudinal_exponent == F(1, 2)
    assert top.primitive_zero_mode_coefficient == (
        "sum_{d<=C_W*T^(1/2)} mu(d)/d^2"
    )
    assert top.primitive_euler_factor_tail_exponent == F(-1, 2)
    assert top.primitive_mobius_inversion_exact
    assert top.primitive_divisor_layers_do_not_worsen
    assert top.zero_mode_obstruction_independent_of_determinant_shell
    assert top.zero_mode_covolume_jacobian_cancels_exactly
    assert top.zero_mode_is_continuous_slope_gram
    assert top.full_zero_mode_gram_positive_semidefinite
    assert top.offdiagonal_is_full_gram_minus_identity_diagonal
    assert not top.kernel_alone_annihilates_zero_mode
    assert top.square_function_route_is_only_sufficient
    assert not top.zero_mode_weight_separates_in_the_entries
    assert not top.zero_mode_mobius_variance_proved
    assert not top.whole_delta_lattice_covered

    lower = adapter(determinant_exponent=F(3, 4))
    assert lower.zero_mode_density_exponent == F(1, 4)
    assert lower.entry_pair_shell_exponent == F(11, 4)
    assert lower.zero_mode_absolute_exponent == F(3)
    assert lower.required_zero_mode_saving_exponent == F(1)
    assert lower.transverse_dual_spacing_exponent == F(3, 4)

    largest_divisor = adapter(
        determinant_exponent=F(1),
        primitive_divisor_exponent=F(1, 2),
    )
    assert largest_divisor.longitudinal_dual_spacing_exponent == F(-1)
    assert largest_divisor.transverse_dual_spacing_exponent == F(0)
    assert largest_divisor.active_longitudinal_frequency_exponent == F(1)
    assert largest_divisor.primitive_divisor_weight_exponent == F(-1)
    assert largest_divisor.weighted_active_longitudinal_exponent == F(0)
    assert largest_divisor.primitive_divisor_layers_do_not_worsen


def test_transition_denominator_gcd_line_reduces_to_two_mobius_square_root() -> None:
    identity = getattr(
        coverage_audit,
        "transition_denominator_gcd_line_identity",
        None,
    )
    assert identity is not None, "denominator-gcd line helper is missing"
    result = identity(
        g=3,
        a=5,
        b=7,
        r1_base=3,
        r2_base=4,
        n=2,
    )
    assert result["s1"] == 15
    assert result["s2"] == 21
    assert result["r1"] == 13
    assert result["r2"] == 18
    assert result["h"] == 1
    assert result["cross_determinant"] == 3
    assert result["denominator_gcd_exact"]
    assert result["primitive_denominator_pair"]
    assert result["line_equation_exact"]

    adapter = getattr(
        coverage_audit,
        "transition_denominator_gcd_line_audit",
        None,
    )
    assert adapter is not None, "denominator-gcd line audit is missing"
    critical = adapter(
        determinant_exponent=F(1),
        denominator_gcd_exponent=F(1, 2),
    )
    assert critical.denominator_pair_exponent == F(3, 2)
    assert critical.determinant_quotient_exponent == F(1, 2)
    assert critical.line_parameter_exponent == F(1, 2)
    assert critical.raw_line_family_exponent == F(5, 2)
    assert critical.required_saving_exponent == F(1, 2)
    assert critical.two_denominator_mobius_length_exponent == F(1)
    assert critical.two_denominator_square_root_saving_exponent == F(1, 2)
    assert critical.post_square_root_exponent == F(2)
    assert critical.square_root_power_margin == F(0)
    assert critical.mobius_product_reduction_exact
    assert critical.top_determinant_is_unique_critical_face
    assert not critical.two_mobius_line_square_root_proved
    assert not critical.shell_covered

    lower = adapter(
        determinant_exponent=F(3, 4),
        denominator_gcd_exponent=F(1, 4),
    )
    assert lower.raw_line_family_exponent == F(5, 2)
    assert lower.required_saving_exponent == F(1, 2)
    assert lower.two_denominator_square_root_saving_exponent == F(3, 4)
    assert lower.post_square_root_exponent == F(7, 4)
    assert lower.square_root_power_margin == F(1, 4)
    assert not lower.top_determinant_is_unique_critical_face

    endpoint = adapter(
        determinant_exponent=F(3, 4),
        denominator_gcd_exponent=F(3, 4),
    )
    assert endpoint.required_saving_exponent == F(0)
    assert endpoint.absolute_count_reaches_target
    assert endpoint.shell_covered


def test_transition_denominator_type_ii_polytope_has_exact_completion_deficit() -> None:
    adapter = getattr(
        coverage_audit,
        "transition_denominator_mobius_type_ii_audit",
        None,
    )
    assert adapter is not None, "denominator Type-I/II audit is missing"

    all_signed = adapter(
        determinant_exponent=F(1),
        denominator_gcd_exponent=F(1, 2),
        left_short_mobius_exponent=F(1, 4),
        left_cutoff_divisor_exponent=F(1, 4),
        right_short_mobius_exponent=F(1, 4),
        right_cutoff_divisor_exponent=F(1, 4),
    )
    assert all_signed.denominator_cofactor_exponent == F(1, 2)
    assert all_signed.cutoff_exponent == F(1, 4)
    assert all_signed.left_unsigned_cofactor_exponent == F(0)
    assert all_signed.right_unsigned_cofactor_exponent == F(0)
    assert all_signed.signed_mobius_atom_volume_exponent == F(1)
    assert all_signed.signed_atom_square_root_saving_exponent == F(1, 2)
    assert all_signed.required_total_saving_exponent == F(1, 2)
    assert all_signed.remaining_completion_saving_exponent == F(0)
    assert all_signed.top_face_deficit_identity_exact
    assert all_signed.no_unsigned_completion_needed
    assert not all_signed.signed_atom_square_root_proved
    assert not all_signed.cell_closed_by_registered_bounds

    all_completion = adapter(
        determinant_exponent=F(1),
        denominator_gcd_exponent=F(1, 2),
        left_short_mobius_exponent=F(0),
        left_cutoff_divisor_exponent=F(0),
        right_short_mobius_exponent=F(0),
        right_cutoff_divisor_exponent=F(0),
    )
    assert all_completion.left_unsigned_cofactor_exponent == F(1, 2)
    assert all_completion.right_unsigned_cofactor_exponent == F(1, 2)
    assert all_completion.signed_mobius_atom_volume_exponent == F(0)
    assert all_completion.remaining_completion_saving_exponent == F(1, 2)
    assert all_completion.top_face_unsigned_half_volume_exponent == F(1, 2)
    assert all_completion.top_face_deficit_identity_exact
    assert not all_completion.no_unsigned_completion_needed
    assert not all_completion.unsigned_cofactor_completion_proved
    assert not all_completion.cell_closed_by_registered_bounds

    lower = adapter(
        determinant_exponent=F(3, 4),
        denominator_gcd_exponent=F(1, 4),
        left_short_mobius_exponent=F(0),
        left_cutoff_divisor_exponent=F(0),
        right_short_mobius_exponent=F(0),
        right_cutoff_divisor_exponent=F(0),
    )
    assert lower.denominator_cofactor_exponent == F(3, 4)
    assert lower.required_total_saving_exponent == F(1, 2)
    assert lower.top_face_unsigned_half_volume_exponent == F(3, 4)
    assert lower.off_top_power_margin_exponent == F(1, 4)
    assert lower.remaining_completion_saving_exponent == F(1, 2)
    assert lower.general_deficit_identity_exact
    assert not lower.top_face_deficit_identity_exact

    mixed = adapter(
        determinant_exponent=F(1),
        denominator_gcd_exponent=F(1, 2),
        left_short_mobius_exponent=F(1, 4),
        left_cutoff_divisor_exponent=F(0),
        right_short_mobius_exponent=F(0),
        right_cutoff_divisor_exponent=F(1, 4),
    )
    assert mixed.left_unsigned_cofactor_exponent == F(1, 4)
    assert mixed.right_unsigned_cofactor_exponent == F(1, 4)
    assert mixed.signed_atom_square_root_saving_exponent == F(1, 4)
    assert mixed.remaining_completion_saving_exponent == F(1, 4)
    assert mixed.top_face_deficit_identity_exact
    assert not mixed.cell_closed_by_registered_bounds


def test_bourgain_garaev_multilinear_theorems_do_not_close_balanced_cell() -> None:
    adapter = getattr(
        coverage_audit,
        "transition_bourgain_garaev_multilinear_audit",
        None,
    )
    assert adapter is not None, "Bourgain--Garaev audit is missing"
    audit = adapter()
    assert audit.modulus_exponent == F(1)
    assert audit.atom_interval_exponent == F(1, 4)
    assert audit.actual_multilinear_variable_count == 4
    assert audit.required_saving_exponent == F(1, 2)
    assert audit.theorem9_grouped_interval_exponent == F(1, 2)
    assert audit.theorem9_saving_exponent == F(1, 16)
    assert audit.theorem9_deficit == F(7, 16)
    assert audit.theorem10_k2_saving_exponent == F(1, 24)
    assert audit.theorem10_k2_deficit == F(11, 24)
    assert audit.theorem11_minimum_variable_count == 7
    assert audit.theorem11_product_length_condition_holds
    assert not audit.theorem11_variable_count_condition_holds
    # Section 10.4 proves the weaker constant C >= 144, but Remark 3 in the
    # published theorem statement says that Theorem 12 can be taken with
    # C = 4.  The adapter must use the strongest published statement while
    # retaining the proof constant as a separate provenance field.
    assert audit.theorem12_section10_4_proof_constant_lower_bound == 144
    assert audit.theorem12_published_constant == 4
    assert audit.theorem12_n4_threshold_exponent == F(1, 4)
    assert not audit.theorem12_length_condition_holds
    assert audit.theorem13_product_interval_exponent == F(1)
    assert audit.theorem13_threshold_exponent == F(1, 2)
    assert audit.theorem13_available_epsilon_margin == F(1, 2)
    assert audit.theorem13_product_condition_holds
    assert not audit.theorem13_saving_exponent_is_explicit
    assert not audit.theorem13_required_half_power_saving_certified
    assert audit.theorems_require_prime_modulus
    assert not audit.actual_determinant_moduli_all_prime
    assert not audit.grouped_product_sets_are_intervals
    assert not audit.actual_four_atom_weights_separate
    assert not audit.reciprocal_product_phase_verified
    assert not audit.published_coverage


def test_iterating_mobius_identity_does_not_force_seven_long_variables() -> None:
    adapter = getattr(
        coverage_audit,
        "transition_bourgain_garaev_iterated_factorization_audit",
        None,
    )
    assert adapter is not None, "iterated Bourgain--Garaev audit is missing"
    audit = adapter()
    assert audit.original_atom_exponent == F(1, 4)
    assert audit.desired_equal_subatom_count == 2
    assert audit.desired_subatom_exponent == F(1, 8)
    assert audit.formal_total_variable_count == 8
    assert audit.theorem11_minimum_variable_count == 7
    assert audit.formal_theorem11_count_condition_holds
    assert audit.formal_theorem11_product_condition_holds
    assert audit.theorem11_required_half_power_saving_certified is False
    # A prime in (p^(1/4), 2 p^(1/4)] has no factorization into two
    # p^(1/8)-scale integers.  The exact finite identity therefore has a
    # cell with one long unsigned cofactor and only unit signed factors.
    assert audit.prime_atom_has_balanced_two_factor_decomposition is False
    assert audit.iterated_identity_forces_seven_positive_length_variables is False
    assert audit.actual_phase_is_reciprocal_product is False
    assert audit.actual_moduli_all_prime is False
    assert audit.published_coverage is False


def test_mobius_hecke_euler_factor_is_a_zeta_and_l_reciprocal() -> None:
    coefficients = getattr(
        coverage_audit,
        "mobius_hecke_local_k_coefficients",
        None,
    )
    assert coefficients is not None, "Möbius--Hecke local factor is missing"
    # For lambda = 3, K_p(x) = 1 - 3 x^3 - 8 x^4 + O(x^5).
    assert coefficients(hecke_lambda=F(3), degree=4) == (
        F(1),
        F(0),
        F(0),
        F(-3),
        F(-8),
    )

    adapter = getattr(
        coverage_audit,
        "transition_mobius_hecke_reciprocal_l_audit",
        None,
    )
    assert adapter is not None, "Möbius--Hecke spectral audit is missing"
    audit = adapter()
    assert audit.local_factorization_exact
    assert audit.k_local_first_nontrivial_degree == 3
    assert audit.k_euler_product_absolutely_convergent_at_half
    assert audit.physical_spectral_line == F(1, 2)
    assert audit.required_mobius_saving_exponent == F(1, 2)
    assert not audit.actual_kuznetsov_reduction_derived
    assert not audit.reciprocal_l_negative_moment_proved
    assert not audit.required_half_power_saving_certified
    assert not audit.whole_line_family_covered

    balanced_coefficients = getattr(
        coverage_audit,
        "balanced_mobius_hecke_local_k_coefficients",
        None,
    )
    assert balanced_coefficients is not None, "balanced local factor is missing"
    assert balanced_coefficients(
        hecke_lambda=F(3),
        left_twist=F(2),
        right_twist=F(5),
        degree=3,
    ) == (F(1), F(0), F(0), F(-609))
    assert audit.balanced_two_factor_local_factorization_exact
    assert audit.balanced_reciprocal_l_factor_count == 2
    assert audit.balanced_zeta_factor_count == 3
    assert audit.balanced_k_local_first_nontrivial_degree == 3
    assert audit.classical_kuznetsov_hecke_index_is_shift
    assert audit.mobius_entries_are_not_classical_hecke_indices
    assert audit.balanced_factor_is_conditional_spectral_diagnostic


def test_exact_entry_weight_forces_primorial_relative_trace_level() -> None:
    adapter = getattr(
        coverage_audit,
        "transition_entry_weighted_relative_trace_audit",
        None,
    )
    assert adapter is not None, "entry-weighted relative-trace audit is missing"
    audit = adapter(prime_bound=7)
    assert audit.required_nonspherical_primes == (2, 3, 5, 7)
    assert audit.minimum_global_level == 210
    assert audit.minimum_global_level_is_primorial
    assert audit.local_spherical_vector_is_constant_on_primitive_columns
    assert audit.primitive_entry_weight_is_not_k_invariant
    assert audit.exact_squarefree_weight_needs_depth_two_for_small_primes
    assert audit.hecke_index_is_shift_not_entry
    assert audit.asymptotic_log_level_scale == F(1)
    assert not audit.polynomial_conductor_preserved
    assert not audit.published_entry_weighted_adapter
    assert not audit.whole_line_family_covered


def test_small_prime_spectral_hybrid_cannot_have_both_fixed_atoms_and_polynomial_level() -> None:
    adapter = getattr(
        coverage_audit,
        "transition_small_prime_spectral_hybrid_audit",
        None,
    )
    assert adapter is not None, "small-prime spectral hybrid audit is missing"
    audit = adapter(fixed_rough_factor_cap=7, polynomial_level_exponent=F(2))
    assert audit.fixed_rough_factor_cap == 7
    assert audit.fixed_cap_cutoff_exponent == F(1, 8)
    assert audit.polynomial_level_exponent == F(2)
    assert audit.logarithmic_cutoff_keeps_polynomial_level
    assert not audit.logarithmic_cutoff_forces_fixed_factor_count
    assert audit.fixed_factor_cutoff_has_superpolynomial_level
    assert audit.rough_density_power_saving_exponent == F(0)
    assert audit.required_saving_exponent == F(1, 2)
    assert audit.residual_power_deficit == F(1, 2)
    assert not audit.published_rough_cofactor_half_power_bound
    assert not audit.whole_line_family_covered


def test_general_mobius_cutoff_only_redistributes_the_critical_half_volume() -> None:
    adapter = getattr(
        coverage_audit,
        "transition_general_cutoff_line_gate_audit",
        None,
    )
    assert adapter is not None, "general-cutoff line-gate audit is missing"
    audit = adapter(
        determinant_exponent=F(1),
        denominator_gcd_exponent=F(1, 2),
        cutoff_ratio=F(2, 3),
        type_split_ratio=F(1, 4),
        left_cutoff_divisor_exponent=F(1, 3),
        left_short_mobius_exponent=F(1, 7),
        right_cutoff_divisor_exponent=F(1, 4),
        right_short_mobius_exponent=F(1, 8),
    )
    assert audit.cofactor_exponent == F(1, 2)
    assert audit.cutoff_exponent == F(1, 3)
    assert audit.type_split_exponent == F(1, 8)
    assert audit.left_unsigned_exponent == F(1, 42)
    assert audit.right_unsigned_exponent == F(1, 8)
    assert audit.signed_square_root_saving == F(143, 336)
    assert audit.unsigned_completion_saving == F(25, 336)
    assert audit.required_saving == F(1, 2)
    assert audit.total_hypothetical_saving == F(1, 2)
    assert audit.top_face_power_margin == F(0)
    assert audit.cutoff_independent_deficit_identity
    assert not audit.cutoff_choice_creates_positive_power_slack
    assert not audit.cell_closed_by_registered_bounds


def test_bblr_joint_quadratic_divisor_still_misses_the_hard_mobius_face() -> None:
    adapter = getattr(
        coverage_audit,
        "transition_bblr_quadratic_divisor_audit",
        None,
    )
    assert adapter is not None, "BBLR quadratic-divisor audit is missing"
    audit = adapter(
        denominator_gcd_exponent=F(0),
        left_signed_outer_exponent=F(0),
        right_signed_outer_exponent=F(0),
    )
    assert audit.cofactor_exponent == F(1)
    assert audit.side_product_exponent == F(2)
    assert audit.total_signed_outer_exponent == F(0)
    assert audit.maximum_signed_outer_exponent == F(0)
    assert audit.unsigned_pair_parameter_exponent == F(2)
    assert audit.shift_exponent == F(1)
    assert audit.frequency_parameter_exponent == F(1)
    assert not audit.sharp_error_formula_applicable
    assert audit.general_error_first_exponent == F(5, 2)
    assert audit.general_error_h_squared_exponent == F(2)
    assert audit.best_error_exponent == F(5, 2)
    assert audit.target_exponent == F(2)
    assert audit.best_error_power_margin == F(-1, 2)
    assert audit.hard_face_global_best_power_margin == F(-1, 2)
    assert audit.outer_slots_absorb_all_signed_atoms
    assert audit.remaining_slots_are_two_unsigned_factors_per_side
    assert audit.arbitrary_coefficients_allowed_only_in_outer_slots
    assert audit.independent_internal_smooth_weights_supported
    assert audit.side_product_balance_verified
    assert audit.outer_coefficient_divisor_bound_verified
    assert audit.proposition_3_1_hypotheses_verified
    assert not audit.four_main_terms_cancelled_after_mobius_recombination
    assert not audit.published_theorem_closes_cell


def test_bblr_sharp_error_can_save_power_before_its_main_terms_are_cancelled() -> None:
    adapter = getattr(
        coverage_audit,
        "transition_bblr_quadratic_divisor_audit",
        None,
    )
    assert adapter is not None, "BBLR quadratic-divisor audit is missing"
    audit = adapter(
        denominator_gcd_exponent=F(4, 5),
        left_signed_outer_exponent=F(1, 5),
        right_signed_outer_exponent=F(1, 5),
    )
    assert audit.cofactor_exponent == F(1, 5)
    assert audit.side_product_exponent == F(6, 5)
    assert audit.total_signed_outer_exponent == F(2, 5)
    assert audit.unsigned_pair_parameter_exponent == F(1)
    assert audit.sharp_error_formula_applicable
    assert audit.sharp_error_ab_exponent == F(11, 10)
    assert audit.sharp_error_watt_exponent == F(23, 20)
    assert audit.sharp_error_exponent == F(23, 20)
    assert audit.target_exponent == F(6, 5)
    assert audit.best_error_exponent == F(23, 20)
    assert audit.best_error_power_margin == F(1, 20)
    assert not audit.four_main_terms_cancelled_after_mobius_recombination
    assert not audit.published_theorem_closes_cell


def test_bblr_uncompressed_lemma_keeps_the_half_power_unsigned_deficit() -> None:
    adapter = getattr(
        coverage_audit,
        "transition_bblr_hard_unsigned_cell_audit",
        None,
    )
    assert adapter is not None, "BBLR hard unsigned-cell audit is missing"

    bottom = adapter(poisson_gcd_exponent=F(0))
    assert bottom.outer_a_exponent == bottom.outer_b_exponent == F(0)
    assert bottom.m1_exponent == bottom.m2_exponent == F(1)
    assert bottom.n1_exponent == bottom.n2_exponent == F(1)
    assert bottom.shift_exponent == F(1)
    assert bottom.lemma_3_1_z_exponent == F(5, 2)
    assert bottom.x_interval_exponent == F(0)
    assert bottom.poisson_gcd_count_exponent == F(0)
    assert bottom.dyadic_layer_exponent == F(5, 2)
    assert bottom.global_error_exponent == F(5, 2)
    assert bottom.target_exponent == F(2)
    assert bottom.power_margin == F(-1, 2)
    assert bottom.one_mobius_pure_unsigned_coefficient == -1
    assert bottom.four_mobius_pure_unsigned_coefficient == 1
    assert not bottom.cellwise_mobius_cancellation_available
    assert bottom.cross_outer_scale_recombination_required
    assert not bottom.uncompressed_lemma_improves_proposition_bound

    top = adapter(poisson_gcd_exponent=F(1))
    assert top.lemma_3_1_z_exponent == F(-1)
    assert top.x_interval_exponent == F(1)
    assert top.poisson_gcd_count_exponent == F(1)
    assert top.dyadic_layer_exponent == F(1)
    assert top.initial_h_squared_error_exponent == F(2)
    assert top.global_error_exponent == F(5, 2)


def test_banks_shparlinski_multiple_mobius_bound_does_not_save_a_slope_power() -> None:
    adapter = getattr(
        coverage_audit,
        "transition_banks_shparlinski_pre_cauchy_audit",
        None,
    )
    assert adapter is not None, "Banks--Shparlinski pre-Cauchy audit is missing"
    audit = adapter()
    assert audit.entry_scale_exponent == F(1)
    assert audit.dual_v_exponent == audit.dual_j_exponent == F(1, 2)
    assert audit.fixed_slope_family_exponent == F(1)
    assert audit.shift_variable_exponent == F(1, 2)
    assert audit.fixed_slope_geometric_count_exponent == F(1)
    assert audit.best_theorem_role_bound_exponent == F(3, 2)
    assert audit.best_fixed_slope_bound_exponent == F(1)
    assert audit.h_poisson_factor_exponent == F(1, 2)
    assert audit.aggregated_exponent == F(5, 2)
    assert audit.target_exponent == F(2)
    assert audit.power_margin == F(-1, 2)
    assert audit.short_interval_threshold_exponent == F(5, 8)
    assert audit.actual_short_interval_exponent == F(1, 2)
    assert audit.short_interval_threshold_margin == F(-1, 8)
    assert audit.additive_theorem_requires_fixing_both_bilinear_slopes
    assert audit.original_shift_has_no_mobius_weight
    assert audit.divisor_convolution_can_insert_the_missing_mobius_weight
    assert not audit.divisor_convolution_creates_power_saving
    assert not audit.all_actual_kernel_hypotheses_verified
    assert not audit.published_theorem_closes_pre_cauchy_sum
    assert audit.source == (
        "Banks--Shparlinski, arXiv:2506.08787v1, "
        "Theorems 2.1 and 2.4"
    )


def test_ramare_squarefree_identity_extracts_each_available_band_prime() -> None:
    helper = getattr(
        coverage_audit,
        "transition_ramare_squarefree_identity",
        None,
    )
    assert helper is not None, "Ramaré squarefree identity helper is missing"

    composite = helper(n=30, prime_lower=2, prime_upper=5)
    assert composite["mobius_value"] == -1
    assert composite["band_prime_divisors"] == (2, 3, 5)
    assert composite["band_prime_divisor_count"] == 3
    assert composite["cofactor_mobius_sum"] == 3
    assert composite["ramare_value"] == F(-1)
    assert composite["identity_exact"]

    prime_outside = helper(n=101, prime_lower=2, prime_upper=11)
    assert prime_outside["band_prime_divisors"] == ()
    assert prime_outside["ramare_value"] is None
    assert not prime_outside["identity_applies"]

    prime_inside = helper(n=101, prime_lower=2, prime_upper=101)
    assert prime_inside["band_prime_divisors"] == (101,)
    assert prime_inside["cofactor_mobius_sum"] == 1
    assert prime_inside["ramare_value"] == F(-1)
    assert prime_inside["minimum_positive_length_factor_count"] == 1
    assert prime_inside["identity_exact"]


def test_ramare_medium_prime_band_cannot_force_multilinearity() -> None:
    adapter = getattr(
        coverage_audit,
        "transition_ramare_medium_prime_audit",
        None,
    )
    assert adapter is not None, "Ramaré medium-prime audit is missing"

    proper = adapter(
        entry_exponent=F(1),
        band_lower_exponent=F(1, 4),
        band_upper_exponent=F(3, 4),
    )
    assert proper.required_line_saving_exponent == F(1)
    assert proper.prime_exceptional_set_exponent == F(1)
    assert proper.prime_exceptional_log_density_saving == F(1)
    assert proper.prime_exceptional_power_density_saving == F(0)
    assert proper.uncovered_power_deficit == F(1)
    assert not proper.band_reaches_entry_scale
    assert proper.proper_band_leaves_prime_sector_exceptional
    assert not proper.prime_sector_is_in_ramare_sum
    assert not proper.forces_two_positive_length_factors
    assert not proper.ramare_decomposition_closes_line_gate

    full = adapter(
        entry_exponent=F(1),
        band_lower_exponent=F(1, 4),
        band_upper_exponent=F(1),
    )
    assert full.band_reaches_entry_scale
    assert full.prime_sector_is_in_ramare_sum
    assert full.prime_exceptional_set_exponent == F(0)
    assert full.prime_exceptional_log_density_saving == F(0)
    assert full.prime_sector_extracted_factor_exponent == F(1)
    assert full.prime_sector_cofactor_exponent == F(0)
    assert full.prime_sector_positive_length_factor_count == 1
    assert not full.proper_band_leaves_prime_sector_exceptional
    assert not full.forces_two_positive_length_factors
    assert not full.ramare_decomposition_closes_line_gate


def test_prime_kloosterman_results_leave_an_explicit_half_power_deficit() -> None:
    adapter = getattr(
        coverage_audit,
        "transition_prime_kloosterman_audit",
        None,
    )
    assert adapter is not None, "prime-Kloosterman audit is missing"
    audit = adapter()
    assert audit.modulus_exponent == F(1)
    assert audit.prime_interval_exponent == F(1)
    assert audit.required_saving_exponent == F(1, 2)
    assert audit.unrestricted_prime_bound_exponent == F(17, 18)
    assert audit.unrestricted_prime_saving_exponent == F(1, 18)
    assert audit.progression_prime_bound_exponent == F(191, 192)
    assert audit.progression_prime_saving_exponent == F(1, 192)
    assert audit.progression_modulus_cap_exponent == F(1, 100)
    assert audit.optimistic_four_unrestricted_saving_exponent == F(2, 9)
    assert audit.optimistic_four_unrestricted_deficit == F(5, 18)
    assert audit.optimistic_four_progression_saving_exponent == F(1, 48)
    assert audit.optimistic_four_progression_deficit == F(23, 48)
    assert audit.published_theorem_has_fixed_prime_modulus
    assert not audit.actual_determinant_moduli_all_prime
    assert not audit.standard_single_kloosterman_argument_verified
    assert not audit.other_entry_weights_separate
    assert not audit.published_theorem_closes_prime_sector


def test_poisson_exchange_reciprocity_is_exact_but_does_not_force_reality() -> None:
    helper = getattr(
        coverage_audit,
        "poisson_exchange_reciprocity_identity",
        None,
    )
    assert helper is not None, "Poisson exchange-reciprocity helper is missing"
    for r, s, h, delta in (
        (5, 7, 3, 2),
        (11, 13, -4, 9),
        (17, 19, 8, -5),
    ):
        exact = helper(r=r, s=s, h=h, delta=delta)
        assert exact["primitive_pair"]
        assert exact["reciprocity_phase_exact"]
        assert exact["swapped_full_poisson_term_is_conjugate"]

    adapter = getattr(
        coverage_audit,
        "poisson_exchange_second_order_audit",
        None,
    )
    assert adapter is not None, "Poisson exchange second-order audit is missing"
    audit = adapter()
    assert audit.physical_shifted_sum_swap_is_conjugate
    assert audit.poisson_modulus_changes_under_swap
    assert audit.reciprocity_correction_retained
    assert audit.full_poisson_term_swap_is_conjugate
    assert not audit.completed_coefficient_forced_real
    assert audit.imaginary_coefficient_has_linear_centered_term
    assert audit.second_order_bound_requires_real_coefficient
    assert not audit.second_order_collar_unconditional


def test_centered_conjugate_pair_has_a_linear_imaginary_coefficient_term() -> None:
    helper = getattr(
        coverage_audit,
        "centered_conjugate_pair_taylor_coefficients",
        None,
    )
    assert helper is not None, "centered conjugate-pair helper is missing"
    generic = helper(real_part=F(2), imaginary_part=F(3))
    assert generic["constant_coefficient"] == F(0)
    assert generic["linear_coefficient_in_2pi_x"] == F(-6)
    assert generic["quadratic_coefficient_in_2pi_x"] == F(-2)
    assert not generic["second_order_zero"]

    real = helper(real_part=F(2), imaginary_part=F(0))
    assert real["linear_coefficient_in_2pi_x"] == F(0)
    assert real["second_order_zero"]


def test_exchange_symmetry_audit_is_documented_and_reported(
    capsys: pytest.CaptureFixture[str],
) -> None:
    note = Path(
        "docs/research/2026-08-25-mwkf-alternative-routes-spike.md"
    ).read_text()
    for marker in (
        "### 4.73 Exact exchange symmetry does not square the centered collar",
        "\\tag{4.642}",
        "\\tag{4.646}",
        "second_order_collar_unconditional=False",
        "### 4.74 Common-modulus completion recovers two disjoint sublattices",
        "\\tag{4.653}",
        "\\tag{4.655}",
        "common_modulus_forces_real_completed_coefficient=False",
        "### 4.75 Midpoint gauge gives a nondegenerate Hermitian completion",
        "\\tag{4.661}",
        "\\tag{4.663a}",
        r"\frac{HL}{2RS}\mathfrak H_q[\Psi]",
        "\\tag{4.665}",
        "midpoint_hermitian_published_bound=False",
        "### 4.76 Exact Salié-phase match does not satisfy the published adapter",
        "\\tag{4.666}",
        "withdrawn_claim_closes_midpoint_gate=False",
        "### 4.77 Unitary-divisor roots collapse the two Möbius weights",
        "\\tag{4.670}",
        "\\tag{4.673}",
        "unitary_root_trace_bound_verified=False",
        "### 4.78 Root-Farey large sieve leaves the same deficit in both gauges",
        "\\tag{4.676}",
        "\\tag{4.678}",
        "root_farey_large_sieve_closes_gate=False",
        "### 4.79 Root CRT exposes the exact Möbius Type-II kernel",
        "\\tag{4.680}",
        "\\tag{4.683}",
        "k:=-h\\delta",
        "completed_centering_exact=True",
        "physical_zero_residue_vanishes=True",
        "physical_centered_subtraction_present=False",
        "root_type_ii_bound_verified=False",
        "### 4.80 Root fibers unfold to four classical fraction variables",
        "\\tag{4.685}",
        "\\tag{4.687}",
        "four_factor_type_ii_bound_verified=False",
        "### 4.81 One physical Poisson step gives the exact resonance lattice",
        "\\tag{4.691}",
        "\\tag{4.693}",
        "\\tag{4.694}",
        "physical_poisson_route_is_independent=False",
        "outer_mobius_square_root_verified=False",
        "### 4.82 Full root trace is a Salié sum but the adapter is nonuniform",
        "\\tag{4.696}",
        "\\tag{4.698}",
        "salie_adapter_closes_root_gate=False",
        "### 4.83 Joint Salié averaging is the existing BCR endpoint",
        "\\tag{4.701}",
        "\\tag{4.703}",
        "balanced_root_filter_excludes_dfi_square_main=True",
        "### 4.84 Quadratic Gauss completion linearizes the square numerator",
        "\\tag{4.705}",
        "\\tag{4.707}",
        "gauss_completion_improves_square_sector=False",
        "### 4.85 The sufficient Möbius fourth moment is one shifted determinant gate",
        "\\tag{4.708}",
        "\\tag{4.711}",
        "shifted_mobius_determinant_bound_proved=False",
        "### 4.86 The smooth determinant-surface theorem does not accept the Möbius gate",
        "\\tag{4.712}",
        "\\tag{4.715}",
        "ganguly_guria_route_closes_mobius_gate=False",
        "### 4.87 Published short-interval variance classes exclude the restricted inverse-zeta square",
        "\\tag{4.716}",
        "\\tag{4.719}",
        "darbar_das_route_closes_mobius_gate=False",
        "### 4.88 Ratio Mellin inversion restores a multiplicative inverse-zeta family",
        "\\tag{4.720}",
        "\\tag{4.723a}",
        "\\tag{4.723c}",
        "\\tag{4.725}",
        "shifted_inverse_zeta_variance_proved=False",
        "### 4.89 Published additive twists of $\\mu*\\mu$ miss the local variance scale",
        "\\tag{4.726}",
        "\\tag{4.730}",
        "brz_direct_pointwise_route_closes_variance_gate=False",
        "### 4.90 The uniform inverse-zeta variance gate would prove a new zero-free strip",
        "\\tag{4.731}",
        "\\tag{4.734}",
        "inverse_zeta_variance_gate_available_unconditionally=False",
        "### 4.91 A second Poisson step closes the BBLR all-unsigned hard box at power level",
        "\\tag{4.735}",
        "\\tag{4.739}",
        "all_unsigned_hard_box_power_closed=True",
        "whole_signed_hard_face_covered=False",
        "### 4.92 The signed hard face reduces to one outer-scale parameter",
        "\\tag{4.740}",
        "\\tag{4.744}",
        "published_bblr_power_coverage_upper=1/4",
        "signed_residual_lower_exponent=1/4",
        "### 4.93 Exact signed-atom convolution collapses only for product-compatible weights",
        "\\tag{4.745}",
        "\\tag{4.748}",
        "signed_dual_product_collapse_exact=True",
        "actual_transformed_weight_product_compatible=False",
        "### 4.94 The collapsed model isolates a coupled ratio-Mellin Type-II gate",
        "\\tag{4.749}",
        "\\tag{4.753}",
        "quotient_mobius_prevents_direct_bv=True",
        "coupled_ratio_mellin_type_ii_bound_proved=False",
        "### 4.95 Four cross-coprimality allocations make the collapsed superposition exact",
        "\\tag{4.754}",
        "\\tag{4.757}",
        "four_variable_superposition_exact=True",
        "collapsed_coefficients_independent_of_long_variables=True",
        "### 4.96 The equal-product face contains an ordinary two-point Chowla correlation",
        "\\tag{4.758}",
        "\\tag{4.761}",
        "equal_collapsed_product_face_present=True",
        "uniform_ratio_frequency_triangle_gate_admissible=False",
        "### 4.97 Physical ratio recombination does not annihilate the primitive equal face",
        "\\tag{4.762}",
        "\\tag{4.765}",
        "primitive_equal_face_coefficient_can_be_nonzero=True",
        "arbitrary_smooth_weight_enlargement_admissible=False",
        "### 4.98 Gcd layers expose the centered coupled-dispersion scale",
        "\\tag{4.766}",
        "\\tag{4.770}",
        "required_saving_exponent=s-gamma",
        "fixed_affine_chowla_must_remain_inside_g_sum=True",
        "### 4.99 Primitive refactorization closes the top equal-product face",
        "\\tag{4.771}",
        "\\tag{4.775}",
        "top_equal_product_face_closed_unconditionally=True",
        "### 4.100 The same outer PNT closes every fixed polylog gcd collar",
        "\\tag{4.776}",
        "\\tag{4.780}",
        "polylog_gcd_collar_closed_unconditionally=True",
        "### 4.101 The strict-power residual is one exact three-block Type-II gate",
        "\\tag{4.781}",
        "\\tag{4.785}",
        "unsigned_reduced_block_exponent=delta",
        "### 4.102 Convolution makes BBLR legal, but Cauchy recreates the raw-scale grouped diagonal",
        "\\tag{4.786}",
        "\\tag{4.795}",
        "near_frequency_type_ii_proved=False",
        "### 4.103 The inherited ratio-Mellin kernel has zero power bandwidth",
        "\\tag{4.796}",
        "\\tag{4.800}",
        "ratio_mellin_supplies_required_delta_saving=False",
        "### 4.104 Double Poisson exposes a resonance but absolute summation enlarges the deficit",
        "\\tag{4.801}",
        "\\tag{4.805}",
        "\\tag{4.806}",
        "\\tag{4.809}",
        "absolute_double_poisson_route_covered=False",
        "double_poisson_improves_bblr=False",
    ):
        assert marker in note

    coverage_audit.main()
    report = capsys.readouterr().out
    assert (
        "mwkf_final: status=analytic remainder gate open "
        "theta=3 main=4/3 residual_cells=1 remainder_o_T=False"
    ) in report
    assert (
        "large_q_transition: poisson_exchange_second_order="
        "shift_conjugate=True,modulus_changes=True,"
        "reciprocity_correction=True,full_conjugate=True,"
        "coefficient_real=False,linear_imaginary=True,"
        "real_required=True,second_order=False"
    ) in report
    assert (
        "large_q_transition: common_modulus_exchange="
        "Q=6,craw=7/2,vraw=7/2,original_divisor=3,"
        "swapped_divisor=3,creduced=1/2,vreduced=1/2,"
        "r_lattice=True,s_lattice=True,nonzero_intersection=False,"
        "centered_zero=True,coefficient_real=False,"
        "conductor_reduced=False,second_order=False"
    ) in report
    assert (
        "large_q_transition: midpoint_hermitian_completion="
        "Q=6,craw=7/2,vraw=7/2,ambient=13,prefactor=-1,"
        "target=7,sqrt=13/2,allowance=1/2,unit=True,involution=True,"
        "swap_negates=True,same_frequency=True,row_centered=True,"
        "column_centered=True,small_phase=False,published=False"
    ) in report
    assert (
        "large_q_transition: midpoint_published_hermitian_adapter="
        "numerator=7,rs_trivial=6,claimed_inner=6,claimed_save=0,"
        "bulk_claimed_inner=23/4,bulk_save=1/4,fixed_numerator=False,"
        "separated=False,frequency_average=False,withdrawn=True,"
        "corrected_improved=False,closes=False"
    ) in report
    assert (
        "large_q_transition: midpoint_unitary_divisor="
        "n=6,Q=6,physical_numerator=5,dual_numerator=7,"
        "factorization_root_bijection=True,mobius_collapses=True,"
        "root_count_subpower=True,balanced_filter=True,joint=True,"
        "published=False"
    ) in report
    assert (
        "large_q_transition: root_farey_large_sieve="
        "points=6,denominator=6,spacing_reciprocal=12,"
        "physical_numerator=5,physical_energy=5,physical_bound=23/2,"
        "physical_target=6,physical_deficit=11/2,dual_numerator=7,"
        "dual_energy=7,dual_bound=25/2,dual_target=7,dual_deficit=11/2,"
        "injective=True,reduced=True,separated=False,closes=False"
    ) in report
    assert (
        "large_q_transition: root_type_ii="
        "product=6,left=3,right=3,physical_numerator=5,dual_numerator=7,"
        "crt=True,reciprocal_split=True,left_cU=True,right_mu=True,"
        "root_fibers_subpower=True,completed_centering=True,zero_residue=True,"
        "physical_subtraction=False,fixed_numerator=False,joint=True,"
        "published=False"
    ) in report
    assert (
        "large_q_transition: root_four_factor="
        "left_product=3,right_product=3,physical_numerator=5,"
        "r=3,s=3,roots_unfold=True,pairwise=True,left_cU=True,"
        "right_mu_splits=True,phase=True,completed_centering=True,"
        "zero_residue=True,physical_subtraction=False,extreme_hard=True,joint=True,"
        "published=False"
    ) in report
    assert (
        "large_q_transition: midpoint_physical_poisson="
        "Q=6,h=5/2,delta=5/2,resonance=7/2,lattice=1/2,"
        "pointwise=3,raw=5,physical_save=2,outer_points=6,"
        "outer_target=6,outer_required_save=3,lattice_exact=True,"
        "poisson_exact=True,joint_derivatives=True,determinant_line=True,"
        "independent=False,outer_sqrt=False"
    ) in report
    assert (
        "large_q_transition: root_salie_adapter="
        "modulus=6,numerator=5,fixed_k_bound=351/59,fixed_k_save=3/59,"
        "summed_k_bound=646/59,target=6,deficit=292/59,"
        "odd_trace_exact=True,even_branch=False,balanced_filter=False,"
        "mobius_modulus=False,fixed_numerator=False,square_exception=False,"
        "joint=False,closes=False"
    ) in report
    assert (
        "large_q_transition: root_salie_joint="
        "m=3,n=3,numerator=5,bc1=101/10,bc2=85/8,bound=85/8,"
        "target=6,deficit=37/8,square_pairs=5/2,dfi_y=7/5,"
        "dfi_z=174/59,balanced=3,fixed_square=95/16,"
        "square_bound=135/16,square_deficit=39/16,phase=True,"
        "bcr_endpoint=True,mobius_coefficients=True,mobius_beyond_l2=False,"
        "dfi_main_excluded=True,closes=False"
    ) in report
    assert (
        "large_q_transition: square_salie_gauss="
        "r=3,s=3,t=5/2,x=3,y=3,normalization=-3,resonance=7/2,"
        "localized_pointwise=3,direct_square=5/2,identity=True,"
        "character_mod8=True,t_linear=True,joint=True,improves=False,"
        "closes=False"
    ) in report
    assert (
        "large_q_transition: mobius_product_shifted_variance="
        "factor=1,product=2,shift=1,diagonal_power=0,diagonal_log=1,"
        "raw_offdiag=3,target=2,required=1,convolution=True,"
        "diagonal=True,tail=True,collar=True,m4_equivalent=True,bound=False,"
        "original_requires=False,closes=False"
    ) in report
    assert (
        "large_q_transition: ganguly_guria_determinant="
        "X=1,shift=1,theta=7/64,fixed_error=71/64,"
        "absolute_shift_sum=135/64,target=2,deficit=7/64,"
        "fixed_main=2,absolute_main=3,smooth=True,distinct=False,"
        "arithmetic=False,coefficient_uniform=False,type_i_ii=False,"
        "ramanujan_power=True,ramanujan_log=False,main_cancel=False,"
        "closes=False"
    ) in report
    assert (
        "large_q_transition: darbar_das_short_variance="
        "ambient=2,window=1,generic_variance=4,target_variance=3,"
        "required=1,full_series_zeta_power=-2,auxiliary_zeta_power=-3,"
        "h_p=-3,h_p2=3,h_p3=-1,m_class=False,g_class=False,"
        "restricted_multiplicative=False,full_convolution=False,"
        "restricted_convolution=False,closes=False"
    ) in report
    assert (
        "large_q_transition: restricted_mobius_ratio_mellin="
        "factor=1,product=2,window=1,variance_target=3,"
        "ratio_coordinates=True,inversion=True,multiplicative=True,"
        "dirichlet_series=True,outer_smooth=True,tau_decay=True,"
        "tau_uniform_sufficient=True,tau_zero_full=True,tau_zero_pole=4,"
        "diag_log=3,target_log=1,excess=2,euler_no_p=True,euler_half=True,"
        "needs_offdiag=True,diagonal_lower=False,diagonal_disproves=False,"
        "joint_diag_log1=True,mangerel=4,"
        "mangerel_deficit=1,mangerel_log=True,tau_hypotheses=False,"
        "published=False,closes=False"
    ) in report
    assert (
        "large_q_transition: brz_mobius_convolution="
        "ambient=1,window=1/2,critical_q=1/2,term1=16/17,"
        "term2=11/12,term3=15/16,best=16/17,required=1/2,"
        "pointwise_deficit=15/34,local_variance=81/34,"
        "variance_target=3/2,variance_deficit=15/17,"
        "major_variance=2,major_deficit=1/2,published=True,"
        "twisted=False,local_l2=False,closes=False"
    ) in report
    assert (
        "large_q_transition: mrtt_signed_mobius_power_shift="
        "ambient=2,shift=1,relative=1/2,long_threshold=8/33,"
        "delta_threshold=8/25,published_long=True,identity=True,d2=True,"
        "ramare=True,major=True,typical_verified=False,fixed_power=True,"
        "average_exponent=3,required_exponent=2,power_deficit=1,"
        "scale_closes=False,ratio_family=False,product_vertex=False,"
        "physical=False,core=False"
    ) in report
    assert (
        "large_q_transition: hard_vertex_four_mobius="
        "ambient=2,shift=1,gcd=1/2,primitive=1/2,"
        "shift_quotient=1/2,line=1/2,raw=5/2,target=2,"
        "required=1/2,outer_sqrt=1/2,shift_full=1/2,"
        "unimodular=True,critical=True,mrtt_log_only=True,"
        "top_chowla=False,top_log=False,published_spectral=False,"
        "physical=False,proved=False"
    ) in report
    assert (
        "large_q_transition: blomer_milicevic_mobius_modulus="
        "modulus=3,period=3,l2=3/2,theta=7/64,"
        "base=69/32,total=117/32,trivial=3,deficit=21/32,"
        "selberg=227/64,selberg_deficit=35/64,ramanujan=3,"
        "ramanujan_margin=0,linnik=True,injective=True,"
        "parseval=True,small_period_ruled_out=False,qct_complete=False,"
        "power_saving=False,covered=False"
    ) in report
    assert (
        "large_q_transition: blomer_milicevic_type_i_level="
        "modulus=3,numerator=5,target=2,level=1,theta=7/64,"
        "fixed=69/32,type_i=101/32,type_i_deficit=37/32,"
        "ideal_cauchy=85/32,ideal_deficit=21/32,"
        "type_i_threshold=-5/32,cauchy_threshold=-5/16,"
        "type_i_window=False,cauchy_window=False,selberg_fixed=131/64,"
        "selberg_type_i_threshold=-3/64,selberg_cauchy_threshold=-3/32,"
        "selberg_endpoint=163/64,selberg_deficit=35/64,"
        "ramanujan_fixed=3/2,ramanujan_type_i_threshold=1/2,"
        "ramanujan_cauchy_threshold=1,ramanujan_endpoint=2,"
        "ramanujan_margin=0,linnik=True,"
        "divisibility=True,identity=True,exceptional_removed=False,"
        "cauchy_proved=False,model_only=True,physical=False,covered=False"
    ) in report
    assert (
        "large_q_transition: humphries_exceptional_level_density="
        "modulus=3,numerator=5,bessel_ratio=1,target=2,level=1,"
        "theta=7/64,slope=4,count=9/16,normalized=-7/16,"
        "ramanujan_base=2,finite_hecke=35/64,residual=0,"
        "total=163/64,deficit=35/64,target_level_max=1,neutral_level=1/4,"
        "compatible=True,archimedean_neutral=True,linnik_level=True,"
        "positive=True,mobius_signs=False,"
        "qct_weights=False,exceptional_covered=False,covered=False"
    ) in report
    assert (
        "large_q_transition: finite_prime_hecke_average="
        "modulus=3,left=5/2,right=5/2,numerator=5,level=1,target=2,"
        "theta=7/64,ramanujan_base=2,pointwise_loss=35/64,"
        "pointwise_total=163/64,pointwise_deficit=35/64,"
        "fixed_ls_loss=3/2,fixed_ls_total=7/2,required_saving=35/64,"
        "log=True,pascadi_arch=True,pascadi_finite=False,"
        "entry_adapter=False,physical=False,hecke_covered=False,covered=False"
    ) in report
    assert (
        "large_q_transition: farey_dilate_pre_cauchy="
        "entry=3,shift=5/2,left=1/2,right=1/2,gate=3499/1000,"
        "arc=5/2,left_arc=-2,right_arc=-2,energy=3,"
        "left_bandwidth=1/2,right_bandwidth=1/2,"
        "left_local_l2=7/2,right_local_l2=7/2,"
        "left_self=7/2,right_self=7/2,left_cauchy=7,right_cauchy=7,"
        "separate=7,separate_deficit=7/2,ideal=7/2,"
        "ideal_deficit=1/1000,endpoint=7/2,endpoint_reached=True,"
        "window_lost=True,shift_zero=True,self_removed=False,"
        "extra_saving=True,published=False,physical=False,covered=False"
    ) in report
    assert (
        "large_q_transition: farey_dilate_convolution_poisson="
        "entry=3,dilate=1/2,shift=5/2,gate=3499/1000,product=7/2,"
        "semiprime=7/2,numerator=1/2,packet=-7/2,determinant=5/2,"
        "determinant_match=True,complete_epsilon=True,dyadic_complete=False,"
        "semiprime_survives=True,equal_products_removed=True,"
        "cauchy_energy=True,poisson_loop=True,convolution_saving=False,"
        "physical=False,covered=False"
    ) in report
    assert (
        "large_q_transition: smooth_hecke_product_mobius="
        "left=5/2,right=5/2,product=5,conductor=1,theta=7/64,"
        "pointwise_loss=35/64,split=3/2,small=5/2,large=7/2,"
        "saving=3/2,log=True,hecke_identity=True,entire=True,"
        "functional_equation=True,rankin_pnt=True,pointwise_removed=True,"
        "eisenstein_separate=True,ramified_newform=True,oldclass=False,physical=False,"
        "finite_gate=False,covered=False"
    ) in report
    assert (
        "large_q_transition: smooth_hecke_oldclass_product="
        "index=5/2,level=1,theta=7/64,split=3/2,"
        "newform_endpoint=7/2,oldclass_slope=57/64,"
        "worst_endpoint=7/2,worst_at_newform=True,bm_formula=True,"
        "first_coprime=True,divisors_subpower=True,pnt_log=True,"
        "ramified=True,product_model=True,physical=False,"
        "finite_gate=False,covered=False"
    ) in report
    assert (
        "large_q_transition: physical_qct_hecke_kernel="
        "left=5/2,right=5/2,level=1,theta=7/64,qct_dim=4,"
        "augmented_dim=5,derivative_slope=8,contour=-1/2,"
        "exceptional_order=7/32,contour_margin=9/32,conductor=1,"
        "bandwidth=0,fourier_exact=True,nuclear_polylog=True,"
        "j_mellin=True,k_mellin=True,product=True,maass_tail=True,"
        "holo_tail=True,exceptional_inside=True,product_lemma=True,"
        "oldclass=True,kernel_model=True,qct_adapter=False,"
        "other_entries=False,level_family=False,finite_gate=False,"
        "covered=False"
    ) in report
    assert (
        "large_q_transition: type_i_atkin_lehner_cusp="
        "entry=3,modulus=3,product=5,entry_divisor=1/2,"
        "modulus_divisor=1/2,quotient=5/2,dual=1/2,level=1,"
        "rejected_cusp_modulus=13/4,lifted_modulus=7/2,"
        "bessel_numerator=6,bessel_ratio=1,"
        "poisson_norm=-1/2,lifted_prefactor=3,dual_l1=0,unweighted=True,"
        "coprime_divisors=True,allowed_moduli=True,kloosterman=False,"
        "inverse_obstruction=True,crt_lift=True,ramanujan_nonzero=True,"
        "coprime_level_family=True,"
        "newform_sign=True,oldclass_permuted=True,zero_eisenstein=True,"
        "raw_dual_l1=True,dual_no_power=False,physical=True,qct_adapter=False,"
        "standard_qct_adapter=True,"
        "level_family=False,type_ii=False,finite_gate=False,covered=False"
    ) in report
    assert (
        "large_q_transition: newform_level_mobius_projector="
        "prime=5,index=6,mobius=-2,newform=-1/6,difference=-11/6,"
        "geometric=True,squarefree=True,oldclass_tail=True,"
        "hecke_modified=True,match=False,projector=False,"
        "oldforms_killed=False,qct=False,covered=False"
    ) in report
    assert (
        "large_q_transition: robles_four_mobius_minor_arc="
        "variable=1,raw=3,target=2,mobius=4,q_lower=2/5,q_upper=3/5,"
        "one_bound=4/5,one_saving=1/5,total_saving=4/5,required=1,"
        "post=11/5,deficit=1/5,q1=1,zero=True,"
        "major_neighborhoods=False,joint=False,major_power=False,"
        "physical=False,covered=False"
    ) in report
    assert (
        "large_q_transition: inverse_zeta_zero_free_implication="
        "ambient=1,window=1/2,variance=3/2,block=3/4,"
        "abscissa=3/4,x_integral=True,cauchy=True,dyadic=True,"
        "zero_free=True,original_necessary=False,available=False"
    ) in report
    assert (
        "large_q_transition: bblr_h_poisson_unsigned="
        "old=5/2,new=2,target=2,saving=1/2,h_modulus=True,"
        "poisson=True,inverse_removed=True,gcd_sum=True,"
        "positive_d_tail=True,approximation=2,power_closed=True,"
        "log_closed=False,whole_face=False"
    ) in report
    assert (
        "large_q_transition: bblr_h_poisson_signed_boundary="
        "s=1/4,large_inner=7/8,small_inner=1/8,shift=1/4,"
        "side=5/4,raw=3/2,required=5/4,saving=1/4,"
        "prefactor=3/4,error1=2,error2=2,target=2,margin=0,"
        "diagonal_reduction=True,sharp=True,published_upper=1/4,"
        "boundary_log=False,residual_lower=1/4,residual_upper=1,"
        "whole_face=False"
    ) in report
    assert (
        "large_q_transition: signed_dual_convolution="
        "outer=1/2,dual=1/2,product=1,signed_atoms=2,"
        "collapse=True,survivor=mobius,cutoff=True,"
        "product_weight=False,ratio_mellin=True,published=False,"
        "whole_face=False"
    ) in report
    assert (
        "large_q_transition: coupled_ratio_mellin_type_ii_endpoint="
        "s=1,long=1,collapsed=1,shift=1,ambient=2,modulus=1,"
        "level=1/2,raw=3,target=2,required=1,two_coeff_sqrt=1,"
        "margin=0,bv_range=True,fixed_shift=False,quotient_mobius=True,"
        "coupled_shift=True,coprime_allocation=True,four_variable=False,"
        "published=False,whole_face=False"
    ) in report
    assert (
        "large_q_transition: collapsed_coprimality_allocation="
        "cross_conditions=4,allocation_divisors=4,identity=True,"
        "finite=True,power_loss=0,log_loss=4,superposition=True,"
        "independent=True,bv=False,type_ii=False,whole_face=False"
    ) in report
    assert (
        "large_q_transition: collapsed_chowla_face_endpoint="
        "s=1,long=1,collapsed=1,face_raw=2,target=2,margin=0,"
        "equal_face=True,fixed_shift=True,primitive_excludes=False,"
        "zero_ratio_mobius=True,chowla=True,ordinary_chowla=False,"
        "log_little_o=True,pointwise_triangle=False,joint_ratio=True,"
        "type_ii=False,whole_face=False"
    ) in report
    assert (
        "large_q_transition: physical_joint_ratio_recombination="
        "finite_kernel=True,equal_face_nonzero=True,witness=4,"
        "joint_mellin_annihilates=False,arbitrary_weight=False,"
        "allocation_triangle=False,face_separate=False,"
        "full_outer_coupling=True,centered_dispersion=False,"
        "whole_face=False"
    ) in report
    assert (
        "large_q_transition: collapsed_gcd_centered_kernel="
        "s=1,gamma=3/5,A=2/5,raw=12/5,target=2,saving=2/5,"
        "inner_target=8/5,diagonal_killed=True,centered=True,"
        "full_g=True,full_allocation_ratio=True,pointwise_chowla=False,"
        "published_average=False,"
        "dispersion=False,whole_face=False"
    ) in report
    assert (
        "large_q_transition: top_equal_product_outer_pnt="
        "atom=1/2,q=0,outer=1,long=1,raw=2,target=2,margin=0,"
        "factorization=True,interval_convolution=True,balanced=True,"
        "coprime_pnt=True,euler_polylog=True,trivial_long=True,"
        "fixed_chowla=False,face_closed=True,whole_face=False"
    ) in report
    assert (
        "large_q_transition: polylog_gcd_collar_outer_pnt="
        "K=5,A=0,cross=0,q=0,required=0,factorization=True,"
        "cross_identity=True,divisible_coprime_pnt=True,"
        "absorbs_polylog=True,trivial_long=True,collar_closed=True,"
        "positive_power=False,whole_face=False"
    ) in report
    assert (
        "large_q_transition: strict_power_gcd_core="
        "s=1,delta=2/5,gamma=3/5,theta=1/5,r1=1/4,r2=7/20,"
        "a0=3/20,b0=1/20,u0=1/4,v0=3/20,unsigned=2/5,"
        "signed=2/5,g=3/5,raw=12/5,target=2,saving=2/5,"
        "feasible=True,deficit_block=True,full_coupling=True,"
        "two_arithmetic=True,bblr_adapter=True,required=True,"
        "proved=False,whole_face=False"
    ) in report
    assert (
        "large_q_transition: strict_power_convolution="
        "r=5/4,t=27/20,a0=3/20,b0=1/20,side=7/5,outside=3/5,"
        "bblr_hypotheses=True,bblr_ab=7/2,bblr_watt=81/40,"
        "bblr_target=7/5,bblr_deficits=21/10/5/8,bblr_covered=False,"
        "dual=6/5,numerator=8/5,normalization=-6/5,"
        "bc_hypotheses=True,bc_totals=1323/400/551/160,"
        "bc_deficits=523/400/231/160,bc_covered=False,"
        "cross_centered=True,tuple_diagonal=11/5,grouped_diagonal=12/5,"
        "diagonal_target=2,grouped_deficit=2/5,grouped_raw=True,"
        "grouped_killed=False,near_type_ii=False"
    ) in report
    assert (
        "large_q_transition: strict_power_ratio_mellin_bandwidth="
        "u0=1/4,v0=3/20,hidden=2/5,height_derivative=0,"
        "ratio_derivative=0,mellin_bandwidth=0,adjacent=1/4/3/20,"
        "cauchy_deficit=2/5,rapid_tail=True,scaled_not_bandwidth=True,"
        "second_coordinate=False,resolves_hidden=False,"
        "supplies_delta=False,pre_cauchy=True"
    ) in report
    assert (
        "large_q_transition: strict_power_double_poisson_resonance="
        "a0=3/20,b0=1/20,r=5/4,t=27/20,k=17/20,l=19/20,"
        "product=11/5,shift=6/5,amplitude=1/5,overlap=-1,"
        "transformed_inner=13/5,original_inner=9/5,loss=4/5,"
        "transformed_global=16/5,target=2,required=6/5,"
        "identity=True,scales=True,loss_formula=True,covered=False,"
        "pre_cauchy=True"
    ) in report
    assert (
        "large_q_transition: strict_power_double_poisson_bblr="
        "sharp=True,before=43/10/129/40,normalization=-4/5,"
        "totals=41/10/121/40,deficits=21/10/41/40,"
        "original=21/10/5/8,ab_invariant=True,watt_extra=2/5,"
        "watt_nonnegative=True,improves=False"
    ) in report


def test_common_modulus_gauss_kernel_is_exactly_degenerate() -> None:
    helper = getattr(
        coverage_audit,
        "common_modulus_degenerate_gauss_identity",
        None,
    )
    assert helper is not None, "common-modulus Gauss helper is missing"

    nonzero = helper(r=5, s=7, c=10, v=15)
    assert nonzero["common_modulus"] == 35
    assert nonzero["gauss_support_requires_r_divides_c_and_v"]
    assert nonzero["r_divides_c_and_v"]
    assert nonzero["orthogonality_derivation_exact"]
    assert nonzero["gauss_amplitude"] == 175
    assert nonzero["gauss_phase"] == F(2, 7)

    c_off = helper(r=5, s=7, c=11, v=15)
    assert not c_off["r_divides_c"]
    assert c_off["gauss_amplitude"] == 0
    assert c_off["orthogonality_derivation_exact"]

    v_off = helper(r=5, s=7, c=10, v=16)
    assert v_off["r_divides_c"]
    assert not v_off["r_divides_v"]
    assert v_off["gauss_amplitude"] == 0
    assert v_off["orthogonality_derivation_exact"]


def test_common_modulus_exchange_sublattices_only_meet_at_centered_zero() -> None:
    adapter = getattr(
        coverage_audit,
        "common_modulus_exchange_audit",
        None,
    )
    assert adapter is not None, "common-modulus exchange audit is missing"
    audit = adapter()
    assert audit.common_modulus_exponent == F(6)
    assert audit.raw_dual_c_exponent == F(7, 2)
    assert audit.raw_dual_v_exponent == F(7, 2)
    assert audit.original_gauss_support_divisor_exponent == F(3)
    assert audit.swapped_gauss_support_divisor_exponent == F(3)
    assert audit.reduced_dual_c_exponent == F(1, 2)
    assert audit.reduced_dual_v_exponent == F(1, 2)
    assert audit.original_frequency_sublattice_is_r_times_square
    assert audit.swapped_frequency_sublattice_is_s_times_square
    assert audit.nonzero_sublattice_intersection_empty_mod_rs
    assert audit.centered_zero_frequency_annihilated
    assert not audit.common_modulus_forces_real_completed_coefficient
    assert not audit.common_modulus_reduces_conductor
    assert not audit.second_order_collar_unconditional


def test_midpoint_common_modulus_kernel_is_a_nondegenerate_involution() -> None:
    helper = getattr(
        coverage_audit,
        "midpoint_common_modulus_involution_identity",
        None,
    )
    assert helper is not None, "midpoint common-modulus helper is missing"

    exact = helper(r=5, s=7, c=11, v=13)
    assert exact["common_modulus"] == 70
    assert exact["bilinear_coefficient"] == 29
    assert exact["swapped_bilinear_coefficient"] == 41
    assert exact["coefficient_is_unit"]
    assert exact["coefficient_is_involution"]
    assert exact["swap_negates_coefficient"]
    assert exact["qualifying_y"] == (39,)
    assert exact["unique_qualifying_y_is_Ac"]
    assert exact["gauss_amplitude"] == 70
    assert exact["gauss_phase"] == F(17, 70)
    assert exact["swapped_gauss_phase"] == F(53, 70)
    assert exact["swap_phase_is_conjugate"]

    second = helper(r=7, s=9, c=-4, v=8)
    assert second["coefficient_is_unit"]
    assert second["coefficient_is_involution"]
    assert second["swap_negates_coefficient"]
    assert second["unique_qualifying_y_is_Ac"]
    assert second["swap_phase_is_conjugate"]

    for r in range(2, 10):
        for s in range(2, 10):
            if gcd(r, s) != 1:
                continue
            for c in (-5, -1, 0, 2, 7):
                for v in (-4, 0, 3, 8):
                    sample = helper(r=r, s=s, c=c, v=v)
                    assert sample["coefficient_is_unit"]
                    assert sample["coefficient_is_involution"]
                    assert sample["swap_negates_coefficient"]
                    assert sample["unique_qualifying_y_is_Ac"]
                    assert sample["swap_phase_is_conjugate"]


def test_midpoint_hermitian_completion_has_exact_critical_ledger() -> None:
    adapter = getattr(
        coverage_audit,
        "midpoint_hermitian_completion_audit",
        None,
    )
    assert adapter is not None, "midpoint Hermitian completion audit is missing"
    audit = adapter()
    assert audit.common_modulus_exponent == F(6)
    assert audit.raw_dual_c_exponent == F(7, 2)
    assert audit.raw_dual_v_exponent == F(7, 2)
    assert audit.completed_ambient_exponent == F(13)
    assert audit.completion_prefactor_exponent == F(-1)
    assert audit.completed_gate_target_exponent == F(7)
    assert audit.square_root_ambient_exponent == F(13, 2)
    assert audit.allowance_beyond_square_root_exponent == F(1, 2)
    assert audit.midpoint_coefficient_is_unit
    assert audit.midpoint_coefficient_is_involution
    assert audit.exchange_negates_midpoint_coefficient
    assert audit.same_frequency_swap_is_conjugate
    assert audit.centered_multiplier_zero_on_c_zero_row
    assert audit.centered_multiplier_zero_on_v_zero_column
    assert not audit.modular_involution_phase_is_near_diagonal_small
    assert not audit.published_bound_verified


def test_midpoint_phase_is_exactly_hermitian_up_to_frequency_parity() -> None:
    helper = getattr(
        coverage_audit,
        "midpoint_salie_phase_identity",
        None,
    )
    assert helper is not None, "midpoint Salié-phase helper is missing"
    odd = helper(r=5, s=7, c=11, v=13)
    assert odd["midpoint_phase"] == F(17, 70)
    assert odd["hermitian_phase"] == F(26, 35)
    assert odd["parity_correction"] == F(1, 2)
    assert odd["identity_exact_mod_one"]

    even = helper(r=7, s=9, c=4, v=8)
    assert even["parity_correction"] == F(0)
    assert even["identity_exact_mod_one"]

    for r in range(2, 10):
        for s in range(2, 10):
            if gcd(r, s) != 1:
                continue
            for c in (-5, -2, 0, 3, 8):
                for v in (-7, 0, 4, 9):
                    assert helper(
                        r=r,
                        s=s,
                        c=c,
                        v=v,
                    )["identity_exact_mod_one"]


def test_withdrawn_hermitian_claim_does_not_cover_midpoint_operator() -> None:
    adapter = getattr(
        coverage_audit,
        "midpoint_published_hermitian_adapter_audit",
        None,
    )
    assert adapter is not None, "midpoint published-adapter audit is missing"
    audit = adapter()
    assert audit.numerator_exponent == F(7)
    assert audit.rs_trivial_exponent == F(6)
    assert audit.withdrawn_claimed_outer_inner_bound_exponent == F(6)
    assert audit.withdrawn_claimed_outer_inner_saving_exponent == F(0)
    assert audit.withdrawn_claimed_bulk_inner_bound_exponent == F(23, 4)
    assert audit.withdrawn_claimed_bulk_inner_saving_exponent == F(1, 4)
    assert not audit.theorem_has_moving_numerator
    assert not audit.theorem_accepts_joint_r_s_c_v_coefficient
    assert not audit.theorem_supplies_c_v_frequency_average
    assert audit.claim_withdrawn_for_missing_l_squared_factor
    assert not audit.corrected_argument_gives_claimed_improvement
    assert not audit.withdrawn_claim_closes_midpoint_gate


def test_midpoint_roots_biject_with_ordered_coprime_factorizations() -> None:
    helper = getattr(
        coverage_audit,
        "midpoint_unitary_divisor_root_bijection",
        None,
    )
    assert helper is not None, "unitary-divisor root helper is missing"

    for n, expected_count in ((6, 4), (15, 4), (30, 8), (105, 8), (210, 16)):
        exact = helper(n=n)
        assert exact["squarefree"]
        assert exact["ordered_factorization_count"] == expected_count
        assert exact["root_count"] == expected_count
        assert exact["expected_root_count"] == expected_count
        assert exact["factorization_to_root_injective"]
        assert exact["root_to_factorization_exact"]
        assert exact["bijection_exact"]
        for item in exact["factorizations"]:
            assert item["r"] * item["s"] == n
            assert gcd(item["r"], item["s"]) == 1
            assert item["coefficient_squared_is_one"]
            assert item["recovered_r"] == item["r"]
            assert item["recovered_s"] == item["s"]

    nonsquarefree = helper(n=12)
    assert not nonsquarefree["squarefree"]
    assert nonsquarefree["ordered_factorization_count"] == 0
    assert nonsquarefree["root_count"] == 0


def test_unitary_divisor_reparametrization_records_the_remaining_gate() -> None:
    adapter = getattr(
        coverage_audit,
        "midpoint_unitary_divisor_audit",
        None,
    )
    assert adapter is not None, "unitary-divisor audit is missing"
    audit = adapter()
    assert audit.product_variable_exponent == F(6)
    assert audit.root_modulus_exponent == F(6)
    assert audit.physical_numerator_exponent == F(5)
    assert audit.dual_numerator_exponent == F(7)
    assert audit.factorization_root_bijection_exact
    assert audit.mobius_product_collapses_to_single_mobius
    assert audit.root_multiplicity_is_subpower
    assert audit.balanced_dyadic_condition_is_root_filter
    assert audit.root_trace_coefficient_remains_joint
    assert not audit.unitary_root_trace_bound_verified


def test_root_farey_large_sieve_has_the_exact_eleven_halves_deficit() -> None:
    helper = getattr(
        coverage_audit,
        "midpoint_root_fraction_identity",
        None,
    )
    assert helper is not None, "root-fraction helper is missing"
    first = helper(r=5, s=7)
    second = helper(r=7, s=5)
    assert first["numerator"] == 29
    assert first["denominator"] == 70
    assert first["fraction_is_reduced"]
    assert first["recovered_r"] == 5
    assert first["recovered_s"] == 7
    assert first["factorization_recovered_exactly"]
    assert second["numerator"] == 41
    assert second["denominator"] == 70
    assert second["fraction_is_reduced"]
    assert second["factorization_recovered_exactly"]

    adapter = getattr(
        coverage_audit,
        "midpoint_root_farey_large_sieve_audit",
        None,
    )
    assert adapter is not None, "root-Farey large-sieve audit is missing"
    audit = adapter()
    assert audit.root_point_count_exponent == F(6)
    assert audit.denominator_exponent == F(6)
    assert audit.reciprocal_spacing_exponent == F(12)
    assert audit.physical_numerator_length_exponent == F(5)
    assert audit.physical_product_energy_exponent == F(5)
    assert audit.physical_large_sieve_bound_exponent == F(23, 2)
    assert audit.physical_target_exponent == F(6)
    assert audit.physical_deficit_exponent == F(11, 2)
    assert audit.dual_numerator_length_exponent == F(7)
    assert audit.dual_product_energy_exponent == F(7)
    assert audit.dual_large_sieve_bound_exponent == F(25, 2)
    assert audit.dual_target_exponent == F(7)
    assert audit.dual_deficit_exponent == F(11, 2)
    assert audit.root_fractions_injective
    assert audit.root_fractions_reduced
    assert not audit.actual_joint_coefficient_is_separated
    assert not audit.root_farey_large_sieve_closes_gate


def test_root_crt_phase_split_and_type_ii_kernel_are_exact() -> None:
    helper = getattr(
        coverage_audit,
        "midpoint_root_crt_phase_identity",
        None,
    )
    assert helper is not None, "root CRT phase helper is missing"
    exact = helper(a=3, b=5, root_a=5, root_b=9, numerator=7)
    assert exact["combined_root"] == 29
    assert exact["combined_modulus"] == 30
    assert exact["combined_root_squared_is_one"]
    assert exact["combined_root_restricts_to_root_a"]
    assert exact["combined_root_restricts_to_root_b"]
    assert exact["full_phase"] == F(23, 30)
    assert exact["small_correction_phase"] == F(7, 30)
    assert exact["left_reciprocal_phase"] == F(1, 3)
    assert exact["right_reciprocal_phase"] == F(1, 5)
    assert exact["phase_split_exact_mod_one"]

    for a, b in ((2, 3), (3, 10), (5, 14), (7, 15)):
        roots_a = coverage_audit.midpoint_unitary_divisor_root_bijection(
            n=a
        )["roots"]
        roots_b = coverage_audit.midpoint_unitary_divisor_root_bijection(
            n=b
        )["roots"]
        for root_a in roots_a:
            for root_b in roots_b:
                for numerator in (-11, 0, 8):
                    sample = helper(
                        a=a,
                        b=b,
                        root_a=root_a,
                        root_b=root_b,
                        numerator=numerator,
                    )
                    assert sample["combined_root_squared_is_one"]
                    assert sample["combined_root_restricts_to_root_a"]
                    assert sample["combined_root_restricts_to_root_b"]
                    assert sample["phase_split_exact_mod_one"]

    adapter = getattr(
        coverage_audit,
        "midpoint_root_type_ii_audit",
        None,
    )
    assert adapter is not None, "root Type-II audit is missing"
    audit = adapter()
    assert audit.product_exponent == F(6)
    assert audit.left_factor_exponent == F(3)
    assert audit.right_factor_exponent == F(3)
    assert audit.physical_numerator_exponent == F(5)
    assert audit.dual_numerator_exponent == F(7)
    assert audit.generalized_crt_exact
    assert audit.reciprocal_phase_split_exact
    assert audit.left_factor_has_truncated_divisor_coefficient
    assert audit.right_factor_retains_mobius
    assert audit.root_fibers_are_subpower
    assert audit.completed_centering_exact
    assert audit.physical_zero_residue_vanishes
    assert not audit.physical_centered_subtraction_present
    assert not audit.published_hermitian_theorem_has_root_dependent_numerator
    assert audit.actual_transform_coefficient_remains_joint
    assert not audit.root_type_ii_bound_verified


def test_root_type_ii_unfolds_to_exact_four_factor_kloosterman_phase() -> None:
    helper = getattr(
        coverage_audit,
        "midpoint_root_four_factor_phase_identity",
        None,
    )
    assert helper is not None, "root four-factor phase helper is missing"

    exact = helper(d_r=3, d_s=5, e_r=7, e_s=2, numerator=11)
    assert exact["d"] == 15
    assert exact["e"] == 14
    assert exact["recovered_r"] == 21
    assert exact["recovered_s"] == 10
    assert exact["root_d"] == 11
    assert exact["root_e"] == 13
    assert exact["combined_root"] == 41
    assert exact["full_phase"] == F(31, 420)
    assert exact["small_correction_phase"] == F(11, 420)
    assert exact["left_kloosterman_phase"] == F(1, 3)
    assert exact["right_kloosterman_phase"] == F(5, 7)
    assert exact["all_factors_pairwise_coprime"]
    assert exact["combined_root_recovers_original_factorization"]
    assert exact["root_phase_equals_four_factor_phase"]

    extreme = helper(d_r=3, d_s=1, e_r=1, e_s=5, numerator=7)
    assert extreme["recovered_r"] == 3
    assert extreme["recovered_s"] == 5
    assert extreme["full_phase"] == F(17, 30)
    assert extreme["small_correction_phase"] == F(7, 30)
    assert extreme["left_kloosterman_phase"] == F(1, 3)
    assert extreme["right_kloosterman_phase"] == F(0)
    assert extreme["extreme_sector_recovers_original_fraction"]

    for d_r, d_s, e_r, e_s in (
        (2, 3, 5, 7),
        (3, 5, 7, 11),
        (5, 1, 1, 14),
        (1, 15, 2, 7),
    ):
        for numerator in (-13, 0, 17):
            sample = helper(
                d_r=d_r,
                d_s=d_s,
                e_r=e_r,
                e_s=e_s,
                numerator=numerator,
            )
            assert sample["all_factors_pairwise_coprime"]
            assert sample["combined_root_recovers_original_factorization"]
            assert sample["root_phase_equals_four_factor_phase"]

    adapter = getattr(
        coverage_audit,
        "midpoint_root_four_factor_audit",
        None,
    )
    assert adapter is not None, "root four-factor audit is missing"
    audit = adapter()
    assert audit.left_product_exponent == F(3)
    assert audit.right_product_exponent == F(3)
    assert audit.physical_numerator_exponent == F(5)
    assert audit.recovered_r_exponent == F(3)
    assert audit.recovered_s_exponent == F(3)
    assert audit.root_fibers_unfold_to_ordered_factorizations
    assert audit.four_factors_are_pairwise_coprime
    assert audit.truncated_divisor_coefficient_remains_on_left_product
    assert audit.mobius_splits_over_right_factors
    assert audit.kloosterman_phase_identity_exact
    assert audit.completed_centering_exact
    assert audit.physical_zero_residue_vanishes
    assert not audit.physical_centered_subtraction_present
    assert audit.extreme_sector_recovers_hard_fraction
    assert audit.actual_smooth_weight_remains_joint
    assert not audit.four_factor_type_ii_bound_verified


def test_midpoint_physical_poisson_resonance_lattice_is_exact() -> None:
    helper = getattr(
        coverage_audit,
        "midpoint_involution_resonance_lattice_identity",
        None,
    )
    assert helper is not None, "midpoint resonance-lattice helper is missing"
    exact = helper(r=5, s=7, h=1, poisson_frequency=0)
    assert exact["modulus"] == 70
    assert exact["midpoint_root"] == 29
    assert exact["resonance_integer"] == 29
    assert exact["a"] == 3
    assert exact["b"] == -2
    assert exact["h_equals_r_a_plus_s_b"]
    assert exact["u_equals_r_a_minus_s_b"]
    assert exact["root_congruences_exact"]
    assert exact["lattice_bijection_exact"]

    for r, s, h, frequency in (
        (3, 5, 11, -2),
        (5, 8, -7, 3),
        (7, 9, 23, -1),
        (11, 13, -19, 4),
    ):
        sample = helper(
            r=r,
            s=s,
            h=h,
            poisson_frequency=frequency,
        )
        assert sample["root_congruences_exact"]
        assert sample["lattice_bijection_exact"]

    adapter = getattr(
        coverage_audit,
        "midpoint_physical_poisson_audit",
        None,
    )
    assert adapter is not None, "midpoint physical-Poisson audit is missing"
    audit = adapter()
    assert audit.modulus_exponent == F(6)
    assert audit.h_exponent == F(5, 2)
    assert audit.delta_exponent == F(5, 2)
    assert audit.resonance_window_exponent == F(7, 2)
    assert audit.lattice_parameter_exponent == F(1, 2)
    assert audit.pointwise_bilinear_bound_exponent == F(3)
    assert audit.raw_bilinear_exponent == F(5)
    assert audit.physical_oscillation_saving_exponent == F(2)
    assert audit.outer_root_point_exponent == F(6)
    assert audit.outer_target_exponent == F(6)
    assert audit.required_outer_saving_exponent == F(3)
    assert audit.resonance_lattice_bijection_exact
    assert audit.one_variable_poisson_exact
    assert audit.joint_weight_has_uniform_delta_derivatives
    assert audit.determinant_line_correspondence_exact
    assert not audit.physical_poisson_route_is_independent
    assert not audit.outer_mobius_square_root_verified


def test_odd_root_trace_has_exact_salie_coefficient_identity() -> None:
    helper = getattr(
        coverage_audit,
        "odd_root_trace_salie_coefficient_identity",
        None,
    )
    assert helper is not None, "odd root-trace Salié helper is missing"
    for modulus, numerator in (
        (3, 1),
        (5, 2),
        (15, 4),
        (21, 5),
        (35, 6),
        (105, 8),
    ):
        exact = helper(modulus=modulus, numerator=numerator)
        assert exact["modulus_is_odd_squarefree"]
        assert exact["numerator_is_coprime_to_modulus"]
        assert exact["root_count"] == 2 ** len(exact["prime_factors"])
        assert exact["salie_coefficient_identity_exact"]

    adapter = getattr(
        coverage_audit,
        "root_salie_adapter_audit",
        None,
    )
    assert adapter is not None, "root-trace Salié adapter is missing"
    audit = adapter()
    assert audit.modulus_exponent == F(6)
    assert audit.physical_numerator_exponent == F(5)
    assert audit.fixed_numerator_bound_exponent == F(351, 59)
    assert audit.fixed_numerator_saving_exponent == F(3, 59)
    assert audit.absolute_numerator_sum_bound_exponent == F(646, 59)
    assert audit.physical_target_exponent == F(6)
    assert audit.absolute_numerator_sum_deficit_exponent == F(292, 59)
    assert audit.odd_full_root_trace_identity_exact
    assert not audit.even_midpoint_modulus_adapter_verified
    assert not audit.theorem_accepts_balanced_root_filter
    assert not audit.theorem_accepts_mobius_modulus_weight
    assert not audit.theorem_accepts_moving_numerator
    assert not audit.square_numerator_exception_covered
    assert not audit.theorem_accepts_joint_transform_weight
    assert not audit.salie_adapter_closes_root_gate


def test_square_product_sector_and_joint_salie_ledger_are_exact() -> None:
    helper = getattr(
        coverage_audit,
        "square_product_common_kernel_identity",
        None,
    )
    assert helper is not None, "square-product kernel helper is missing"
    for left, right, expected_kernel, expected_x, expected_y in (
        (12, 75, 3, 2, 5),
        (18, 8, 2, 3, 2),
        (45, 20, 5, 3, 2),
        (49, 81, 1, 7, 9),
    ):
        exact = helper(left=left, right=right)
        assert exact["product_is_square"]
        assert exact["common_squarefree_kernel"] == expected_kernel
        assert exact["left_square_factor"] == expected_x
        assert exact["right_square_factor"] == expected_y
        assert exact["left_reconstruction_exact"]
        assert exact["right_reconstruction_exact"]
    nonsquare = helper(left=12, right=50)
    assert not nonsquare["product_is_square"]
    assert not nonsquare["common_kernel_exists"]

    adapter = getattr(
        coverage_audit,
        "root_salie_joint_average_audit",
        None,
    )
    assert adapter is not None, "joint Salié average audit is missing"
    audit = adapter()
    assert audit.left_root_factor_exponent == F(3)
    assert audit.right_root_factor_exponent == F(3)
    assert audit.physical_numerator_exponent == F(5)
    assert audit.bcr_term_1_exponent == F(101, 10)
    assert audit.bcr_term_2_exponent == F(85, 8)
    assert audit.bcr_bound_exponent == F(85, 8)
    assert audit.physical_target_exponent == F(6)
    assert audit.bcr_deficit_exponent == F(37, 8)
    assert audit.square_product_pair_count_exponent == F(5, 2)
    assert audit.dfi_square_main_short_factor_cutoff_exponent == F(7, 5)
    assert audit.dfi_long_long_cutoff_exponent == F(174, 59)
    assert audit.balanced_root_factor_exponent == F(3)
    assert audit.fixed_square_hermitian_bound_exponent == F(95, 16)
    assert audit.absolute_square_family_bound_exponent == F(135, 16)
    assert audit.absolute_square_family_deficit_exponent == F(39, 16)
    assert audit.salie_factorization_matches_midpoint_phase
    assert audit.joint_average_is_existing_bcr_endpoint
    assert audit.bcr_accepts_mobius_coefficients
    assert not audit.bcr_uses_mobius_beyond_l2
    assert audit.balanced_root_filter_excludes_dfi_square_main
    assert not audit.joint_salie_route_closes_root_gate


def test_square_salie_quadratic_gauss_completion_is_exact() -> None:
    helper = getattr(
        coverage_audit,
        "square_salie_double_gauss_identity",
        None,
    )
    assert helper is not None, "square Salié double-Gauss helper is missing"
    for r, s, t in ((3, 5, 2), (5, 7, 3), (7, 9, -2), (11, 13, 4)):
        exact = helper(r=r, s=s, square_root=t)
        assert exact["factors_are_odd_coprime"]
        assert exact["quadratic_completion_identity_exact"]
        assert exact["combined_phase_factorization_exact"]
        assert exact["gauss_product_character_is_mod8_local"]

    adapter = getattr(
        coverage_audit,
        "square_salie_gauss_completion_audit",
        None,
    )
    assert adapter is not None, "square Salié Gauss audit is missing"
    audit = adapter()
    assert audit.r_exponent == F(3)
    assert audit.s_exponent == F(3)
    assert audit.square_root_exponent == F(5, 2)
    assert audit.x_exponent == F(3)
    assert audit.y_exponent == F(3)
    assert audit.gauss_normalization_exponent == F(-3)
    assert audit.t_poisson_resonance_exponent == F(7, 2)
    assert audit.localized_pointwise_exponent == F(3)
    assert audit.direct_square_sector_pointwise_exponent == F(5, 2)
    assert audit.double_gauss_identity_exact
    assert audit.cross_character_depends_only_on_mod8
    assert audit.square_root_variable_is_linearized
    assert audit.remaining_quadratic_weight_is_joint
    assert not audit.gauss_completion_improves_square_sector
    assert not audit.square_salie_gauss_route_closes_gate


def test_balanced_mobius_product_shift_variance_is_exact() -> None:
    helper = getattr(
        coverage_audit,
        "balanced_product_diagonal_parameterization",
        None,
    )
    assert helper is not None, "balanced-product diagonal helper is missing"
    for a, b, c, d, expected in (
        (6, 35, 10, 21, (2, 3, 5, 7)),
        (14, 15, 21, 10, (7, 2, 3, 5)),
        (25, 14, 35, 10, (5, 5, 7, 2)),
        (13, 17, 13, 17, (13, 1, 1, 17)),
    ):
        exact = helper(a=a, b=b, c=c, d=d)
        assert exact["products_equal"]
        assert (
            exact["common_factor"],
            exact["left_primitive"],
            exact["right_primitive"],
            exact["complementary_factor"],
        ) == expected
        assert exact["primitive_pair_coprime"]
        assert exact["left_reconstruction_exact"]
        assert exact["right_reconstruction_exact"]
        assert exact["complementary_reconstruction_exact"]

    off = helper(a=6, b=35, c=10, d=19)
    assert not off["products_equal"]
    assert off["product_shift"] == 20

    adapter = getattr(
        coverage_audit,
        "mobius_product_shifted_variance_audit",
        None,
    )
    assert adapter is not None, "Möbius product-shift audit is missing"
    audit = adapter()
    assert audit.factor_length_exponent == F(1)
    assert audit.product_length_exponent == F(2)
    assert audit.transform_shift_exponent == F(1)
    assert audit.diagonal_power_exponent == F(0)
    assert audit.diagonal_logarithmic_exponent == F(1)
    assert audit.raw_shifted_determinant_exponent == F(3)
    assert audit.shifted_determinant_target_exponent == F(2)
    assert audit.required_shifted_determinant_saving_exponent == F(1)
    assert audit.product_convolution_identity_exact
    assert audit.diagonal_parameterization_exact
    assert audit.schwartz_tail_is_power_negligible
    assert audit.polylogarithmic_transition_collar_retained
    assert audit.equivalent_to_separated_mixed_fourth_moment_gate
    assert not audit.shifted_mobius_determinant_bound_proved
    assert not audit.original_signed_kernel_requires_component_gate
    assert not audit.route_closes_mwkf_gate


def test_ganguly_guria_determinant_adapter_has_exact_residual_power() -> None:
    adapter = getattr(
        coverage_audit,
        "ganguly_guria_determinant_audit",
        None,
    )
    assert adapter is not None, "Ganguly--Guria determinant audit is missing"
    audit = adapter()
    assert audit.variable_length_exponent == F(1)
    assert audit.shift_range_exponent == F(1)
    assert audit.ramanujan_exponent == F(7, 64)
    assert audit.fixed_shift_error_exponent == F(71, 64)
    assert audit.absolute_shift_sum_error_exponent == F(135, 64)
    assert audit.shifted_determinant_target_exponent == F(2)
    assert audit.absolute_shift_sum_power_deficit == F(7, 64)
    assert audit.fixed_shift_main_exponent == F(2)
    assert audit.absolute_shift_sum_main_exponent == F(3)
    assert audit.smooth_unweighted_fixed_shift_theorem_proved
    assert not audit.distinct_tensor_weights_accepted_as_stated
    assert not audit.arithmetic_coefficients_accepted
    assert not audit.coefficient_form_uniformity_quantified
    assert not audit.mobius_type_i_ii_adapter_proved
    assert audit.ramanujan_conjecture_removes_power_deficit
    assert not audit.ramanujan_conjecture_supplies_logarithmic_saving
    assert not audit.mobius_main_term_cancellation_proved
    assert not audit.ganguly_guria_route_closes_mobius_gate


def test_darbar_das_variance_class_excludes_inverse_zeta_square() -> None:
    coefficients = getattr(
        coverage_audit,
        "mobius_triple_convolution_prime_power_coefficients",
        None,
    )
    assert coefficients is not None, "triple-Möbius local helper is missing"
    assert coefficients() == (1, -3, 3, -1, 0)

    adapter = getattr(
        coverage_audit,
        "darbar_das_short_variance_audit",
        None,
    )
    assert adapter is not None, "Darbar--Das variance audit is missing"
    audit = adapter()
    assert audit.ambient_length_exponent == F(2)
    assert audit.short_window_exponent == F(1)
    assert audit.generic_short_variance_exponent == F(4)
    assert audit.required_short_variance_exponent == F(3)
    assert audit.required_variance_saving_exponent == F(1)
    assert audit.full_mobius_convolution_zeta_power == -2
    assert audit.required_auxiliary_zeta_power == -3
    assert audit.required_auxiliary_prime_coefficient == -3
    assert audit.required_auxiliary_prime_square_coefficient == 3
    assert audit.required_auxiliary_prime_cube_coefficient == -1
    assert not audit.auxiliary_fits_squarefree_m_class
    assert not audit.auxiliary_fits_completely_multiplicative_g_class
    assert not audit.restricted_convolution_is_multiplicative
    assert not audit.published_theorem_covers_full_mobius_convolution
    assert not audit.published_theorem_covers_restricted_convolution
    assert not audit.darbar_das_route_closes_mobius_gate


def test_ratio_mellin_coordinates_restore_multiplicativity_exactly() -> None:
    coordinates = getattr(
        coverage_audit,
        "restricted_product_ratio_coordinates",
        None,
    )
    assert coordinates is not None, "ratio-coordinate helper is missing"
    exact = coordinates(a=15, b=28, scale=11)
    assert exact["product_coordinate"] == F(420, 121)
    assert exact["factor_ratio"] == F(15, 28)
    assert exact["left_coordinate_squared"] == F(225, 121)
    assert exact["right_coordinate_squared"] == F(784, 121)
    assert exact["left_reconstruction_squared_exact"]
    assert exact["right_reconstruction_squared_exact"]

    local_factor = getattr(
        coverage_audit,
        "mobius_square_convolution_second_moment_local_factor",
        None,
    )
    assert local_factor is not None, "mu*mu square local-factor helper is missing"
    assert local_factor() == (1, 0, -9, 16, -9, 0, 1)

    adapter = getattr(
        coverage_audit,
        "restricted_mobius_ratio_mellin_audit",
        None,
    )
    assert adapter is not None, "ratio-Mellin audit is missing"
    audit = adapter()
    assert audit.factor_length_exponent == F(1)
    assert audit.product_length_exponent == F(2)
    assert audit.short_window_exponent == F(1)
    assert audit.required_short_variance_exponent == F(3)
    assert audit.ratio_coordinate_identity_exact
    assert audit.ratio_fourier_inversion_exact
    assert audit.integrand_coefficient_is_multiplicative
    assert audit.shifted_inverse_zeta_dirichlet_series_exact
    assert audit.product_coordinate_weight_is_smooth
    assert audit.ratio_transform_is_rapidly_decaying
    assert audit.uniform_single_tau_variance_is_sufficient
    assert audit.tau_zero_is_full_mobius_convolution
    assert audit.tau_zero_square_dirichlet_series_zeta_pole_order == 4
    assert audit.tau_zero_diagonal_log_exponent == 3
    assert audit.required_diagonal_log_exponent == 1
    assert audit.tau_zero_euler_remainder_has_no_prime_term
    assert audit.tau_zero_euler_remainder_converges_for_real_part_gt_half
    assert audit.tau_zero_formal_diagonal_log_excess == 2
    assert audit.tau_zero_diagonal_excess_requires_offdiagonal_cancellation
    assert audit.diagonal_term_is_not_lower_bound_for_full_variance
    assert not audit.tau_zero_diagonal_alone_disproves_uniform_gate
    assert audit.joint_ratio_recombination_has_restricted_diagonal_log_order_one
    assert audit.optimistic_mangerel_variance_exponent == F(4)
    assert audit.mangerel_power_deficit == F(1)
    assert audit.mangerel_only_supplies_logarithmic_saving
    assert not audit.uniform_tau_mangerel_hypotheses_verified
    assert not audit.shifted_inverse_zeta_variance_proved
    assert not audit.ratio_mellin_route_closes_mobius_gate


def test_brz_pointwise_mobius_convolution_bound_misses_local_variance() -> None:
    adapter = getattr(
        coverage_audit,
        "basak_robles_zaharescu_mobius_convolution_audit",
        None,
    )
    assert adapter is not None, "BRZ Möbius-convolution audit is missing"
    audit = adapter()
    assert audit.ambient_length_exponent == F(1)
    assert audit.short_window_exponent == F(1, 2)
    assert audit.critical_denominator_exponent == F(1, 2)
    assert audit.first_pointwise_term_exponent == F(16, 17)
    assert audit.second_pointwise_term_exponent == F(11, 12)
    assert audit.third_pointwise_term_exponent == F(15, 16)
    assert audit.best_published_pointwise_exponent == F(16, 17)
    assert audit.required_pointwise_exponent == F(1, 2)
    assert audit.pointwise_exponent_deficit == F(15, 34)
    assert audit.direct_local_arc_variance_exponent == F(81, 34)
    assert audit.required_local_variance_exponent == F(3, 2)
    assert audit.local_arc_variance_deficit == F(15, 17)
    assert audit.major_arc_direct_variance_exponent == F(2)
    assert audit.major_arc_power_deficit == F(1, 2)
    assert audit.published_full_mobius_convolution_pointwise_bound
    assert not audit.published_ratio_twisted_family_bound
    assert not audit.published_local_l2_bound
    assert not audit.brz_direct_pointwise_route_closes_variance_gate


def test_truncated_heath_brown_identity_for_mobius_is_exact() -> None:
    helper = getattr(
        coverage_audit,
        "truncated_heath_brown_mobius_identity",
        None,
    )
    assert helper is not None, "truncated Möbius identity helper is missing"

    # U^K is the exact validity range.  Exercise squarefree, nonsquarefree,
    # prime, and endpoint inputs rather than checking only a formal series.
    for cutoff, depth in ((2, 5), (3, 4), (5, 3)):
        for n in range(1, cutoff**depth + 1):
            exact = helper(n=n, cutoff=cutoff, depth=depth)
            assert exact["in_valid_range"]
            assert exact["lhs"] == exact["rhs"]
            assert exact["identity_exact"]


def test_mrtt_signed_power_shift_adapter_separates_model_from_physical_kernel() -> None:
    adapter = getattr(
        coverage_audit,
        "mrtt_signed_mobius_power_shift_audit",
        None,
    )
    assert adapter is not None, "signed MRTT power-shift audit is missing"

    hard = adapter(delta=F(1))
    assert hard.ambient_product_exponent == F(2)
    assert hard.shift_exponent == F(1)
    assert hard.relative_shift_exponent == F(1, 2)
    assert hard.long_shift_threshold == F(8, 33)
    assert hard.long_shift_delta_threshold == F(8, 25)
    assert hard.published_long_shift_range_applies
    assert hard.truncated_mobius_identity_exact
    assert hard.absolute_coefficient_is_bounded_by_d2
    assert hard.ramare_prime_factor_is_exact
    assert hard.major_arc_has_arbitrary_log_decay
    assert hard.fixed_power_shift_has_arbitrary_log_saving
    assert hard.mrtt_shift_average_exponent == F(3)
    assert hard.required_mwkf_correlation_exponent == F(2)
    assert hard.remaining_shift_power_deficit == F(1)
    assert not hard.mrtt_scale_closes_mwkf_model
    assert not hard.full_ratio_twisted_multiplicative_family_covered
    assert not hard.product_compatible_hard_vertex_covered
    assert not hard.physical_gcd_layer_adapter_verified
    assert not hard.whole_strict_power_core_covered

    below_long_threshold = adapter(delta=F(1, 4))
    assert below_long_threshold.relative_shift_exponent == F(1, 5)
    assert not below_long_threshold.published_long_shift_range_applies
    assert not below_long_threshold.fixed_power_shift_has_arbitrary_log_saving
    assert below_long_threshold.signed_typical_factor_extension_required
    assert not below_long_threshold.signed_typical_factor_extension_verified
    assert below_long_threshold.mrtt_shift_average_exponent == F(3, 2)
    assert below_long_threshold.required_mwkf_correlation_exponent == F(5, 4)
    assert below_long_threshold.remaining_shift_power_deficit == F(1, 4)
    assert not below_long_threshold.mrtt_scale_closes_mwkf_model
    assert not below_long_threshold.full_ratio_twisted_multiplicative_family_covered
    assert not below_long_threshold.physical_gcd_layer_adapter_verified


def test_hard_vertex_four_mobius_determinant_line_is_unimodular() -> None:
    helper = getattr(
        coverage_audit,
        "hard_vertex_four_mobius_determinant_line_identity",
        None,
    )
    assert helper is not None, "four-Möbius determinant helper is missing"

    for a in range(2, 13):
        for c in range(2, 13):
            for b, d in ((5, 8), (7, 3), (11, 12)):
                identity = helper(a=a, b=b, c=c, d=d)
                assert identity["gcd_extracted_exact"]
                assert identity["primitive_slopes_coprime"]
                assert identity["shift_quotient_integral"]
                assert identity["bezout_identity_exact"]
                assert identity["coordinate_change_determinant"] == -1
                assert identity["b_reconstructed"] == b
                assert identity["d_reconstructed"] == d
                assert identity["determinant_reconstructed_exact"]


def test_hard_vertex_four_mobius_gate_needs_exact_outer_square_root() -> None:
    adapter = getattr(
        coverage_audit,
        "hard_vertex_four_mobius_determinant_audit",
        None,
    )
    assert adapter is not None, "four-Möbius determinant audit is missing"

    for kappa, raw, saving in (
        (F(0), F(3), F(1)),
        (F(1, 2), F(5, 2), F(1, 2)),
        (F(1), F(2), F(0)),
    ):
        audit = adapter(gcd_exponent=kappa)
        assert audit.ambient_product_exponent == F(2)
        assert audit.shift_exponent == F(1)
        assert audit.primitive_slope_exponent == F(1) - kappa
        assert audit.shift_quotient_exponent == F(1) - kappa
        assert audit.line_parameter_exponent == kappa
        assert audit.raw_gcd_layer_exponent == raw
        assert audit.local_target_exponent == F(2)
        assert audit.required_power_saving == saving
        assert audit.outer_slope_pair_square_root_saving == saving
        assert audit.shift_quotient_full_cancellation_saving == saving
        assert audit.unimodular_line_parameterization_exact
        assert audit.outer_square_root_is_exponent_critical
        assert audit.mrtt_supplies_only_logarithmic_saving
        assert audit.top_face_contains_fixed_shift_chowla == (
            kappa == F(1)
        )
        assert not audit.top_face_logarithmic_saving_proved
        assert not audit.published_centered_outer_mobius_spectral_bound
        assert not audit.physical_ratio_kernel_restored
        assert not audit.hard_vertex_determinant_estimate_proved


def test_blomer_milicevic_periodic_mobius_encoding_has_no_power_gain() -> None:
    adapter = getattr(
        coverage_audit,
        "blomer_milicevic_mobius_modulus_audit",
        None,
    )
    assert adapter is not None, "Blomer--Milićević modulus audit is missing"

    hard = adapter(
        modulus_scale_exponent=F(3),
        numerator_product_exponent=F(5),
    )
    assert hard.kloosterman_modulus_scale_exponent == F(3)
    assert hard.periodic_encoding_modulus_exponent == F(3)
    assert hard.mobius_support_l2_lower_exponent == F(3, 2)
    assert hard.ramanujan_theta == F(7, 64)
    assert hard.bm_archimedean_factor_exponent == F(69, 32)
    assert hard.bm_total_bound_exponent == F(117, 32)
    assert hard.trivial_normalized_modulus_sum_exponent == F(3)
    assert hard.published_bound_deficit == F(21, 32)
    assert hard.selberg_replacement_bound_exponent == F(227, 64)
    assert hard.selberg_replacement_deficit == F(35, 64)
    assert hard.full_ramanujan_bound_exponent == F(3)
    assert hard.full_ramanujan_margin == F(0)
    assert hard.linnik_range_hypothesis_holds
    assert hard.collision_free_exact_periodic_encoding_available
    assert hard.fourier_l1_lower_bound_follows_from_parseval
    assert not hard.small_period_exact_mobius_encoding_ruled_out
    assert not hard.actual_qct_kernel_is_complete_kloosterman_family
    assert not hard.direct_periodic_weight_adapter_has_power_saving
    assert not hard.whole_mobius_gate_covered


def test_blomer_milicevic_type_i_level_split_keeps_exceptional_deficit() -> None:
    adapter = getattr(
        coverage_audit,
        "blomer_milicevic_type_i_level_audit",
        None,
    )
    assert adapter is not None, "BM Type-I level audit is missing"

    level_zero = adapter(
        modulus_scale_exponent=F(3),
        numerator_product_exponent=F(5),
        target_exponent=F(2),
        exposed_level_box_exponent=F(0),
    )
    assert level_zero.fixed_level_bound_exponent == F(69, 32)
    assert level_zero.type_i_absolute_bound_exponent == F(69, 32)
    assert level_zero.type_i_power_deficit == F(5, 32)
    assert level_zero.ideal_level_cauchy_bound_exponent == F(69, 32)
    assert level_zero.ideal_level_cauchy_power_deficit == F(5, 32)
    assert level_zero.uniform_type_i_level_threshold == F(-5, 32)
    assert level_zero.uniform_ideal_cauchy_level_threshold == F(-5, 16)
    assert not level_zero.uniform_type_i_has_nonnegative_level_window
    assert not level_zero.uniform_ideal_cauchy_has_nonnegative_level_window

    endpoint = adapter(
        modulus_scale_exponent=F(3),
        numerator_product_exponent=F(5),
        target_exponent=F(2),
        exposed_level_box_exponent=F(1),
    )
    assert endpoint.type_i_absolute_bound_exponent == F(101, 32)
    assert endpoint.type_i_power_deficit == F(37, 32)
    assert endpoint.ideal_level_cauchy_bound_exponent == F(85, 32)
    assert endpoint.ideal_level_cauchy_power_deficit == F(21, 32)
    assert endpoint.selberg_fixed_level_bound_exponent == F(131, 64)
    assert endpoint.selberg_type_i_level_threshold == F(-3, 64)
    assert endpoint.selberg_ideal_cauchy_level_threshold == F(-3, 32)
    assert endpoint.selberg_ideal_cauchy_bound_exponent == F(163, 64)
    assert endpoint.selberg_ideal_cauchy_power_deficit == F(35, 64)
    assert endpoint.full_ramanujan_fixed_level_bound_exponent == F(3, 2)
    assert endpoint.full_ramanujan_type_i_level_threshold == F(1, 2)
    assert endpoint.full_ramanujan_ideal_cauchy_level_threshold == F(1)
    assert endpoint.full_ramanujan_ideal_cauchy_bound_exponent == F(2)
    assert endpoint.full_ramanujan_ideal_cauchy_power_margin == F(0)
    assert endpoint.linnik_range_hypothesis_holds
    assert endpoint.level_divisibility_estimate_occurs_in_bm_proof
    assert endpoint.exact_mobius_type_i_identity_available
    assert not endpoint.exceptional_spectrum_removed_for_level_family
    assert not endpoint.level_cauchy_bound_proved_for_qct_coefficients
    assert endpoint.product_compatible_hard_vertex_only
    assert not endpoint.physical_coupled_kernel_restored
    assert not endpoint.whole_mobius_gate_covered


def test_humphries_density_neutralizes_only_archimedean_exceptional_loss() -> None:
    adapter = getattr(
        coverage_audit,
        "humphries_exceptional_level_density_audit",
        None,
    )
    assert adapter is not None, "exceptional level-density audit is missing"

    hard = adapter(
        modulus_scale_exponent=F(3),
        numerator_product_scale_exponent=F(5),
        target_exponent=F(2),
        level_family_exponent=F(1),
    )
    assert hard.numerator_product_scale_exponent == F(5)
    assert hard.bessel_ratio_exponent == F(1)
    assert hard.ramanujan_theta == F(7, 64)
    assert hard.gamma0_density_slope == F(4)
    assert hard.humphries_count_exponent_at_theta == F(9, 16)
    assert hard.volume_normalized_count_exponent_at_theta == F(-7, 16)
    assert hard.ideal_ramanujan_level_cauchy_base_exponent == F(2)
    assert hard.finite_prime_hecke_loss_exponent == F(35, 64)
    assert hard.residual_exceptional_loss_exponent == F(0)
    assert hard.density_enhanced_bound_exponent == F(163, 64)
    assert hard.density_enhanced_power_deficit == F(35, 64)
    assert hard.maximum_level_allowed_by_target == F(1)
    assert hard.level_needed_to_neutralize_exceptional_growth == F(1, 4)
    assert hard.target_and_density_thresholds_compatible
    assert hard.density_numerically_neutralizes_archimedean_exceptional_growth
    assert hard.linnik_scale_dominates_level_family
    assert hard.density_theorem_is_positive_counting_input
    assert not hard.mobius_level_signs_used_by_density_theorem
    assert not hard.qct_spectral_weights_accepted
    assert not hard.exceptional_spectrum_gate_covered
    assert not hard.whole_mobius_gate_covered


def test_finite_prime_hecke_average_is_the_corrected_spectral_gate() -> None:
    adapter = getattr(
        coverage_audit,
        "finite_prime_hecke_average_audit",
        None,
    )
    assert adapter is not None, "finite-prime Hecke-average audit is missing"

    hard = adapter(
        kloosterman_modulus_exponent=F(3),
        left_hecke_index_exponent=F(5, 2),
        right_hecke_index_exponent=F(5, 2),
        level_exponent=F(1),
        target_exponent=F(2),
        ramanujan_theta=F(7, 64),
    )
    assert hard.numerator_product_exponent == F(5)
    assert hard.full_ramanujan_level_cauchy_base_exponent == F(2)
    assert hard.pointwise_finite_hecke_loss_exponent == F(35, 64)
    assert hard.pointwise_total_bound_exponent == F(163, 64)
    assert hard.pointwise_power_deficit == F(35, 64)
    assert hard.fixed_index_spectral_large_sieve_loss_exponent == F(3, 2)
    assert hard.fixed_index_total_bound_exponent == F(7, 2)
    assert hard.required_pre_cauchy_hecke_saving_exponent == F(35, 64)
    assert hard.required_post_saving_log_decay
    assert hard.pascadi_archimedean_exceptional_large_sieve_published
    assert not hard.pascadi_finite_place_extension_published
    assert not hard.mobius_entry_to_hecke_index_adapter_derived
    assert not hard.physical_coupled_kernel_restored
    assert not hard.finite_prime_hecke_gate_covered
    assert not hard.whole_mobius_gate_covered


def test_pre_cauchy_farey_dilate_family_reaches_only_the_zero_margin_endpoint() -> None:
    note = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "### 4.109b Fourier separation of the original Farey family cannot precede positive Cauchy",
        "\\tag{4.845e}",
        "\\tag{4.845f}",
        "\\tag{4.845j}",
        "farey_dilate_pre_cauchy_audit",
    ):
        assert marker in note

    adapter = getattr(
        coverage_audit,
        "farey_dilate_pre_cauchy_audit",
        None,
    )
    assert adapter is not None, "pre-Cauchy Farey-dilate audit is missing"

    hard = adapter(
        mobius_entry_exponent=F(3),
        shift_window_exponent=F(5, 2),
        left_dilate_exponent=F(1, 2),
        right_dilate_exponent=F(1, 2),
        gate_target_exponent=F(3499, 1000),
    )
    assert hard.fourier_arc_denominator_exponent == F(5, 2)
    assert hard.left_rescaled_arc_exponent == F(-2)
    assert hard.right_rescaled_arc_exponent == F(-2)
    assert hard.mobius_coefficient_energy_exponent == F(3)
    assert hard.left_one_dilate_bandwidth_excess_exponent == F(1, 2)
    assert hard.right_one_dilate_bandwidth_excess_exponent == F(1, 2)
    assert hard.left_one_dilate_local_l2_exponent == F(7, 2)
    assert hard.right_one_dilate_local_l2_exponent == F(7, 2)
    assert hard.left_family_positive_self_diagonal_exponent == F(7, 2)
    assert hard.right_family_positive_self_diagonal_exponent == F(7, 2)
    assert hard.left_family_cauchy_normalized_l2_exponent == F(7)
    assert hard.right_family_cauchy_normalized_l2_exponent == F(7)
    assert hard.separate_family_cauchy_bound_exponent == F(7)
    assert hard.separate_family_cauchy_zero_slack_deficit == F(7, 2)
    assert hard.ideal_joint_dilate_bound_exponent == F(7, 2)
    assert hard.ideal_joint_dilate_gate_deficit == F(1, 1000)
    assert hard.zero_slack_endpoint_exponent == F(7, 2)
    assert hard.ideal_joint_dilate_reaches_zero_slack_endpoint
    assert hard.ordinary_fourier_cauchy_loses_farey_window
    assert hard.shift_zero_mode_removed_before_cauchy
    assert not hard.positive_self_diagonal_removed_by_shift_centering
    assert hard.endpoint_requires_additional_logarithmic_or_power_saving
    assert not hard.published_joint_dilate_endpoint_saving_available
    assert not hard.physical_coupled_kernel_restored
    assert not hard.whole_mobius_gate_covered


def test_grouped_dilate_convolution_and_double_poisson_return_the_same_gate() -> None:
    note = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "### 4.109c Grouping the dilates and Poisson summing them are exact loops, not savings",
        "\\tag{4.845k}",
        "\\tag{4.845n}",
        "\\tag{4.845r}",
        "farey_dilate_convolution_poisson_audit",
    ):
        assert marker in note

    adapter = getattr(
        coverage_audit,
        "farey_dilate_convolution_poisson_audit",
        None,
    )
    assert adapter is not None, "dilate convolution--Poisson audit is missing"

    hard = adapter(
        mobius_entry_exponent=F(3),
        dilate_exponent=F(1, 2),
        shift_window_exponent=F(5, 2),
        gate_target_exponent=F(3499, 1000),
    )
    assert hard.grouped_product_length_exponent == F(7, 2)
    assert hard.semiprime_energy_witness_exponent == F(7, 2)
    assert hard.poisson_numerator_exponent == F(1, 2)
    assert hard.poisson_packet_width_exponent == F(-7, 2)
    assert hard.recovered_determinant_window_exponent == F(5, 2)
    assert hard.recovered_determinant_window_matches_original
    assert hard.complete_divisor_convolution_is_epsilon
    assert not hard.dyadic_divisor_window_is_complete
    assert hard.semiprime_witness_survives_dyadic_grouping
    assert hard.original_shift_centering_removes_equal_products
    assert hard.positive_cauchy_reintroduces_grouped_energy
    assert hard.double_dilate_poisson_returns_original_determinant
    assert not hard.dyadic_mobius_convolution_supplies_power_saving
    assert not hard.physical_coupled_kernel_restored
    assert not hard.whole_mobius_gate_covered


def test_smooth_hecke_product_average_removes_the_pointwise_finite_prime_loss() -> None:
    note = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "### 4.109d A smooth product-index average removes the finite-prime Ramanujan loss for newforms",
        "\\tag{4.845s}",
        "\\tag{4.845z}",
        "\\tag{4.845aa}",
        "smooth_hecke_product_mobius_audit",
    ):
        assert marker in note

    adapter = getattr(
        coverage_audit,
        "smooth_hecke_product_mobius_audit",
        None,
    )
    assert adapter is not None, "smooth Hecke-product Möbius audit is missing"

    hard = adapter(
        left_index_exponent=F(5, 2),
        right_index_exponent=F(5, 2),
        spectral_conductor_exponent=F(1),
        pointwise_ramanujan_theta=F(7, 64),
    )
    assert hard.product_index_exponent == F(5)
    assert hard.pointwise_finite_prime_loss_exponent == F(35, 64)
    assert hard.common_divisor_split_exponent == F(3, 2)
    assert hard.small_divisor_cusp_bound_exponent == F(5, 2)
    assert hard.large_divisor_mobius_pnt_bound_exponent == F(7, 2)
    assert hard.large_divisor_saving_over_index_volume == F(3, 2)
    assert hard.large_divisor_endpoint_has_arbitrary_log_decay
    assert hard.unramified_hecke_mobius_inversion_exact
    assert hard.cusp_l_function_is_entire
    assert hard.small_divisor_functional_equation_shift_valid
    assert hard.large_divisor_uses_only_rankin_selberg_and_mobius_pnt
    assert hard.pointwise_ramanujan_loss_removed_for_product_smooth_newforms
    assert hard.eisenstein_spectrum_requires_separate_existing_treatment
    assert hard.ramified_newform_local_factors_restored
    assert not hard.oldclass_coefficients_restored
    assert not hard.physical_coupled_kernel_restored
    assert not hard.finite_prime_hecke_gate_covered
    assert not hard.whole_mobius_gate_covered


def test_bm_oldclasses_preserve_the_smooth_product_index_endpoint() -> None:
    note = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "### 4.109e Blomer--Milićević oldclasses preserve the product-smooth endpoint",
        "\\tag{4.845ab}",
        "\\tag{4.845ag}",
        "smooth_hecke_oldclass_product_audit",
    ):
        assert marker in note

    adapter = getattr(
        coverage_audit,
        "smooth_hecke_oldclass_product_audit",
        None,
    )
    assert adapter is not None, "smooth Hecke oldclass audit is missing"

    hard = adapter(
        index_exponent=F(5, 2),
        ambient_level_exponent=F(1),
        ramanujan_theta=F(7, 64),
    )
    assert hard.minimum_common_divisor_split_exponent == F(3, 2)
    assert hard.newform_endpoint_exponent == F(7, 2)
    assert hard.oldclass_shift_saving_slope == F(57, 64)
    assert hard.worst_oldclass_endpoint_exponent == F(7, 2)
    assert hard.worst_oldclass_endpoint_attained_at_newform_shift_zero
    assert hard.bm_oldclass_fourier_formula_exact
    assert hard.bm_first_index_is_coprime_to_ambient_level
    assert hard.oldclass_divisor_allocations_have_subpower_cost
    assert hard.every_oldclass_cell_retains_mobius_pnt_log_decay
    assert hard.ramified_newform_identity_compatible
    assert hard.oldclass_product_smooth_model_covered
    assert not hard.physical_coupled_kernel_restored
    assert not hard.finite_prime_hecke_gate_covered
    assert not hard.whole_mobius_gate_covered


def test_physical_qct_bessel_kernel_has_zero_power_product_bandwidth() -> None:
    adapter = getattr(
        coverage_audit,
        "physical_qct_hecke_kernel_audit",
        None,
    )
    assert adapter is not None, "physical QCT Hecke-kernel audit is missing"

    note = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "### 4.109f The physical QCT--Bessel kernel has zero-power product bandwidth",
        "\\tag{4.845ah}",
        "\\tag{4.845am}",
        "physical_qct_hecke_kernel_audit",
    ):
        assert marker in note

    hard = adapter(
        left_index_exponent=F(5, 2),
        right_index_exponent=F(5, 2),
        ambient_level_exponent=F(1),
        exceptional_theta=F(7, 64),
    )
    assert hard.normalized_qct_kernel_dimension == 4
    assert hard.bessel_augmented_kernel_dimension == 5
    assert hard.weighted_fourier_derivative_order_slope == 8
    assert hard.bessel_mellin_contour_real_part == F(-1, 2)
    assert hard.maximum_exceptional_bessel_order == F(7, 32)
    assert hard.exceptional_contour_margin == F(9, 32)
    assert hard.spectral_conductor_exponent == F(1)
    assert hard.multiplicative_twist_bandwidth_exponent == F(0)
    assert hard.qct_fourier_tensorization_exact
    assert hard.weighted_fourier_nuclear_norm_is_polylogarithmic
    assert hard.same_sign_bessel_mellin_factorization_exact
    assert hard.opposite_sign_bessel_mellin_factorization_exact
    assert hard.bessel_product_dependence_separates_as_h_times_delta
    assert hard.real_spectral_tail_has_arbitrary_log_decay
    assert hard.holomorphic_tail_has_arbitrary_log_decay
    assert hard.exceptional_spectrum_stays_inside_fixed_contour
    assert hard.product_smooth_hecke_lemma_applies_to_every_kernel_component
    assert hard.oldclass_restoration_is_compatible
    assert hard.physical_qct_kernel_product_model_restored
    assert not hard.actual_qct_geometric_spectral_adapter_derived
    assert not hard.other_mobius_entry_weights_restored
    assert not hard.type_i_level_family_aggregation_proved
    assert not hard.finite_prime_hecke_gate_covered
    assert not hard.whole_mobius_gate_covered


def test_type_i_completion_has_inverse_scaled_kloosterman_obstruction() -> None:
    identity = getattr(
        coverage_audit,
        "type_i_atkin_lehner_cusp_identity",
        None,
    )
    assert identity is not None, "Type-I Atkin--Lehner identity is missing"
    exact = identity(
        entry_divisor=5,
        modulus_divisor=7,
        modulus=77,
        dual_index=3,
        product_index=8,
    )
    assert exact["modulus_is_allowed_for_cusp_pair"]
    assert exact["entry_scaling_permutes_reduced_residues"]
    assert exact["poisson_residue_multisets_match"]
    assert not exact["ordinary_kloosterman_matches_atkin_lehner_cusp_sum"]

    adapter = getattr(
        coverage_audit,
        "type_i_atkin_lehner_cusp_audit",
        None,
    )
    assert adapter is not None, "Type-I Atkin--Lehner audit is missing"

    note = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "### 4.109g Type-I completion leaves an inverse-scaled Kloosterman index",
        "\\tag{4.845an}",
        "\\tag{4.845ar}",
        "type_i_atkin_lehner_cusp_audit",
    ):
        assert marker in note

    hard = adapter(
        entry_scale_exponent=F(3),
        modulus_scale_exponent=F(3),
        product_index_exponent=F(5),
        entry_divisor_exponent=F(1, 2),
        modulus_divisor_exponent=F(1, 2),
    )
    assert hard.entry_quotient_exponent == F(5, 2)
    assert hard.poisson_dual_index_exponent == F(1, 2)
    assert hard.ambient_level_exponent == F(1)
    assert hard.standard_lifted_modulus_exponent == F(7, 2)
    assert hard.bessel_numerator_product_exponent == F(6)
    assert hard.bessel_ratio_inverse_square_exponent == F(1)
    assert hard.poisson_normalization_exponent == F(-1, 2)
    assert hard.poisson_prefactor_after_modulus_lift_exponent == F(3)
    assert hard.normalized_dual_hecke_l1_exponent == F(0)
    assert hard.type_i_identity_leaves_unweighted_quotient
    assert hard.entry_and_modulus_divisors_are_coprime
    assert hard.kiral_young_allowed_moduli_match_exactly
    assert not hard.kiral_young_kloosterman_formula_matches_exactly
    assert hard.inverse_scaled_kloosterman_obstruction_present
    assert hard.crt_product_modulus_lift_exact
    assert hard.squarefree_ramanujan_denominator_nonzero
    assert hard.coprimality_inclusion_exclusion_is_standard_level_family
    assert hard.atkin_lehner_newform_coefficients_match_up_to_sign
    assert hard.atkin_lehner_oldclass_coefficient_lists_are_permuted
    assert hard.zero_dual_mode_is_eisenstein_only
    assert hard.raw_poisson_dual_l1_normalization_is_zero_power
    assert not hard.nonzero_dual_hecke_average_has_no_positive_power_cost
    assert hard.physical_qct_bessel_kernel_restored
    assert hard.type_i_type_i_qct_to_standard_kuznetsov_derived
    assert not hard.type_i_type_i_qct_to_cusp_kuznetsov_derived
    assert not hard.signed_level_family_aggregation_proved
    assert not hard.type_ii_sectors_restored
    assert not hard.finite_prime_hecke_gate_covered
    assert not hard.whole_mobius_gate_covered


def test_type_i_cusp_adapter_rejects_inverse_scaling_counterexample() -> None:
    """Catch the false replacement of inverse(A) by A in the KY index."""
    identity = coverage_audit.type_i_atkin_lehner_cusp_identity(
        entry_divisor=2,
        modulus_divisor=1,
        modulus=5,
        dual_index=1,
        product_index=1,
    )
    assert identity["poisson_first_index_mod_modulus"] == 3
    assert identity["kiral_young_first_index_mod_modulus"] == 2
    assert not identity["ordinary_kloosterman_matches_atkin_lehner_cusp_sum"]


def test_inverse_scaled_kloosterman_has_exact_squarefree_modulus_lift() -> None:
    lift = coverage_audit.inverse_scaled_kloosterman_modulus_lift_identity(
        entry_divisor=2,
        modulus=5,
        dual_index=1,
        product_index=1,
    )
    assert lift["lifted_modulus"] == 10
    assert lift["ramanujan_factor"] == -1
    assert lift["ramanujan_factor_is_nonzero"]
    assert lift["crt_phase_multisets_match"]
    assert lift["lifted_kloosterman_equals_ramanujan_times_physical"]
    assert lift["poisson_prefactor_after_lift_numerator_multiplier"] == 2


def test_lifted_kuznetsov_cell_isolates_exact_level_projector_saving() -> None:
    cell = coverage_audit.lifted_kuznetsov_level_cell_audit(
        entry_scale_exponent=F(3),
        modulus_scale_exponent=F(3),
        entry_divisor_exponent=F(1, 2),
        modulus_divisor_exponent=F(1, 2),
        coprimality_divisor_exponent=F(0),
        product_index_exponent=F(5),
    )
    assert cell.poisson_dual_index_exponent == F(1, 2)
    assert cell.standard_lifted_modulus_exponent == F(7, 2)
    assert cell.lifted_second_index_exponent == F(11, 2)
    assert cell.bessel_numerator_product_exponent == F(6)
    assert cell.bessel_ratio_inverse_square_exponent == F(1)
    assert cell.poisson_lift_outer_prefactor_exponent == F(3)
    assert cell.actual_spectral_level_exponent == F(1)
    assert cell.sparse_support_square_excess_exponent == F(1, 2)
    assert cell.required_local_projector_amplitude_saving_exponent == F(1, 4)
    assert cell.active_bessel_ratio_matches_original_qct_ratio
    assert cell.crt_modulus_lift_is_exact_standard_kuznetsov_orbit
    assert not cell.exact_valuation_level_projector_bound_proved

    top = coverage_audit.lifted_kuznetsov_level_cell_audit(
        entry_scale_exponent=F(3),
        modulus_scale_exponent=F(3),
        entry_divisor_exponent=F(1, 2),
        modulus_divisor_exponent=F(1, 2),
        coprimality_divisor_exponent=F(1, 2),
        product_index_exponent=F(5),
    )
    assert top.actual_spectral_level_exponent == F(3, 2)
    assert top.sparse_support_square_excess_exponent == F(0)
    assert top.required_local_projector_amplitude_saving_exponent == F(0)


def test_unramified_prime_oldspace_cross_factor_has_exact_p_saving() -> None:
    local = coverage_audit.unramified_prime_oldspace_cross_factor_identity(
        prime=5,
        hecke_prime=F(3, 2),
    )
    assert local["oldclass_gram_denominator"] == F(11, 16)
    assert local["unsimplified_cross_factor"] == F(4, 11)
    assert local["simplified_cross_factor"] == F(4, 11)
    assert local["symbolic_simplification_exact"]
    assert local["generic_oldspace_cross_has_one_p_factor"]


def test_conductor_p_oldspace_cross_has_correct_ambient_trace_factor() -> None:
    raised = coverage_audit.conductor_p_raised_oldspace_cross_identity(
        prime=5,
        hecke_prime_square=F(1, 5),
    )
    assert raised["oldclass_gram_denominator"] == F(35, 36)
    assert raised["oldclass_normalization_squared"] == F(36, 35)
    assert raised["ambient_oldclass_cross_factor_relative_to_hecke_prime"] == F(6, 35)
    assert raised["level_p_squared_trace_factor_relative_to_level_p"] == F(6, 175)
    assert raised["level_difference_factor_relative_to_level_p"] == F(169, 175)
    assert not raised["raised_oldspace_cross_vanishes_exactly"]
    assert raised["primitive_conductor_p_squared_coefficient_at_p_times_unit_is_zero"]


def test_lifted_projector_gcd_partition_exactly_recovers_missing_saving() -> None:
    for bad in (F(0), F(1, 2), F(3, 2)):
        partition = coverage_audit.lifted_projector_gcd_partition_audit(
            entry_divisor_exponent=F(3, 2),
            bad_product_gcd_exponent=bad,
        )
        assert partition.generic_prime_amplitude_saving_exponent == (
            F(3, 2) - bad
        ) / 2
        assert partition.bad_divisor_density_amplitude_saving_exponent == bad / 2
        assert partition.combined_amplitude_saving_exponent == F(3, 4)
        assert partition.required_projector_amplitude_saving_exponent == F(3, 4)
        assert partition.gcd_partition_power_balance_exact
        assert partition.physical_product_divisor_density_used
        assert not partition.ramified_oldclass_subpower_norm_proved
        assert not partition.full_exact_valuation_projector_bound_proved


def test_unramified_oldspace_cross_prime_power_recurrence_is_exact() -> None:
    first_bad = coverage_audit.unramified_oldspace_cross_prime_power_identity(
        prime=5,
        hecke_prime=F(3, 2),
        extra_second_index_valuation=1,
    )
    assert first_bad["hecke_values"] == (F(1), F(3, 2), F(5, 4))
    assert first_bad["unsimplified_cross_factor"] == F(-10, 11)
    assert first_bad["recurrence_cross_factor"] == F(-10, 11)
    assert first_bad["recurrence_simplification_exact"]

    deeper = coverage_audit.unramified_oldspace_cross_prime_power_identity(
        prime=5,
        hecke_prime=F(3, 2),
        extra_second_index_valuation=2,
    )
    assert deeper["hecke_values"] == (F(1), F(3, 2), F(5, 4), F(3, 8))
    assert deeper["recurrence_cross_factor"] == F(-19, 11)
    assert deeper["recurrence_simplification_exact"]


def test_level_p_squared_extra_oldvector_cancels_the_level_p_remainder() -> None:
    for extra_valuation, expected_level_p in (
        (0, F(4, 11)),
        (1, F(-10, 11)),
        (2, F(-19, 11)),
    ):
        local = coverage_audit.unramified_level_p_squared_cross_identity(
            prime=5,
            hecke_prime=F(3, 2),
            extra_second_index_valuation=extra_valuation,
        )
        assert local["level_p_cross_factor"] == expected_level_p
        assert local["level_p_squared_extra_oldvector_cross_factor"] == (
            -expected_level_p
        )
        assert local["full_level_p_squared_oldclass_cross_factor"] == F(0)
        assert local["extra_oldvector_cancellation_exact"]


def test_unramified_exact_level_difference_retains_ramanujan_prime_saving() -> None:
    note = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "### 4.109y Exact-level differencing removes the bad valuation multiplicity",
        r"\tag{4.845cz}",
        r"\tag{4.845da}",
        "unramified_exact_level_difference_kernel",
    ):
        assert marker in note

    unit_ramified = coverage_audit.unramified_exact_level_difference_kernel(
        prime=5,
        hecke_prime=F(3, 2),
        first_index_valuation=0,
        second_index_valuation=1,
    )
    assert unit_ramified["level_p_trace_kernel"] == F(2, 33)
    assert unit_ramified["level_p_squared_trace_kernel"] == F(0)
    assert unit_ramified["exact_level_difference_kernel"] == F(2, 33)
    assert unit_ramified["ramanujan_normalized_kernel"] == F(-2, 33)

    bad_bad = coverage_audit.unramified_exact_level_difference_kernel(
        prime=5,
        hecke_prime=F(3, 2),
        first_index_valuation=1,
        second_index_valuation=1,
    )
    assert bad_bad["exact_level_difference_kernel"] == F(20, 33)
    assert bad_bad["ramanujan_normalized_kernel"] == F(5, 33)
    assert bad_bad["level_difference_identity_exact"]


def test_unramified_cross_index_kernel_has_exact_two_shift_factorization() -> None:
    note = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "### 4.109zfd The unramified cross-index kernel is an exact two-shift form",
        r"\tag{4.845dc_14s}",
        r"\tag{4.845dc_14t}",
        "unramified_cross_index_two_shift_identity",
    ):
        assert marker in note

    expected = {
        (0, 1): F(-2, 33),
        (1, 1): F(5, 33),
        (2, 1): F(19, 66),
        (2, 3): F(35, 264),
    }
    for (a, b), normalized in expected.items():
        local = coverage_audit.unramified_cross_index_two_shift_identity(
            prime=5,
            hecke_prime=F(3, 2),
            first_index_valuation=a,
            second_index_valuation=b,
        )
        assert local["gram_polynomial"] == F(99, 4)
        assert local["ramanujan_normalized_kernel"] == normalized
        assert local["rank_two_kernel"] == normalized
        assert local["rank_two_factorization_exact"]
        assert local["positive_valuation_hecke_shift_exact"]
        assert local["rank_two_matrix_determinant"] == F(-4, 99)
        assert local["cross_index_dependence_is_two_fourier_shifts"]
        assert not local["weighted_two_index_large_sieve_proved"]
        assert not local["pevp_proved"]


def test_steinberg_exact_level_difference_has_corrected_square_formula() -> None:
    unit = coverage_audit.steinberg_exact_level_difference_kernel_square(
        prime=5,
        first_index_valuation=0,
        second_index_valuation=1,
    )
    unit_factor = F(1) - F(6, 25 * 7)
    assert unit["ambient_oldclass_r_factor"] == F(35, 36)
    assert unit["level_trace_ratio"] == F(1, 5)
    assert unit["euler_correction_factor"] == unit_factor
    assert unit["ramanujan_normalized_kernel_square"] == F(1, 5) * unit_factor**2
    assert unit["required_prime_square_saving_met"]

    both = coverage_audit.steinberg_exact_level_difference_kernel_square(
        prime=5,
        first_index_valuation=2,
        second_index_valuation=3,
    )
    both_factor = F(1) + F(1, 25 * 7 * 4)
    assert both["euler_correction_factor"] == both_factor
    assert both["ramanujan_normalized_kernel_square"] == F(1, 5**5) * both_factor**2
    assert both["closed_formula_exact"]
    assert not both["previous_target_equality_exact"]


def test_steinberg_cross_index_kernel_is_exact_rank_one() -> None:
    note = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "### 4.109zfe The Steinberg cross-index kernel is rank one",
        r"\tag{4.845dc_14u}",
        r"\tag{4.845dc_14v}",
        "steinberg_cross_index_rank_one_identity",
    ):
        assert marker in note

    local = coverage_audit.steinberg_cross_index_rank_one_identity(prime=5)
    assert local["oldclass_gram_factor"] == F(35, 36)
    assert local["unit_positive_ambient_oldvector_cross_ratio"] == F(-29, 35)
    assert local["positive_positive_ambient_oldvector_cross_ratio"] == F(841, 35)
    assert local["unit_first_rank_one_multiplier"] == F(-169, 175)
    assert local["positive_first_rank_one_multiplier"] == F(-701, 700)
    assert local["unit_first_multiplier_square"] == F(28561, 30625)
    assert local["positive_first_multiplier_square"] == F(491401, 490000)
    assert local["rank_one_factorization_exact"]
    assert local["positive_multiplier_euler_correction_order_at_least_four"]
    assert local["steinberg_conductor_square_mass_is_p_inverse_times_bounded_euler"]
    assert not local["ramified_eisenstein_transfer_proved"]
    assert not local["weighted_harmonic_large_sieve_proved"]
    assert not local["pevp_proved"]


def test_trivial_nebentypus_eisenstein_has_no_conductor_p_cell() -> None:
    note = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "### 4.109zff Trivial-nebentypus Eisenstein conductors are locally even",
        r"\tag{4.845dc_14w}",
        r"\tag{4.845dc_14x}",
        "trivial_nebentypus_eisenstein_conductor_audit",
    ):
        assert marker in note

    local = coverage_audit.trivial_nebentypus_eisenstein_conductor_audit(
        prime=5,
        primitive_character_conductor_exponent=1,
        positive_index_valuation=3,
    )
    assert local["first_character_conductor_exponent"] == 1
    assert local["second_character_conductor_exponent"] == 1
    assert local["primitive_gl2_conductor_exponent"] == 2
    assert local["conductor_exponent_one_absent"]
    assert local["positive_valuation_hecke_coefficient"] == F(0)
    assert local["ramified_conductor_two_cross_index_kernel"] == F(0)
    assert local["continuous_local_cross_index_transfer_proved"]
    assert not local["uniform_polylog_harmonic_large_sieve_proved"]
    assert not local["pevp_proved"]


def test_corrected_steinberg_formula_needs_the_global_reinsertion_for_pevp() -> None:
    """The local formula is insufficient alone; the completed PLS closes it."""
    local = coverage_audit.steinberg_exact_level_difference_kernel_square(
        prime=5,
        first_index_valuation=0,
        second_index_valuation=1,
    )
    assert local["closed_formula_exact"]
    assert not local["previous_target_equality_exact"]

    primitive = coverage_audit.primitive_conductor_level_difference_audit(
        level_factor_exponent=F(3),
        common_mobius_length_exponent=F(3, 2),
        fixed_power_margin=F(0),
    )
    assert primitive.weighted_primitive_large_sieve_proved
    assert primitive.pevp_proved

    final = coverage_audit.unconditional_long_mollifier_asymptotic_audit()
    assert final.pevp_proved
    assert not final.full_remainder_is_little_o_T
    assert not final.unconditional_asymptotic_proved
    assert final.residual_cell_count > 0


def test_ambient_newform_normalization_indices_are_exact_at_p_and_p_squared() -> None:
    index = coverage_audit.gamma0_subgroup_index_ratio
    assert index(primitive_level=1, ambient_level=5) == 6
    assert index(primitive_level=1, ambient_level=25) == 30
    assert index(primitive_level=5, ambient_level=25) == 5
    assert index(primitive_level=6, ambient_level=150) == 30


def test_primitive_conductor_rearrangement_and_polylog_large_sieve_prove_pevp() -> None:
    note = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "### 4.109z Primitive-conductor regrouping is exact and exposes the epsilon-free gate",
        r"\tag{4.845db}",
        r"\tag{4.845dc}",
        r"\tag{PLS}_{Q_0}",
        "primitive_conductor_level_difference_audit",
    ):
        assert marker in note

    audit = coverage_audit.primitive_conductor_level_difference_audit(
        level_factor_exponent=F(3),
        common_mobius_length_exponent=F(3, 2),
        fixed_power_margin=F(0),
    )
    assert audit.ambient_normalization_formula_exact
    assert audit.same_bessel_test_retained_at_every_level
    assert audit.finite_level_and_primitive_conductor_sums_interchanged_exactly
    assert audit.unramified_local_amplitude_saving_exponent == F(1)
    assert audit.unramified_after_density_amplitude_saving_exponent == F(3, 2)
    assert audit.steinberg_local_amplitude_saving_exponent == F(1, 2)
    assert audit.required_projector_square_saving_exponent == F(1)
    assert audit.conductor_two_positive_valuation_vanishes
    assert audit.primitive_subset_overhead_log_exponent == F(1, 2)
    assert audit.signed_square_conductor_overhead_is_polylogarithmic
    assert audit.diagonal_conductor_euler_sum_is_polylogarithmic
    assert audit.length_conductor_euler_sum_is_polylogarithmic
    assert audit.vinogradov_korobov_decay_log_exponent == F(3, 5)
    assert audit.vinogradov_korobov_dominates_subset_overhead
    assert not audit.published_large_sieve_has_explicit_polylog_constant
    assert audit.custom_full_level_harmonic_large_sieve_has_polylog_constant
    assert audit.primitive_family_is_positive_full_level_subfamily
    assert audit.unramified_cross_index_two_shift_transfer_proved
    assert audit.steinberg_cross_index_rank_one_transfer_proved
    assert audit.continuous_local_cross_index_transfer_proved
    assert audit.all_local_cross_index_transfers_proved
    assert audit.shifted_support_does_not_exceed_original_support
    assert audit.pevp_reduced_to_uniform_polylog_harmonic_large_sieve
    assert audit.maass_eisenstein_full_level_large_sieve_proved
    assert audit.holomorphic_weight_ge_four_large_sieve_proved
    assert audit.holomorphic_weight_two_large_sieve_proved
    assert audit.all_archimedean_sectors_reinserted
    assert audit.pevp_is_polynomial_in_fixed_kernel_seminorms
    assert audit.weighted_primitive_large_sieve_proved
    assert audit.pevp_proved


def test_normalized_level_difference_has_a_positive_square_kernel_not_a_pure_layer() -> None:
    note = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "### 4.109za The normalized level difference squares to a positive two-layer kernel",
        r"\tag{4.845dc_1}",
        r"\tag{4.845dc_2}",
        r"\tag{4.845dc_3}",
        "normalized_level_difference_pbk_audit",
    ):
        assert marker in note

    audit = coverage_audit.normalized_level_difference_pbk_audit(prime=5)
    assert audit.prime == 5
    assert audit.level_p_index == 6
    assert audit.level_p_squared_index == 30
    assert audit.ambient_oldspace_eigenvalue == F(2, 15)
    assert audit.exact_layer_eigenvalue == F(-1, 30)
    assert audit.squared_ambient_oldspace_weight == F(4, 225)
    assert audit.squared_exact_layer_weight == F(1, 900)
    assert audit.squared_kernel_identity_mass == F(2, 15)
    assert audit.modulus_valuation_one_kloosterman_coefficient == F(1, 10)
    assert audit.modulus_valuation_at_least_two_kloosterman_coefficient == F(2, 15)
    assert audit.primitive_character_valuation_one_ftb_ratio == F(15, 16)
    assert audit.primitive_character_higher_valuation_ftb_ratio == F(5, 4)
    assert audit.principal_character_valuation_one_ftb_ratio == F(3, 16)
    assert audit.local_geometric_conductor_exponent == 1
    assert audit.exact_layer_geometric_conductor_exponent == 1
    assert audit.normalized_difference_is_not_pure_exact_layer
    assert audit.squared_kernel_is_positive_orthogonal_layer_sum
    assert audit.local_ftb_euler_factor_is_p_over_p_minus_one
    assert audit.global_ftb_product_is_polylogarithmic
    assert not audit.hpy_named_spectral_assumption_applies
    assert not audit.epsilon_free_positive_kernel_large_sieve_proved
    assert not audit.pevp_proved

    dyadic = coverage_audit.normalized_level_difference_pbk_audit(prime=2)
    assert dyadic.modulus_valuation_one_kloosterman_coefficient == 0
    assert dyadic.local_geometric_conductor_exponent == 2
    assert dyadic.exact_layer_geometric_conductor_exponent == 1


def test_common_level_primitive_farey_family_has_epsilon_free_sparse_spacing() -> None:
    note = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "### 4.109zb Primitive character orthogonality removes the ramified-modulus count",
        r"\tag{4.845dc_4}",
        r"\tag{4.845dc_5}",
        "primitive_sparse_farey_large_sieve_audit",
    ):
        assert marker in note

    audit = coverage_audit.primitive_sparse_farey_large_sieve_audit(
        common_level=30,
        dyadic_modulus_bound=300,
        mellin_interval_length=7,
        sequence_length=1000,
    )
    assert audit.minimum_spacing == F(1, 12000)
    assert audit.inverse_spacing_bound == 12000
    assert audit.hybrid_large_sieve_bound == 85000
    assert audit.crt_fraction_is_reduced
    assert audit.distinct_fraction_spacing_proved
    assert audit.primitive_gauss_orthogonality_is_exact
    assert audit.ramified_modulus_count_removed
    assert audit.fixed_common_level_gain_is_epsilon_free
    assert not audit.noncoprime_index_cells_covered
    assert not audit.positive_kernel_harmonic_large_sieve_proved
    assert not audit.pevp_proved


def test_noncoprime_prime_power_kloosterman_cells_have_an_exact_finite_recursion() -> None:
    note = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "### 4.109zc Noncoprime Kloosterman cells reduce by exact valuation recursion",
        r"\tag{4.845dc_6}",
        r"\tag{4.845dc_7}",
        "prime_power_kloosterman_valuation_reduction",
    ):
        assert marker in note

    reduce = coverage_audit.prime_power_kloosterman_valuation_reduction
    assert reduce(prime=5, modulus_exponent=1, left_valuation=2, right_valuation=2) == {
        "kind": "trivial_phase",
        "integer_multiplier": 4,
        "reduced_modulus_exponent": 0,
        "vanishes": False,
    }
    assert reduce(prime=5, modulus_exponent=2, left_valuation=2, right_valuation=2) == {
        "kind": "trivial_phase",
        "integer_multiplier": 20,
        "reduced_modulus_exponent": 0,
        "vanishes": False,
    }
    assert reduce(prime=5, modulus_exponent=4, left_valuation=2, right_valuation=2) == {
        "kind": "unit_unit_reduction",
        "integer_multiplier": 25,
        "reduced_modulus_exponent": 2,
        "vanishes": False,
    }
    assert reduce(prime=5, modulus_exponent=2, left_valuation=1, right_valuation=3) == {
        "kind": "unequal_ramanujan_boundary",
        "integer_multiplier": -5,
        "reduced_modulus_exponent": 1,
        "vanishes": False,
    }
    assert reduce(prime=5, modulus_exponent=3, left_valuation=1, right_valuation=3)[
        "vanishes"
    ]

    audit = coverage_audit.physical_noncoprime_valuation_audit(prime=5)
    assert audit.ramanujan_inverse_square_natural_mean == F(13, 16)
    assert audit.common_positive_valuation_collision_mass == F(1, 24)
    assert audit.same_valuation_tail_reduces_to_primitive_farey_family
    assert audit.unequal_valuation_tail_vanishes_after_boundary_modulus
    assert audit.local_main_density_euler_correction_is_absolutely_summable
    assert not audit.smooth_short_interval_boundary_aggregated
    assert not audit.positive_kernel_harmonic_large_sieve_proved
    assert not audit.pevp_proved


def test_valuation_boundary_divisor_convolution_has_a_uniform_euler_mean() -> None:
    note = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "### 4.109zd The valuation boundary is a bounded divisor-convolution mean",
        r"\tag{4.845dc_8}",
        r"\tag{4.845dc_9}",
        "valuation_boundary_euler_majorant_audit",
    ):
        assert marker in note

    audit = coverage_audit.valuation_boundary_euler_majorant_audit(
        ramified_primes=(2, 3, 5),
    )
    assert audit.local_collision_coefficients == (F(2), F(3, 4), F(5, 16))
    assert audit.main_euler_product == F(2277, 512)
    assert audit.smooth_interval_mean_bound == F(2277, 256)
    assert audit.divisor_convolution_identity_exact
    assert audit.boundary_term_absorbed_by_one_over_d
    assert audit.euler_product_uniformly_bounded
    assert audit.smooth_short_interval_boundary_aggregated
    assert not audit.positive_kernel_harmonic_large_sieve_proved
    assert not audit.pevp_proved


def test_ambient_normalization_rejects_the_positive_kernel_as_a_pevp_closure() -> None:
    note = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "### 4.109ze Ambient normalization reverses the raw positive-kernel saving",
        r"\tag{4.845dc_10}",
        r"\tag{4.845dc_11}",
        "ambient_normalized_positive_kernel_cauchy_audit",
    ):
        assert marker in note

    audit = coverage_audit.ambient_normalized_positive_kernel_cauchy_audit(prime=5)
    assert audit.ambient_level_index == 30
    assert audit.relative_ambient_oldspace_eigenvalue == 4
    assert audit.relative_exact_layer_eigenvalue == -1
    assert audit.ambient_normalized_squared_mass == 4
    assert audit.required_pevp_squared_mass == F(1, 5)
    assert audit.squared_mass_deficit_ratio == 20
    assert audit.common_ambient_measure_inserted_exactly
    assert audit.raw_plancherel_mass_is_not_the_pevp_normalization
    assert audit.index_rescaling_does_not_repair_diagonal_mass
    assert audit.cross_index_oldvector_cancellation_still_required
    assert not audit.positive_square_kernel_closes_pevp
    assert not audit.pevp_proved


def test_full_level_harmonic_large_sieve_polylog_constant_is_still_open() -> None:
    note = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "### 4.109zf Sparse Farey spacing reduces the full-level harmonic large sieve to its transforms",
        r"\tag{4.845dc_12}",
        r"\tag{4.845dc_13}",
        r"\tag{4.845dc_14}",
        "full_level_harmonic_large_sieve_audit",
    ):
        assert marker in note

    audit = coverage_audit.full_level_harmonic_large_sieve_audit(
        level=30,
        dyadic_modulus_bound=300,
        mellin_interval_length=7,
        sequence_length=1000,
    )
    assert audit.minimum_farey_spacing == F(1, 12000)
    assert audit.hybrid_dyadic_inner_bound == 85000
    assert audit.kloosterman_indices_may_be_noncoprime_to_level
    assert audit.full_level_spectral_measure_is_positive
    assert audit.primitive_family_is_positive_subfamily
    assert audit.small_bessel_tail_has_polylog_mean_divisor_bound
    assert audit.archimedean_partition_has_polylog_total_variation
    assert audit.hpy_first_mellin_requires_bessel_scale_above_spectral_square
    assert audit.power_sized_large_bessel_range_covered
    assert not audit.large_bessel_range_requires_new_estimate
    assert audit.maass_and_eisenstein_sectors_covered
    assert audit.holomorphic_sector_covered
    assert audit.uniform_polylog_harmonic_large_sieve_proved


def test_exact_dyadic_mellin_route_closes_every_zero_power_spectral_block() -> None:
    note = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "### 4.109zfa Exact dyadic Mellin inversion removes the raw-volume error, not PEVP",
        r"\tag{4.845dc_14a}",
        r"\tag{4.845dc_14f}",
        "pointwise transform formula as negligible",
        "weight-two Petersson tail",
        "dyadic_bessel_mellin_block_audit",
    ):
        assert marker in note

    block_audit = coverage_audit.dyadic_bessel_mellin_block_audit

    for modulus_exponent in (F(0), F(4), F(5), F(6)):
        block = block_audit(
            sequence_length_exponent=F(5),
            level_exponent=F(3),
            modulus_exponent=modulus_exponent,
            spectral_scale_exponent=F(0),
        )
        assert block.target_exponent == F(2)
        assert not block.pointwise_hpy_remainder_discarded_before_large_sieve
        assert block.exact_dyadic_mellin_inversion_used
        assert block.mellin_remainder_routed_through_gallagher
        assert block.maass_and_eisenstein_block_covered
        assert block.holomorphic_block_covered
        assert block.physical_full_level_block_covered
        assert block.hybrid_gallagher_uses_mellin_linfty_weight
        assert not block.uniform_stationary_phase_seminorm_bound_proved

    large = block_audit(
        sequence_length_exponent=F(5),
        level_exponent=F(3),
        modulus_exponent=F(0),
        spectral_scale_exponent=F(0),
    )
    assert large.large_bessel_range
    assert large.large_mellin_effective_width_exponent == F(5)
    assert large.large_mellin_linfty_prefactor_exponent == F(-5)
    assert large.large_mellin_l1_exponent == F(0)
    assert large.large_mellin_l1_is_not_prefactor_exponent

    boundary = block_audit(
        sequence_length_exponent=F(5),
        level_exponent=F(3),
        modulus_exponent=F(5),
        spectral_scale_exponent=F(0),
    )
    assert not boundary.large_bessel_range
    assert boundary.small_block_first_exponent == F(2)
    assert boundary.small_block_second_exponent == F(0)

    positive_power_spectrum = block_audit(
        sequence_length_exponent=F(5),
        level_exponent=F(3),
        modulus_exponent=F(5),
        spectral_scale_exponent=F(1, 10),
    )
    assert not positive_power_spectrum.physical_full_level_block_covered


def test_exact_archimedean_symbol_route_is_remainder_free_and_weight_two_is_separate() -> None:
    note = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "### 4.109zfg Exact Hankel symbols remove the polylog spectral remainder",
        r"\tag{4.845dc_14xa}",
        r"\tag{4.845dc_14xc}",
        "weight-two Petersson tail",
        "exact_archimedean_mellin_transfer_audit",
    ):
        assert marker in note

    large = coverage_audit.exact_archimedean_mellin_transfer_audit(
        spectral_scale=8,
        bessel_scale=1024,
        maass_zero_order=4,
        minimum_holomorphic_weight=2,
    )
    assert large.large_symbol_range
    assert large.exact_maass_fourier_kernel_retained
    assert large.no_spectral_power_remainder_discarded
    assert large.same_sign_hankel_symbol_bound_proved
    assert large.opposite_sign_nonstationary_bound_proved
    assert large.holomorphic_large_weight_symbol_bound_proved
    assert large.large_mellin_linfty_bound_proved
    assert not large.transition_mellin_l1_bound_used
    assert large.maass_small_argument_tail_power == 8
    assert large.maass_small_argument_tail_summable
    assert large.weight_two_petersson_tail_proved
    assert large.all_archimedean_sectors_and_endpoints_proved
    assert not large.uniform_polylog_harmonic_large_sieve_proved

    transition = coverage_audit.exact_archimedean_mellin_transfer_audit(
        spectral_scale=8,
        bessel_scale=32,
        maass_zero_order=4,
        minimum_holomorphic_weight=4,
    )
    assert not transition.large_symbol_range
    assert transition.transition_mellin_l1_bound_used
    assert transition.transition_mellin_l1_bound_proved
    assert transition.holomorphic_small_argument_tail_power == 3
    assert transition.holomorphic_small_argument_tail_summable
    assert transition.all_archimedean_sectors_and_endpoints_proved
    assert not transition.uniform_polylog_harmonic_large_sieve_proved


def test_weight_two_large_sieve_uses_incomplete_eisenstein_count_not_petersson_tail() -> None:
    note = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "### 4.109zfga The weight-two endpoint is a cusp-strip large sieve",
        r"\tag{4.845dc_14xd}",
        r"\tag{4.845dc_14xg}",
        "weight_two_incomplete_eisenstein_large_sieve_audit",
    ):
        assert marker in note

    audit = coverage_audit.weight_two_incomplete_eisenstein_large_sieve_audit(
        level=25,
        sequence_length=1000,
    )
    assert audit.level == 25
    assert audit.sequence_length == 1000
    assert audit.ford_representative_maximizes_infinity_height
    assert audit.cosets_are_primitive_pairs_with_level_dividing_c
    assert audit.transformed_height_support_lower_bound == F(1, 2000)
    assert audit.nonzero_c_pair_count_bound == 640
    assert audit.incomplete_eisenstein_sup_bound == 641
    assert audit.unfolding_coefficient_is_uniformly_positive_on_dyadic_sequence
    assert audit.fourier_indices_may_share_factors_with_level
    assert audit.oldforms_are_included
    assert not audit.physical_weight_two_transform_vanishes_identically
    assert audit.weight_two_harmonic_large_sieve_proved
    assert not audit.reinserted_into_full_pls


def test_signed_level_difference_becomes_an_exact_valuation_farey_family() -> None:
    note = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "### 4.109zfb Direct geometric differencing preserves the two Fourier indices",
        r"\tag{4.845dc_14g}",
        r"\tag{4.845dc_14k}",
        r"\tag{4.845dc_14m}",
        r"\tag{4.845dc_14n}",
        "joint two-coordinate Gallagher/dispersion",
        "PEVP flags false",
        "exact_level_geometric_fiber_audit",
    ):
        assert marker in note

    audit = coverage_audit.exact_level_geometric_fiber_audit(
        mobius_level=30,
        fixed_level=7,
        cofactor=11,
        first_fourier_index=7,
        dyadic_modulus_bound=5000,
    )
    assert audit.modulus == 2310
    assert audit.signed_level_divisor_coefficient == 1
    assert audit.exact_valuation_cell_active
    assert audit.reduced_second_denominator == 77
    assert audit.unit_reduction_fiber_size == 8
    assert audit.first_farey_spacing == F(210, 4 * 5000 * 5000)
    assert audit.second_farey_spacing == F(6300, 4 * 5000 * 5000)
    assert audit.fiber_weighted_second_inverse_spacing <= (
        audit.first_inverse_spacing
    )
    assert audit.two_geometric_spacing_terms_share_level_AB
    assert audit.ramanujan_fiber_sum == -1
    assert audit.ramanujan_denominator_nonzero
    assert audit.crt_fiber_character_is_a_unit_permutation
    assert audit.ramanujan_denominator_cancels_before_cauchy
    assert audit.inverse_scaled_kloosterman_family_restored_exactly
    assert audit.reciprocity_retains_two_coupled_phase_coordinates
    assert audit.cross_index_phase_retained_before_cauchy
    assert audit.premature_length_term_removed_by_ramanujan_cancellation
    assert audit.joint_two_coordinate_bound_still_required
    assert not audit.pevp_proved

    excluded = coverage_audit.exact_level_geometric_fiber_audit(
        mobius_level=30,
        fixed_level=7,
        cofactor=55,
        first_fourier_index=7,
        dyadic_modulus_bound=5000,
    )
    assert excluded.signed_level_divisor_coefficient == 0
    assert not excluded.exact_valuation_cell_active


def test_coupled_farey_collision_is_a_quadratic_divisor_constraint() -> None:
    note = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "### 4.109zfc Absolute two-coordinate spacing is exactly the old quadratic-divisor majorant",
        r"\tag{4.845dc_14o}",
        r"\tag{4.845dc_14q}",
        r"\tag{4.845dc_14r}",
        "same DCV/quadratic-divisor",
        "coupled_farey_collision_audit",
    ):
        assert marker in note

    audit = coverage_audit.coupled_farey_collision_audit(
        scaling_level=5,
        first_denominator=7,
        first_numerator=2,
        second_denominator=11,
        second_numerator=3,
    )
    assert audit.first_inverse_numerator == 2
    assert audit.second_inverse_numerator == 8
    assert audit.first_determinant_coordinate == 1
    assert audit.second_determinant_coordinate == -34
    assert audit.first_quadratic_divisor_integer == -49
    assert audit.second_quadratic_divisor_integer == -121
    assert audit.first_denominator_divides_first_quadratic_integer
    assert audit.second_denominator_divides_second_quadratic_integer
    assert audit.denominators_are_coprime
    assert audit.coordinate_pairs_unique_for_fixed_determinants
    assert audit.absolute_collision_count_becomes_quadratic_divisor_majorant
    assert audit.absolute_majorant_discards_mobius_signs
    assert not audit.new_saving_beyond_bblr_proved
    assert not audit.joint_two_coordinate_large_sieve_proved


def test_tail_shell_ledger_closes_from_seminorm_stable_pevp() -> None:
    note = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "### 4.109zg Seminorm-stable PEVP sums every AFE and transform tail shell",
        r"\tag{4.845dc_15}",
        r"\tag{4.845dc_16}",
        r"\tag{4.845dc_17}",
        "mwkf_tail_shell_aggregation_audit",
    ):
        assert marker in note

    audit = coverage_audit.mwkf_tail_shell_aggregation_audit(
        tail_log_start=F(100),
        seminorm_decay_order=F(4),
        local_seminorm_log_loss=F(20),
        target_log_saving=F(20),
    )
    assert audit.dyadic_and_harmonic_q_log_loss == F(7)
    assert audit.net_tail_log_saving == F(373)
    assert audit.net_tail_log_saving > audit.target_log_saving
    assert audit.exact_afe_has_no_truncation_error
    assert audit.afe_product_tail_included
    assert audit.time_nonstationary_tail_included
    assert audit.poisson_frequency_tail_included
    assert audit.qct_fourier_mellin_tail_included
    assert audit.pevp_is_polynomial_in_fixed_kernel_seminorms
    assert audit.power_far_shells_are_dominated
    assert audit.polylog_near_shells_are_summable
    assert audit.transform_tail_aggregated
    assert audit.afe_tail_aggregated
    assert audit.total_tail_is_little_o_T


def test_final_theta_three_certificate_retains_one_analytic_residual_cell() -> None:
    note = ALTERNATIVE_ROUTES_NOTE.read_text()
    assert "unconditional asymptotic proved" not in note
    for marker in (
        "### 4.109zh The exact main term leaves only the small-entry compact gate",
        r"\tag{4.845dc_18}",
        r"\tag{4.845dc_19}",
        r"\tag{4.845dc_20}",
        r"\tag{LSEG}_{K,q}^{L}",
        "unconditional_long_mollifier_asymptotic_audit",
        "analytic remainder gate open",
    ):
        assert marker in note

    audit = coverage_audit.unconditional_long_mollifier_asymptotic_audit()
    assert audit.mollifier_length_exponent == 3
    assert audit.main_term_constant == F(4, 3)
    assert audit.exact_completed_afe_proved
    assert audit.poisson_zero_mode_normalization_proved
    assert audit.lcm_main_term_asymptotic_proved
    assert audit.pevp_proved
    assert not audit.compact_nonzero_poisson_core_is_little_o_T
    assert audit.transform_tail_is_little_o_T
    assert audit.afe_tail_is_little_o_T
    assert audit.archimedean_correction_is_beyond_all_powers
    assert not audit.full_remainder_is_little_o_T
    assert not audit.unconditional_asymptotic_proved
    assert audit.residual_cell_count == 1
    assert audit.proof_status == "analytic remainder gate open"


def test_physical_exact_valuation_projector_has_only_power_level_coverage() -> None:
    projector = coverage_audit.physical_exact_valuation_projector_audit(
        ramanujan_theta=F(7, 64),
    )
    assert projector.required_prime_amplitude_saving_exponent == F(1, 2)
    assert projector.generic_unramified_oldspace_saving_exponent == F(57, 64)
    assert projector.generic_unramified_cell_closes
    assert not projector.conductor_p_raised_oldspace_cancels
    assert projector.conductor_p_squared_positive_valuation_vanishes
    assert projector.bad_product_valuation_density_closes
    assert projector.poisson_ramanujan_denominator_closes_positive_valuation
    assert projector.level_p_squared_extra_oldvector_closes
    assert projector.continuous_local_cases_close
    assert projector.prime_local_bounds_tensor_with_subpower_cost
    assert projector.bad_gcd_cell_square_multiplicity_base == 4
    assert projector.divisor_partition_tensor_square_residual_base == 5
    assert projector.power_exponent_exact_valuation_projector_covered
    assert not projector.prime_local_bounds_tensor_with_polylog_cost
    assert not projector.physical_product_exact_valuation_projector_proved
    assert not projector.arbitrary_coefficient_exact_valuation_projector_proved
    assert not projector.outer_qct_normalization_aggregated
    assert not projector.whole_mobius_gate_covered


def test_lifted_outer_qct_core_aggregates_with_exact_seven_log_ledger() -> None:
    text = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "### 4.109w The lifted nonzero Poisson core has a seven-log aggregation",
        "### 4.109x The valuation tensor isolates the PEVP square function",
        r"\tag{4.845cv}",
        r"\tag{4.845cw}",
        r"\tag{4.845cx}",
        r"\tag{4.845cy}",
        r"\tag{PEVP}_{A,B}",
    ):
        assert marker in text

    core = coverage_audit.lifted_outer_qct_aggregation_audit(
        left_entry_exponent=F(3),
        right_entry_exponent=F(2),
        q_exponent=F(0),
        gate_log_power=F(10),
        common_orientation="left",
    )
    assert core.completed_entry_exponent in (F(3), F(2))
    assert core.other_entry_exponent in (F(3), F(2))
    assert core.lifted_inner_target_exponent == core.other_entry_exponent
    assert core.reconstructed_kloosterman_core_target_exponent == F(5)
    assert core.outer_box_exponent == F(1)
    assert core.dyadic_parameter_log_loss == F(6)
    assert core.harmonic_q_log_loss == F(1)
    assert core.total_aggregation_log_loss == F(7)
    assert core.net_log_saving == F(3)
    assert core.single_orientation_used_for_all_spectral_components
    assert core.power_exponent_exact_valuation_projector_used
    assert core.polylog_tensor_projector_gate_proved
    assert core.symmetric_completion_uses_larger_entry_divisor
    assert core.large_entry_divisor_range_uses_pevp_power
    assert core.small_entry_divisor_lifted_gate_stated_exactly
    assert not core.product_hecke_pnt_uniformly_covers_small_entry_cells
    assert not core.collapsed_gcd_to_lifted_entry_adapter_exact
    assert not core.polylog_entry_divisor_range_uses_outer_pnt
    assert not core.logarithmic_entry_divisor_split_is_complete
    assert core.ratio_gcd_layers_retained_inside_local_gate
    assert not core.nonzero_poisson_core_is_little_o_T
    assert core.polylogarithmic_transform_tail_aggregated
    assert core.afe_tail_aggregated
    assert not core.whole_mobius_gate_covered


def test_eisenstein_second_moment_reciprocity_does_not_yet_prove_slf() -> None:
    local_identity = getattr(
        coverage_audit,
        "hecke_double_dirichlet_local_identity",
        None,
    )
    assert local_identity is not None, "Hecke double-series identity is missing"
    identity = local_identity(hecke_prime=F(3, 2), max_exponent=8)
    assert identity["all_coefficients_match"]
    assert identity["checked_pairs"] == 81

    adapter = getattr(
        coverage_audit,
        "eisenstein_second_moment_reciprocity_audit",
        None,
    )
    assert adapter is not None, "Eisenstein second-moment audit is missing"

    note = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "### 4.109h The inverse-zeta zero does not by itself prove level reciprocity",
        "\\tag{4.845as}",
        "\\tag{4.845av}",
        "eisenstein_second_moment_reciprocity_audit",
    ):
        assert marker in note

    hard = adapter(
        entry_divisor_exponent=F(1, 2),
        modulus_divisor_exponent=F(1, 2),
    )
    assert hard.ambient_level_exponent == F(1)
    assert hard.required_half_level_saving_exponent == F(1, 2)
    assert hard.required_endpoint_log_decay
    assert hard.hecke_double_dirichlet_identity_exact
    assert hard.inverse_zeta_central_zero_order == 1
    assert hard.eisenstein_transverse_pole_order == 1
    assert hard.local_crossing_model == "x/y"
    assert not hard.inverse_zeta_zero_cancels_residues_jointly
    assert hard.blomer_khan_total_degree == 8
    assert hard.target_total_degree == 4
    assert not hard.blomer_khan_is_literal_adapter
    assert not hard.andersen_kiral_is_literal_adapter
    assert hard.khan_zeta_dual_family == "Dirichlet characters"
    assert not hard.khan_prime_gaussian_formula_is_composite_smooth_adapter
    assert hard.completed_eisenstein_residue_pairing_required
    assert hard.composite_level_local_corrections_required
    assert not hard.signed_level_family_aggregation_proved
    assert not hard.type_ii_sectors_restored
    assert not hard.whole_mobius_gate_covered


def test_product_hecke_large_sieve_leaves_eisenstein_type_i_gate() -> None:
    energy = getattr(
        coverage_audit,
        "hecke_multiply_coefficient_energy",
        None,
    )
    assert energy is not None, "Hecke multiplication energy checker is missing"
    finite = energy(
        hecke_index=12,
        coefficients={5: F(2), 6: F(-3), 10: F(1)},
    )
    assert finite["input_energy"] == F(14)
    assert finite["output_energy"] <= finite["divisor_square_bound"]
    assert finite["output_support_maximum"] <= 120

    adapter = getattr(
        coverage_audit,
        "product_hecke_spectral_large_sieve_audit",
        None,
    )
    assert adapter is not None, "product-Hecke spectral large-sieve audit is missing"

    note = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "### 4.109i Product-Hecke large sieve closes the cuspidal Type-I/Type-I gate",
        "\\tag{4.845aw}",
        "\\tag{4.845az}",
        "product_hecke_spectral_large_sieve_audit",
    ):
        assert marker in note

    balanced = adapter(
        product_variable_exponent=F(5, 2),
        entry_divisor_exponent=F(1, 2),
        modulus_divisor_exponent=F(1, 2),
    )
    assert balanced.ambient_level_exponent == F(1)
    assert balanced.chosen_poisson_divisor_exponent == F(1, 2)
    assert balanced.common_divisor_threshold_exponent == F(3, 2)
    assert balanced.maximum_residual_hecke_length_exponent == F(1)
    assert balanced.hecke_multiplied_length_exponent == F(3, 2)
    assert balanced.large_common_divisor_bound_exponent == F(11, 4)
    assert balanced.previous_pointwise_bound_exponent == F(7, 2)
    assert balanced.fixed_level_saving_exponent == F(3, 4)
    assert balanced.ramanujan_theta == F(7, 64)
    assert balanced.small_common_divisor_hecke_loss_exponent == F(7, 128)
    assert balanced.small_common_divisor_slf_margin == F(57, 128)
    assert balanced.aggregated_bound_exponent == F(7, 4)
    assert balanced.required_slf_exponent == F(2)
    assert balanced.slf_power_margin == F(1, 4)
    assert balanced.completion_uses_shorter_divisor_side
    assert balanced.standard_large_sieve_normalization_exact
    assert balanced.hecke_multiplication_has_subpower_energy_cost
    assert balanced.atkin_lehner_oldclass_permutation_preserves_l2
    assert balanced.eisenstein_basis_change_is_unitary
    assert balanced.physical_kernel_tensorization_compatible
    assert balanced.small_common_divisor_range_covered
    assert balanced.cuspidal_holomorphic_type_i_type_i_slf_proved
    assert balanced.continuous_ramified_oldvector_gate_open
    assert not balanced.type_i_type_i_slf_proved
    assert not balanced.type_ii_sectors_restored
    assert not balanced.whole_mobius_gate_covered

    unbalanced = adapter(
        product_variable_exponent=F(5, 2),
        entry_divisor_exponent=F(1),
        modulus_divisor_exponent=F(0),
    )
    assert unbalanced.chosen_poisson_divisor_exponent == F(0)
    assert unbalanced.large_common_divisor_bound_exponent == F(5, 2)
    assert unbalanced.aggregated_bound_exponent == F(3, 2)
    assert unbalanced.required_slf_exponent == F(2)
    assert unbalanced.slf_power_margin == F(1, 2)
    assert unbalanced.cuspidal_holomorphic_type_i_type_i_slf_proved
    assert not unbalanced.type_i_type_i_slf_proved

    bounded = adapter(
        product_variable_exponent=F(5, 2),
        entry_divisor_exponent=F(0),
        modulus_divisor_exponent=F(0),
    )
    assert bounded.slf_power_margin == F(0)
    assert bounded.bounded_level_cell_uses_existing_mobius_log_decay
    assert bounded.cuspidal_holomorphic_type_i_type_i_slf_proved
    assert not bounded.type_i_type_i_slf_proved

    for a_num in range(9):
        for b_num in range(9 - a_num):
            alpha = F(a_num, 8)
            beta = F(b_num, 8)
            cell = adapter(
                product_variable_exponent=F(5, 2),
                entry_divisor_exponent=alpha,
                modulus_divisor_exponent=beta,
            )
            assert cell.slf_power_margin == max(alpha, beta) / 2
            assert cell.cuspidal_holomorphic_type_i_type_i_slf_proved
            assert not cell.type_i_type_i_slf_proved


def test_alternative_routes_note_has_no_ascii_control_characters() -> None:
    data = ALTERNATIVE_ROUTES_NOTE.read_bytes()
    forbidden = {
        byte
        for byte in data
        if byte < 32 and byte not in (9, 10, 13)
    }
    assert forbidden == set()


def test_high_level_product_hecke_sieve_isolates_type_ii_square() -> None:
    adapter = getattr(
        coverage_audit,
        "high_level_product_hecke_spectral_audit",
        None,
    )
    assert adapter is not None, "high-level product-Hecke audit is missing"

    note = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "### 4.109j The Type-II residual is a closed level square",
        "\\tag{4.845ba}",
        "\\tag{4.845bd}",
        "high_level_product_hecke_spectral_audit",
    ):
        assert marker in note

    center = adapter(
        product_variable_exponent=F(5, 2),
        left_level_factor_exponent=F(5, 4),
        right_level_factor_exponent=F(5, 4),
    )
    assert center.ambient_level_exponent == F(5, 2)
    assert center.maximum_residual_hecke_length_exponent == F(5, 2)
    assert center.chosen_poisson_index_exponent == F(5, 4)
    assert center.large_sieve_excess_exponent == F(5, 4)
    assert center.aggregated_bound_exponent == F(17, 8)
    assert center.target_exponent == F(2)
    assert center.power_deficit == F(1, 8)
    assert center.maximum_type_ii_deficit == F(1, 8)
    assert center.maximum_deficit_witness == (F(5, 4), F(5, 4))
    assert center.type_ii_factor_to_cusp_adapter_exact
    assert center.product_hecke_large_sieve_applies
    assert center.inside_closed_type_ii_residual_square
    assert not center.power_bound_closes_cell
    assert not center.endpoint_log_decay_required
    assert not center.type_ii_cell_covered
    assert not center.whole_type_ii_region_covered

    outside = adapter(
        product_variable_exponent=F(5, 2),
        left_level_factor_exponent=F(1),
        right_level_factor_exponent=F(2),
    )
    assert outside.large_sieve_excess_exponent == F(1, 2)
    assert outside.aggregated_bound_exponent == F(7, 4)
    assert outside.power_saving_margin == F(1, 4)
    assert not outside.inside_closed_type_ii_residual_square
    assert outside.power_bound_closes_cell
    assert outside.type_ii_cell_covered

    boundary = adapter(
        product_variable_exponent=F(5, 2),
        left_level_factor_exponent=F(1),
        right_level_factor_exponent=F(3, 2),
    )
    assert boundary.large_sieve_excess_exponent == F(1)
    assert boundary.power_deficit == F(0)
    assert boundary.endpoint_log_decay_required
    assert not boundary.endpoint_log_decay_proved
    assert not boundary.type_ii_cell_covered

    for a_num in range(8, 25):
        for b_num in range(8, 25):
            alpha = F(a_num, 8)
            beta = F(b_num, 8)
            cell = adapter(
                product_variable_exponent=F(5, 2),
                left_level_factor_exponent=alpha,
                right_level_factor_exponent=beta,
            )
            expected_residual = (
                F(1) <= alpha <= F(3, 2)
                and F(1) <= beta <= F(3, 2)
            )
            assert cell.inside_closed_type_ii_residual_square == expected_residual
            assert cell.type_ii_cell_covered == (not expected_residual)


def test_primal_dual_hecke_sieve_leaves_ramified_eisenstein_gate() -> None:
    adapter = getattr(
        coverage_audit,
        "primal_dual_product_hecke_spectral_audit",
        None,
    )
    assert adapter is not None, "primal-dual product-Hecke audit is missing"

    note = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "### 4.109k Functional-equation duality removes the cuspidal Type-II square",
        "\\tag{4.845be}",
        "\\tag{4.845bi}",
        "primal_dual_product_hecke_spectral_audit",
    ):
        assert marker in note

    center = adapter(
        product_variable_exponent=F(5, 2),
        left_level_factor_exponent=F(5, 4),
        right_level_factor_exponent=F(5, 4),
        primitive_conductor_exponent=F(5, 2),
    )
    assert center.ambient_level_exponent == F(5, 2)
    assert center.chosen_poisson_index_exponent == F(5, 4)
    assert center.worst_primitive_conductor_exponent == F(5, 2)
    assert center.primal_dual_transition_exponent == F(5, 4)
    assert center.normalized_m_times_sqrt_conductor_exponent == F(0)
    assert center.optimized_large_sieve_excess_exponent == F(0)
    assert center.product_spectral_bound_exponent == F(5, 2)
    assert center.aggregated_bound_exponent == F(3, 2)
    assert center.target_exponent == F(2)
    assert center.power_saving_margin == F(1, 2)
    assert center.primitive_functional_equation_exact
    assert center.dual_coefficient_energy_matches_primal
    assert center.gamma_transform_has_polylog_nuclear_norm
    assert center.oldclass_conductor_split_has_subpower_cost
    assert center.squarefree_level_forces_trivial_eisenstein_character
    assert center.eisenstein_unramified_hecke_index_has_divisor_bound
    assert center.eisenstein_ramified_oldvector_witness_prime == 5
    assert center.eisenstein_ramified_oldvector_ratio_at_witness == F(3)
    assert not center.eisenstein_ramified_oldvector_has_divisor_bound
    assert not center.continuous_spectrum_has_no_positive_m_power
    assert center.cuspidal_holomorphic_sectors_covered
    assert not center.all_type_i_ii_sectors_covered
    assert not center.finite_prime_hecke_gate_covered
    assert not center.transform_tail_aggregated
    assert not center.whole_mobius_gate_covered

    for a_num in range(0, 25):
        for b_num in range(0, 25):
            alpha = F(a_num, 8)
            beta = F(b_num, 8)
            level = alpha + beta
            cell = adapter(
                product_variable_exponent=F(5, 2),
                left_level_factor_exponent=alpha,
                right_level_factor_exponent=beta,
                primitive_conductor_exponent=level,
            )
            assert cell.normalized_m_times_sqrt_conductor_exponent <= F(0)
            assert cell.optimized_large_sieve_excess_exponent == F(0)
            assert cell.aggregated_bound_exponent == F(3, 2)
            assert cell.cuspidal_holomorphic_sectors_covered
            assert not cell.all_type_i_ii_sectors_covered


def test_eisenstein_oldspace_projector_localizes_loss_to_common_ramification() -> None:
    adapter = getattr(
        coverage_audit,
        "eisenstein_oldspace_projector_audit",
        None,
    )
    assert adapter is not None, "Eisenstein oldspace projector audit is missing"

    note = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "### 4.109l The same-cusp Eisenstein projector localizes the loss",
        "\\tag{4.845bj}",
        "\\tag{4.845bm}",
        "eisenstein_oldspace_projector_audit",
    ):
        assert marker in note

    audit = adapter(prime=5)
    assert audit.individual_ramified_ratio_at_witness == F(3)
    assert audit.coprime_coprime_projector == {0: F(6, 25)}
    assert audit.coprime_once_ramified_projector == {
        -1: F(1, 25),
        0: F(1, 25),
    }
    assert audit.once_ramified_once_ramified_projector == {
        -1: F(-4, 25),
        0: F(22, 25),
        1: F(-4, 25),
    }
    assert audit.oldspace_sum_factorizes_prime_by_prime
    assert audit.coprime_ramified_projector_gains_one_prime
    assert audit.local_loss_depends_only_on_common_ramification
    assert audit.same_cusp_global_kernel_has_gcd_over_level_majorant
    assert not audit.atkin_lehner_cross_cusp_projector_identified
    assert not audit.same_cusp_projector_is_physical_adapter
    assert not audit.common_ramification_gcd_aggregation_proved
    assert not audit.continuous_spectrum_gate_covered
    assert not audit.whole_mobius_gate_covered


def test_common_ramification_gcd_has_zero_power_poisson_average() -> None:
    adapter = getattr(
        coverage_audit,
        "eisenstein_common_ramification_average_audit",
        None,
    )
    assert adapter is not None, "common-ramification average audit is missing"

    note = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "### 4.109m The Poisson average absorbs common ramification in the same-cusp model",
        "\\tag{4.845bn}",
        "\\tag{4.845bo}",
        "eisenstein_common_ramification_average_audit",
    ):
        assert marker in note

    for frequency_length in range(1, 25):
        for index in range(1, 31):
            for level in range(1, 31):
                audit = adapter(
                    frequency_length=frequency_length,
                    second_index=index,
                    ambient_level=level,
                )
                assert audit.gcd_divisor_totient_identity_exact
                assert audit.exact_frequency_gcd_sum <= audit.divisor_bound_upper_bound
                assert audit.normalized_average_has_zero_power_cost
                assert audit.same_cusp_poisson_frequency_gcd_aggregation_proved
                assert not audit.physical_cross_cusp_gcd_aggregation_proved
                assert not audit.completed_eisenstein_residue_pairing_proved
                assert not audit.continuous_spectrum_gate_covered


def test_pole_subtracted_eisenstein_functional_equation_isolates_residues() -> None:
    adapter = getattr(
        coverage_audit,
        "pole_subtracted_eisenstein_functional_equation_audit",
        None,
    )
    assert adapter is not None, "pole-subtracted Eisenstein audit is missing"

    note = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "### 4.109n Pole subtraction dualizes the Eisenstein polynomial",
        "\\tag{4.845bp}",
        "\\tag{4.845bs}",
        "pole_subtracted_eisenstein_functional_equation_audit",
    ):
        assert marker in note

    hard = adapter(
        primal_length_exponent=F(5, 4),
        spectral_bandwidth_exponent=F(0),
    )
    assert hard.archimedean_conductor_exponent == F(0)
    assert hard.dual_length_exponent == F(-5, 4)
    assert hard.effective_dual_length_exponent == F(0)
    assert hard.completed_zeta_product_functional_equation_exact
    assert hard.two_simple_residues_exact
    assert hard.central_collision_limit_is_finite
    assert hard.central_collision_log_y_coefficient == F(1)
    assert hard.central_collision_euler_gamma_coefficient == F(2)
    assert hard.pole_subtracted_transform_has_rapid_decay
    assert hard.same_cusp_projector_and_poisson_gcd_audited
    assert not hard.atkin_cross_cusp_oldspace_restored
    assert not hard.nonresidual_continuous_local_polynomial_covered
    assert not hard.zero_mode_residue_pairing_proved
    assert not hard.continuous_spectrum_gate_covered
    assert not hard.whole_mobius_gate_covered


def test_ramanujan_zero_mode_has_exact_inverse_zeta_euler_factor() -> None:
    local = getattr(
        coverage_audit,
        "ramanujan_prime_power_generating_polynomial",
        None,
    )
    audit_adapter = getattr(
        coverage_audit,
        "ramanujan_zero_mode_euler_audit",
        None,
    )
    assert local is not None
    assert audit_adapter is not None

    note = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "### 4.109o The Ramanujan zero mode carries the inverse-zeta factor",
        "\\tag{4.845bt}",
        "\\tag{4.845bv}",
        "ramanujan_zero_mode_euler_audit",
    ):
        assert marker in note

    assert local(prime=5, valuation=0) == {0: 1, 1: -1}
    assert local(prime=5, valuation=1) == {0: 1, 1: 4, 2: -5}
    assert local(prime=5, valuation=2) == {0: 1, 1: 4, 2: 20, 3: -25}

    audit = audit_adapter(prime=5, valuation=2)
    assert audit.ramanujan_prime_power_coefficients_exact
    assert audit.local_generating_identity_exact
    assert audit.global_dirichlet_series_identity_exact
    assert audit.inverse_zeta_zero_order_at_one == 1
    assert audit.archimedean_zero_mode_residue_normalization_matched is False
    assert audit.completed_zero_mode_residue_pairing_proved is False
    assert audit.continuous_spectrum_gate_covered is False


def test_prime_level_eisenstein_cross_cusp_keeps_half_level_deficit() -> None:
    adapter = getattr(
        coverage_audit,
        "prime_level_eisenstein_cross_cusp_audit",
        None,
    )
    assert adapter is not None, "prime cross-cusp audit is missing"

    note = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "### 4.109p The physical cross-cusp projector retains a half-level deficit",
        "\\tag{4.845bw}",
        "\\tag{4.845bx}",
        "prime_level_eisenstein_cross_cusp_audit",
    ):
        assert marker in note

    audit = adapter(prime=5)
    assert audit.unramified_diagonal_cusp_value_at_t_zero == F(-1, 5)
    assert audit.once_ramified_diagonal_cusp_value_at_t_zero == F(8, 5)
    assert audit.offdiagonal_cusp_value_squared_at_t_zero == F(5, 16)
    assert audit.mixed_cross_projector_squared_at_t_zero == F(49, 80)
    assert audit.mixed_cross_projector_asymptotic_prime_exponent == F(-1)
    assert audit.same_cusp_candidate_squared_prime_exponent == F(-2)
    assert audit.half_level_loss_vs_same_cusp_candidate == F(1, 2)
    assert audit.kiral_young_specialization_exact
    assert audit.physical_cross_cusp_projector_identified
    assert audit.same_cusp_projector_candidate_rejected
    assert audit.cross_cusp_half_level_saving_proved
    assert not audit.global_residue_level_ledger_restored
    assert not audit.continuous_spectrum_gate_covered


def test_completed_eisenstein_residue_is_exact_level_frequency_trilinear_gate() -> None:
    adapter = getattr(
        coverage_audit,
        "completed_eisenstein_residue_trilinear_audit",
        None,
    )
    assert adapter is not None, "completed residue trilinear audit is missing"

    note = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "### 4.109q The completed Eisenstein residue is a three-variable gate",
        "\\tag{4.845by}",
        "\\tag{4.845ca}",
        "completed_eisenstein_residue_trilinear_audit",
    ):
        assert marker in note

    center = adapter(
        left_level_factor_exponent=F(5, 4),
        right_level_factor_exponent=F(5, 4),
        product_variable_exponent=F(5, 2),
    )
    assert center.ambient_level_exponent == F(5, 2)
    assert center.poisson_frequency_exponent == F(5, 4)
    assert center.primal_residue_bound_exponent == F(17, 8)
    assert center.target_exponent == F(2)
    assert center.required_saving_exponent == F(1, 8)
    assert center.maximum_required_saving_exponent == F(1, 8)
    assert center.maximum_saving_witness == (F(5, 4), F(5, 4))
    assert center.residue_expansion_term_count == 3
    assert center.remaining_arithmetic_variable_count == 3
    assert center.grouped_left_mobius_coefficient_exact
    assert center.grouped_right_mobius_coefficient_exact
    assert center.kiral_young_cross_kernel_exact
    assert center.pole_subtracted_identity_exact
    assert not center.signed_level_frequency_trilinear_estimate_proved
    assert not center.continuous_spectrum_gate_covered
    assert not center.whole_mobius_gate_covered


def test_cross_cusp_ramification_density_is_only_a_local_candidate() -> None:
    adapter = getattr(
        coverage_audit,
        "eisenstein_cross_cusp_ramification_density_audit",
        None,
    )
    assert adapter is not None, "cross-cusp density audit is missing"

    note = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "### 4.109r Ramification density gives a local candidate, not a closure",
        "\\tag{4.845cb}",
        "\\tag{4.845cd}",
        "eisenstein_cross_cusp_ramification_density_audit",
    ):
        assert marker in note

    audit = adapter(
        prime=5,
        left_level_factor_exponent=F(5, 4),
        right_level_factor_exponent=F(5, 4),
    )
    assert audit.expected_absolute_diagonal_cusp_factor == F(13, 25)
    assert audit.offdiagonal_cusp_factor_squared == F(5, 16)
    assert audit.cross_average_majorant_squared == F(169, 500)
    assert audit.cross_average_squared_prime_exponent == F(-3)
    assert audit.same_cusp_average_squared_prime_exponent == F(-2)
    assert audit.extra_cross_density_amplitude_saving_exponent == F(1)
    assert audit.center_pre_density_bound_exponent == F(17, 8)
    assert audit.candidate_center_density_saving_exponent == F(5, 4)
    assert audit.candidate_center_post_density_bound_exponent == F(7, 8)
    assert audit.smooth_interval_boundary_has_divisor_subpower_cost
    assert audit.unrestricted_two_index_density_bound_proved
    assert audit.candidate_density_would_close_center
    assert not audit.physical_tensor_preserves_unrestricted_density
    assert not audit.residue_residue_terms_covered
    assert not audit.residue_dual_mixed_terms_covered
    assert not audit.completed_residue_trilinear_gate_covered
    assert not audit.continuous_local_gate_covered
    assert not audit.global_ratio_gcd_aggregation_proved
    assert not audit.whole_mobius_gate_covered


def test_cross_cusp_l2_density_closes_nonzero_continuous_residual_square() -> None:
    adapter = getattr(
        coverage_audit,
        "eisenstein_cross_cusp_l2_density_audit",
        None,
    )
    assert adapter is not None, "cross-cusp L2 density audit is missing"

    note = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "### 4.109s The L2 ramification density closes the nonzero continuous square",
        "\\tag{4.845ce}",
        "\\tag{4.845ch}",
        "eisenstein_cross_cusp_l2_density_audit",
    ):
        assert marker in note

    audit = adapter(
        prime=5,
        left_level_factor_exponent=F(5, 4),
        right_level_factor_exponent=F(5, 4),
    )
    assert audit.product_index_factor_count == 2
    assert audit.expected_squared_product_index_diagonal_factor == F(182, 125)
    assert audit.unramified_poisson_diagonal_factor_squared == F(1, 25)
    assert audit.cross_second_moment_majorant == F(187, 200)
    assert audit.cross_second_moment_prime_exponent == F(-2)
    assert audit.extra_cross_density_amplitude_saving_exponent == F(1, 2)
    assert audit.center_pre_density_bound_exponent == F(17, 8)
    assert audit.center_density_saving_exponent == F(5, 8)
    assert audit.center_post_density_bound_exponent == F(3, 2)
    assert audit.residual_square_post_bound_exponent == F(3, 2)
    assert audit.target_exponent == F(2)
    assert audit.residual_square_margin_exponent == F(1, 2)
    assert audit.qct_product_weights_separated
    assert audit.common_divisor_prime_allocations_have_subpower_cost
    assert audit.weighted_crt_boundary_absorbed_on_residual_square
    assert audit.physical_cross_cusp_nonzero_mode_covered
    assert not audit.completed_residue_decomposition_needed
    assert audit.original_common_mellin_zero_mode_main_term_proved
    assert not audit.separate_spectral_residue_pairing_needed
    assert not audit.global_ratio_gcd_aggregation_proved
    assert not audit.whole_mobius_gate_covered


def test_balanced_spectral_factor_polytope_is_fully_covered() -> None:
    adapter = getattr(
        coverage_audit,
        "balanced_spectral_factor_polytope_audit",
        None,
    )
    assert adapter is not None, "balanced factor-polytope audit is missing"

    note = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "### 4.109t Every balanced factor cell has a half-power margin",
        "\\tag{4.845ci}",
        "\\tag{4.845ck}",
        "\\tag{4.845cl}",
        "\\tag{4.845cm}",
        "\\tag{4.845cn}",
        "cross_cusp_density_boundary_audit",
        "balanced_spectral_factor_polytope_audit",
    ):
        assert marker in note

    center = adapter(
        left_level_factor_exponent=F(5, 4),
        right_level_factor_exponent=F(5, 4),
    )
    assert center.product_variable_exponent == F(5, 2)
    assert center.ambient_level_exponent == F(5, 2)
    assert center.shorter_level_factor_exponent == F(5, 4)
    assert center.maximum_residual_hecke_length_exponent == F(5, 2)
    assert center.primal_large_sieve_excess_exponent == F(5, 4)
    assert center.primal_excess_never_exceeds_shorter_factor
    assert center.cuspidal_normalized_excess_exponent == F(0)
    assert center.cuspidal_holomorphic_bound_exponent == F(3, 2)
    assert center.continuous_bound_exponent == F(3, 2)
    assert center.universal_factor_cell_bound_exponent == F(3, 2)
    assert center.target_exponent == F(2)
    assert center.fixed_margin_exponent == F(1, 2)
    assert center.type_i_type_i_cells_covered
    assert center.mixed_type_i_type_ii_cells_covered
    assert center.type_ii_type_ii_cells_covered
    assert center.balanced_hard_geometry_all_factor_cells_covered
    assert not center.unbalanced_original_exponent_polytope_covered
    assert not center.polylogarithmic_transform_tail_aggregated
    assert not center.whole_mobius_gate_covered

    edge = adapter(
        left_level_factor_exponent=F(3),
        right_level_factor_exponent=F(3),
    )
    assert edge.weighted_crt_square_decay_exponent == F(5)
    assert edge.effective_cross_density_square_saving_exponent == F(2)
    assert edge.effective_cross_density_amplitude_saving_exponent == F(1)
    assert not edge.weighted_crt_main_term_dominates
    assert edge.continuous_bound_exponent == F(1, 2)
    assert edge.universal_factor_cell_bound_exponent == F(3, 2)
    assert edge.balanced_hard_geometry_all_factor_cells_covered


def test_cross_cusp_density_ledger_retains_short_interval_boundaries() -> None:
    adapter = getattr(
        coverage_audit,
        "cross_cusp_density_boundary_audit",
        None,
    )
    assert adapter is not None, "cross-cusp boundary audit is missing"

    center = adapter(
        shorter_level_factor_exponent=F(5, 4),
        left_product_variable_exponent=F(5, 2),
        right_product_variable_exponent=F(5, 2),
    )
    assert center.pointwise_square_decay_exponent == F(5, 4)
    assert center.weighted_crt_square_decay_exponent == F(5, 2)
    assert center.two_variable_square_saving_exponent == F(5, 4)
    assert center.one_variable_gcd_square_saving_exponent == F(0)
    assert center.effective_square_saving_exponent == F(5, 4)
    assert center.effective_amplitude_saving_exponent == F(5, 8)
    assert center.weighted_crt_main_term_dominates

    short = adapter(
        shorter_level_factor_exponent=F(3),
        left_product_variable_exponent=F(5, 2),
        right_product_variable_exponent=F(5, 2),
    )
    assert short.weighted_crt_square_decay_exponent == F(5)
    assert short.two_variable_square_saving_exponent == F(2)
    assert short.one_variable_gcd_square_saving_exponent == F(0)
    assert short.effective_square_saving_exponent == F(2)
    assert short.effective_amplitude_saving_exponent == F(1)
    assert not short.weighted_crt_main_term_dominates

    degenerate = adapter(
        shorter_level_factor_exponent=F(1),
        left_product_variable_exponent=F(0),
        right_product_variable_exponent=F(1),
    )
    assert degenerate.weighted_crt_square_decay_exponent == F(1)
    assert degenerate.two_variable_square_saving_exponent == F(0)
    assert degenerate.one_variable_gcd_square_saving_exponent == F(1)
    assert degenerate.effective_square_saving_exponent == F(1)
    assert degenerate.effective_amplitude_saving_exponent == F(1, 2)
    assert degenerate.positive_density_saving_available
    assert not degenerate.on_exact_zero_density_saving_face
    assert degenerate.zero_density_saving_face_characterization_exact

    zero_face = adapter(
        shorter_level_factor_exponent=F(2),
        left_product_variable_exponent=F(1),
        right_product_variable_exponent=F(1),
    )
    assert zero_face.effective_square_saving_exponent == F(0)
    assert zero_face.on_exact_zero_density_saving_face
    assert zero_face.zero_density_saving_face_characterization_exact


def test_balanced_completion_density_absorbs_unequal_product_excess() -> None:
    adapter = getattr(
        coverage_audit,
        "balanced_completion_unequal_product_audit",
        None,
    )
    assert adapter is not None, "unequal-product completion audit is missing"

    note = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "### 4.109u Unequal product lengths leave no normalized continuous excess",
        "\\tag{4.845co}",
        "\\tag{4.845cp}",
        "balanced_completion_unequal_product_audit",
    ):
        assert marker in note

    unequal = adapter(
        left_level_factor_exponent=F(1, 2),
        right_level_factor_exponent=F(1, 2),
        left_product_variable_exponent=F(1),
        right_product_variable_exponent=F(5, 4),
    )
    assert unequal.ambient_level_exponent == F(1)
    assert unequal.shorter_level_factor_exponent == F(1, 2)
    assert unequal.common_divisor_split_exponent == F(1, 4)
    assert unequal.poisson_multiplied_residual_exponent == F(3, 4)
    assert unequal.large_sieve_excess_exponent == F(1, 4)
    assert unequal.effective_density_square_saving_exponent == F(1, 2)
    assert unequal.density_amplitude_saving_exponent == F(1, 4)
    assert unequal.large_sieve_excess_absorbed_by_density

    zero_face = adapter(
        left_level_factor_exponent=F(1),
        right_level_factor_exponent=F(1),
        left_product_variable_exponent=F(1, 2),
        right_product_variable_exponent=F(1, 2),
    )
    assert zero_face.on_exact_zero_density_saving_face
    assert zero_face.large_sieve_excess_exponent == F(0)
    assert zero_face.zero_density_face_has_zero_large_sieve_excess
    assert zero_face.all_unequal_product_cells_normalized_excess_covered
    assert not zero_face.unbalanced_entry_scale_normalization_derived
    assert not zero_face.whole_mobius_gate_covered


def test_unbalanced_completion_orientations_cover_normalized_spectral_excess() -> None:
    adapter = getattr(
        coverage_audit,
        "unbalanced_completion_orientation_audit",
        None,
    )
    assert adapter is not None, "unbalanced orientation audit is missing"

    note = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "### 4.109v CRT lift and reciprocity close the normalized spectral excess",
        "\\tag{4.845cq}",
        "\\tag{4.845cs}",
        "unbalanced_completion_orientation_audit",
    ):
        assert marker in note

    audit = adapter(
        left_entry_exponent=F(3),
        right_entry_exponent=F(2),
        left_level_factor_exponent=F(3, 2),
        right_level_factor_exponent=F(1),
        left_product_variable_exponent=F(2),
        right_product_variable_exponent=F(2),
    )
    assert audit.ambient_level_exponent == F(5, 2)
    assert audit.left_poisson_exponent == F(1, 2)
    assert audit.right_poisson_exponent == F(2)
    assert audit.left_large_sieve_excess_exponent == F(0)
    assert audit.right_large_sieve_excess_exponent == F(3, 2)
    assert audit.left_density_square_saving_exponent == F(3, 2)
    assert audit.right_density_square_saving_exponent == F(1)
    assert audit.continuous_chosen_orientation == "left"
    assert audit.continuous_some_orientation_closes
    assert audit.cuspidal_chosen_poisson_exponent == F(1, 2)
    assert audit.cuspidal_primal_dual_normalized_excess_exponent == F(-3, 4)
    assert audit.cuspidal_holomorphic_normalized_excess_closes
    assert audit.common_spectral_orientation == "left"
    assert audit.single_orientation_closes_all_spectral_components
    assert audit.conditional_standard_kuznetsov_factor_model_covered
    assert audit.inverse_scaled_kloosterman_adapter_derived
    assert audit.lifted_non_squarefree_level_family_covered
    assert audit.all_normalized_spectral_factor_cells_covered
    assert not audit.outer_qct_unbalanced_normalization_derived
    assert not audit.polylogarithmic_transform_tail_aggregated
    assert not audit.whole_mobius_gate_covered

    inactive = adapter(
        left_entry_exponent=F(3),
        right_entry_exponent=F(2),
        left_level_factor_exponent=F(0),
        right_level_factor_exponent=F(1),
        left_product_variable_exponent=F(0),
        right_product_variable_exponent=F(1),
    )
    assert inactive.left_poisson_exponent == F(0)
    assert inactive.right_poisson_exponent == F(2)
    assert inactive.left_large_sieve_excess_exponent == F(0)
    assert inactive.continuous_some_orientation_closes
    assert inactive.poisson_conservation_or_inactive_orientation_exact

    former_mixed_orientation_witness = adapter(
        left_entry_exponent=F(1),
        right_entry_exponent=F(3, 2),
        left_level_factor_exponent=F(0),
        right_level_factor_exponent=F(3, 2),
        left_product_variable_exponent=F(3, 2),
        right_product_variable_exponent=F(3, 2),
    )
    assert former_mixed_orientation_witness.left_poisson_exponent == F(1, 2)
    assert former_mixed_orientation_witness.right_poisson_exponent == F(1)
    assert former_mixed_orientation_witness.continuous_chosen_orientation == "right"
    assert former_mixed_orientation_witness.common_spectral_orientation == "right"
    assert former_mixed_orientation_witness.single_orientation_closes_all_spectral_components

    for rho, sigma in (
        (F(3), F(3)),
        (F(3), F(2)),
        (F(2), F(3)),
        (F(1), F(1)),
    ):
        for alpha in (F(0), rho / 2, rho):
            for beta in (F(0), sigma / 2, sigma):
                for h in (F(0), F(1, 2), F(1), F(2)):
                    for ell in (F(0), F(1, 2), F(1), F(2)):
                        cell = adapter(
                            left_entry_exponent=rho,
                            right_entry_exponent=sigma,
                            left_level_factor_exponent=alpha,
                            right_level_factor_exponent=beta,
                            left_product_variable_exponent=h,
                            right_product_variable_exponent=ell,
                        )
                        assert cell.continuous_some_orientation_closes
                        assert cell.cuspidal_holomorphic_normalized_excess_closes
                        assert cell.conditional_standard_kuznetsov_factor_model_covered
                        assert cell.inverse_scaled_kloosterman_adapter_derived
                        assert cell.lifted_non_squarefree_level_family_covered
                        assert cell.all_normalized_spectral_factor_cells_covered


def test_mobius_level_weight_is_not_the_newform_kuznetsov_projector() -> None:
    adapter = getattr(
        coverage_audit,
        "newform_level_mobius_projector_audit",
        None,
    )
    assert adapter is not None, "newform level-projector audit is missing"

    prime = adapter(prime=5)
    assert prime.squarefree_level_index == F(6)
    assert prime.mobius_convolution_prime_coefficient == F(-2)
    assert prime.newform_leading_sieve_prime_coefficient == F(-1, 6)
    assert prime.local_coefficient_difference == F(-11, 6)
    assert prime.geometric_divisor_convolution_identity_exact
    assert prime.newform_formula_requires_squarefree_level
    assert prime.newform_prime_power_oldclass_tail_present
    assert prime.newform_formula_modifies_hecke_indices
    assert not prime.local_coefficients_match
    assert not prime.mobius_level_sum_is_exact_newform_projector
    assert not prime.exceptional_oldforms_annihilated_algebraically
    assert not prime.qct_newform_spectral_adapter_derived
    assert not prime.whole_mobius_gate_covered


def test_exceptional_oldclass_leading_mobius_sum_hits_zero_free_barrier() -> None:
    adapter = getattr(
        coverage_audit,
        "exceptional_oldclass_mobius_perron_audit",
        None,
    )
    assert adapter is not None, "exceptional oldclass Perron audit is missing"

    endpoint = adapter(exceptional_parameter=F(7, 64))
    assert endpoint.natural_level_sum_exponent == F(7, 32)
    assert endpoint.required_level_power_saving == F(7, 32)
    assert endpoint.required_zero_free_real_part == F(25, 32)
    assert endpoint.correction_absolute_convergence_boundary == F(-9, 32)
    assert endpoint.squarefree_level_prime_coefficient == F(-2)
    assert endpoint.newform_level_index_prime_offset == F(1)
    assert endpoint.leading_cofactor_euler_factor_exact
    assert endpoint.inverse_zeta_square_factor_exact
    assert endpoint.smooth_sum_bound_would_imply_zero_free_strip
    assert not endpoint.required_fixed_zero_free_strip_known
    assert endpoint.full_oldclass_tail_recombined
    assert not endpoint.averaged_newform_cancellation_proved
    assert not endpoint.direct_perron_route_closes_exceptional_gate
    assert not endpoint.whole_mobius_gate_covered


def test_full_oldclass_tail_preserves_inverse_zeta_square_barrier() -> None:
    adapter = getattr(
        coverage_audit,
        "exceptional_full_oldclass_tail_audit",
        None,
    )
    assert adapter is not None, "full oldclass-tail audit is missing"

    endpoint = adapter(
        prime=5,
        hecke_eigenvalue_squared=F(1),
        exceptional_parameter=F(7, 64),
        ramanujan_theta=F(7, 64),
    )
    assert endpoint.level_index == F(6)
    assert endpoint.local_rho == F(31, 36)
    assert endpoint.leading_oldclass_multiplier == F(1, 6)
    assert endpoint.full_oldclass_multiplier == F(6, 31)
    assert endpoint.tail_correction == F(5, 186)
    assert endpoint.full_mobius_prime_coefficient == F(-12, 31)
    assert endpoint.leading_prime_decay_exponent == F(-1)
    assert endpoint.tail_error_decay_exponent == F(-57, 32)
    assert endpoint.inverse_zeta_correction_boundary == F(-9, 32)
    assert endpoint.tail_correction_boundary == F(-9, 16)
    assert endpoint.full_prime_power_tail_recombined
    assert endpoint.full_multiplier_identity_exact
    assert endpoint.tail_changes_only_second_order_euler_terms
    assert endpoint.inverse_zeta_square_factor_persists
    assert endpoint.full_tail_cancels_inverse_zeta_poles is False
    assert endpoint.averaged_newform_cancellation_proved is False
    assert endpoint.direct_perron_route_closes_exceptional_gate is False
    assert endpoint.whole_mobius_gate_covered is False


def test_robles_additive_twist_bound_misses_four_mobius_gate_by_one_fifth() -> None:
    adapter = getattr(
        coverage_audit,
        "robles_four_mobius_minor_arc_audit",
        None,
    )
    assert adapter is not None, "Robles minor-arc audit is missing"

    hard = adapter(
        variable_length_exponent=F(1),
        raw_determinant_exponent=F(3),
        target_exponent=F(2),
        mobius_variables=4,
    )
    assert hard.balanced_denominator_lower_exponent == F(2, 5)
    assert hard.balanced_denominator_upper_exponent == F(3, 5)
    assert hard.one_variable_bound_exponent == F(4, 5)
    assert hard.one_variable_power_saving == F(1, 5)
    assert hard.optimistic_independent_total_saving == F(4, 5)
    assert hard.required_determinant_saving == F(1)
    assert hard.optimistic_post_bound_exponent == F(11, 5)
    assert hard.optimistic_residual_deficit == F(1, 5)
    assert hard.q_equals_one_bound_exponent == F(1)
    assert hard.centered_kernel_kills_exact_zero_mode
    assert not hard.centered_kernel_kills_major_arc_neighborhoods
    assert not hard.four_applications_are_jointly_legal
    assert not hard.major_arc_power_saving_available
    assert not hard.physical_coupled_kernel_restored
    assert not hard.robles_route_closes_gate


def test_robles_balanced_type_ii_only_recovers_geometric_determinant_count() -> None:
    adapter = getattr(
        coverage_audit,
        "robles_balanced_product_fourier_audit",
        None,
    )
    assert adapter is not None, "Robles balanced-product Fourier audit is missing"

    hard = adapter(denominator_exponent=F(1))
    assert hard.product_length_exponent == F(2)
    assert hard.left_factor_exponent == F(1)
    assert hard.right_factor_exponent == F(1)
    assert hard.fourier_ambient_exponent == F(4)
    assert hard.side_type_ii_bound_exponent == F(3, 2)
    assert hard.two_side_pointwise_bound_exponent == F(3)
    assert hard.fourier_prefactor_exponent == F(1)
    assert hard.fourier_window_exponent == F(-1)
    assert hard.normalized_fourier_bound_exponent == F(3)
    assert hard.raw_determinant_exponent == F(3)
    assert hard.target_exponent == F(2)
    assert hard.remaining_deficit == F(1)
    assert hard.denominator_is_balanced_optimum
    assert hard.type_ii_bound_recovers_geometric_window_saving
    assert not hard.type_ii_bound_supplies_post_geometric_saving
    assert not hard.absolute_product_bound_preserves_centering
    assert not hard.signed_two_side_correlation_proved
    assert not hard.robles_route_closes_gate

    lower = adapter(denominator_exponent=F(1, 2))
    upper = adapter(denominator_exponent=F(3, 2))
    assert lower.side_type_ii_bound_exponent == F(7, 4)
    assert upper.side_type_ii_bound_exponent == F(7, 4)
    assert lower.normalized_fourier_bound_exponent == F(7, 2)
    assert upper.normalized_fourier_bound_exponent == F(7, 2)
    assert lower.remaining_deficit == F(3, 2)
    assert upper.remaining_deficit == F(3, 2)


def test_inverse_zeta_variance_gate_implies_zero_free_three_quarters() -> None:
    adapter = getattr(
        coverage_audit,
        "inverse_zeta_variance_zero_free_audit",
        None,
    )
    assert adapter is not None, "inverse-zeta zero-free audit is missing"
    audit = adapter()
    assert audit.ambient_length_exponent == F(1)
    assert audit.short_window_exponent == F(1, 2)
    assert audit.variance_bound_exponent == F(3, 2)
    assert audit.dyadic_coefficient_block_exponent == F(3, 4)
    assert audit.implied_dyadic_convergence_abscissa == F(3, 4)
    assert audit.x_integration_identity_exact
    assert audit.cauchy_schwarz_exponent_exact
    assert audit.dyadic_continuation_argument_exact
    assert audit.implies_zeta_zero_free_real_part_gt_three_quarters
    assert not audit.original_mwkf_asymptotic_requires_this_gate
    assert not audit.inverse_zeta_variance_gate_available_unconditionally


def test_bblr_h_poisson_removes_inverse_and_closes_unsigned_power_box() -> None:
    helper = getattr(
        coverage_audit,
        "bblr_h_poisson_inverse_removal",
        None,
    )
    assert helper is not None, "BBLR h-Poisson helper is missing"
    exact = helper(m=7, n=19, ell=5, dual_frequency=-3)
    assert exact["inverse_residue"] == 11
    assert exact["poisson_numerator"] == -2
    assert exact["poisson_residue"] == 17
    assert exact["inverse_phase_congruence"] == 17
    assert exact["linear_congruence_left"] == 5
    assert exact["linear_congruence_right"] == 5
    assert exact["inverse_removed_exactly"]

    adapter = getattr(
        coverage_audit,
        "bblr_h_poisson_unsigned_hard_box_audit",
        None,
    )
    assert adapter is not None, "BBLR h-Poisson audit is missing"
    audit = adapter()
    assert audit.old_weil_bound_exponent == F(5, 2)
    assert audit.h_poisson_bound_exponent == F(2)
    assert audit.local_target_exponent == F(2)
    assert audit.recovered_power_saving == F(1, 2)
    assert audit.h_length_matches_reduced_modulus
    assert audit.h_poisson_identity_exact
    assert audit.inverse_fraction_becomes_linear_congruence
    assert audit.weighted_gcd_sum_is_diagonal_scale
    assert audit.positive_gcd_layers_are_power_negligible
    assert audit.approximation_error_exponent == F(2)
    assert audit.all_unsigned_hard_box_power_closed
    assert not audit.global_logarithmic_little_o_closed
    assert not audit.whole_signed_hard_face_covered


def test_bblr_h_poisson_signed_cells_reduce_to_one_quarter_boundary() -> None:
    adapter = getattr(
        coverage_audit,
        "bblr_h_poisson_signed_cell_audit",
        None,
    )
    assert adapter is not None, "signed h-Poisson cell audit is missing"

    interior = adapter(outer_scale_exponent=F(1, 8))
    assert interior.large_inner_factor_exponent == F(15, 16)
    assert interior.small_inner_factor_exponent == F(1, 16)
    assert interior.transformed_shift_exponent == F(1, 8)
    assert interior.transformed_side_product_exponent == F(9, 8)
    assert interior.transformed_raw_count_exponent == F(5, 4)
    assert interior.transformed_required_bound_exponent == F(9, 8)
    assert interior.required_outer_mobius_saving == F(1, 8)
    assert interior.h_poisson_prefactor_exponent == F(7, 8)
    assert interior.first_total_bblr_error_exponent == F(7, 4)
    assert interior.second_total_bblr_error_exponent == F(15, 8)
    assert interior.power_margin == F(1, 8)
    assert interior.dyadic_cross_terms_reduce_to_diagonal_norms
    assert interior.transformed_bblr_sharp_condition_holds
    assert interior.published_bblr_power_covers_cell

    boundary = adapter(outer_scale_exponent=F(1, 4))
    assert boundary.first_total_bblr_error_exponent == F(2)
    assert boundary.second_total_bblr_error_exponent == F(2)
    assert boundary.power_margin == F(0)
    assert not boundary.published_bblr_power_covers_cell
    assert not boundary.boundary_logarithmic_little_o_closed
    assert boundary.published_bblr_power_coverage_upper == F(1, 4)
    assert boundary.signed_residual_lower_exponent == F(1, 4)
    assert boundary.signed_residual_upper_exponent == F(1)
    assert not boundary.whole_signed_hard_face_covered


def test_signed_atom_and_h_poisson_dual_convolution_collapses_exactly() -> None:
    helper = getattr(
        coverage_audit,
        "truncated_signed_dual_convolution_identity",
        None,
    )
    assert helper is not None, "signed-dual convolution helper is missing"

    for cutoff, cofactor, product in (
        (5, 2, 3),
        (5, 2, 4),
        (5, 2, 5),
        (5, 2, 6),
        (7, 1, 6),
        (7, 3, 6),
        (11, 4, 10),
        (11, 4, 12),
    ):
        exact = helper(cutoff=cutoff, cofactor=cofactor, product=product)
        assert exact["finite_reindexing_exact"]
        assert exact["weighted_convolution"] == exact["collapsed_value"]

    audit_adapter = getattr(
        coverage_audit,
        "signed_dual_convolution_audit",
        None,
    )
    assert audit_adapter is not None, "signed-dual convolution audit is missing"
    audit = audit_adapter(outer_atom_exponent=F(1, 2))
    assert audit.outer_atom_exponent == F(1, 2)
    assert audit.h_poisson_dual_exponent == F(1, 2)
    assert audit.product_variable_exponent == F(1)
    assert audit.signed_atom_count == 2
    assert audit.signed_dual_product_collapse_exact
    assert audit.collapsed_coefficient_is_one_mobius
    assert audit.cutoff_condition_retained_exactly
    assert not audit.actual_transformed_weight_product_compatible
    assert audit.ratio_mellin_family_required
    assert not audit.weighted_collapse_bound_proved
    assert not audit.whole_signed_hard_face_covered


def test_coupled_ratio_mellin_gate_has_exact_level_half_endpoint() -> None:
    adapter = getattr(
        coverage_audit,
        "coupled_ratio_mellin_type_ii_gate_audit",
        None,
    )
    assert adapter is not None, "coupled ratio-Mellin Type-II audit is missing"

    interior = adapter(outer_scale_exponent=F(1, 2))
    assert interior.long_mobius_variable_exponent == F(1)
    assert interior.collapsed_product_variable_exponent == F(1, 2)
    assert interior.shift_exponent == F(1, 2)
    assert interior.convolution_ambient_exponent == F(3, 2)
    assert interior.progression_modulus_exponent == F(1, 2)
    assert interior.modulus_level_relative_to_ambient == F(1, 3)
    assert interior.raw_shifted_count_exponent == F(2)
    assert interior.required_inner_bound_exponent == F(3, 2)
    assert interior.required_cancellation_exponent == F(1, 2)
    assert interior.two_collapsed_coefficients_square_root_saving == F(1, 2)
    assert interior.square_root_power_margin == F(0)
    assert interior.modulus_within_bombieri_vinogradov_level

    endpoint = adapter(outer_scale_exponent=F(1))
    assert endpoint.convolution_ambient_exponent == F(2)
    assert endpoint.modulus_level_relative_to_ambient == F(1, 2)
    assert endpoint.raw_shifted_count_exponent == F(3)
    assert endpoint.required_inner_bound_exponent == F(2)
    assert endpoint.required_cancellation_exponent == F(1)
    assert endpoint.two_collapsed_coefficients_square_root_saving == F(1)
    assert endpoint.square_root_power_margin == F(0)
    assert endpoint.modulus_within_bombieri_vinogradov_level
    assert not endpoint.fixed_shift_dispersion_suffices_after_shift_sum
    assert endpoint.quotient_mobius_prevents_direct_bv
    assert endpoint.full_shift_average_must_remain_coupled
    assert endpoint.coprimality_prime_allocation_required
    assert not endpoint.four_variable_reduction_exact
    assert not endpoint.coupled_ratio_mellin_type_ii_bound_proved
    assert not endpoint.whole_signed_hard_face_covered


def test_four_cross_coprimalities_give_exact_finite_allocation() -> None:
    helper = getattr(
        coverage_audit,
        "collapsed_cross_coprimality_identity",
        None,
    )
    assert helper is not None, "collapsed coprimality helper is missing"

    for x, u, y, v in (
        (5, 7, 11, 13),
        (6, 5, 7, 11),
        (5, 6, 7, 11),
        (5, 7, 6, 11),
        (5, 7, 11, 6),
        (6, 35, 10, 21),
    ):
        exact = helper(x=x, u=u, y=y, v=v)
        assert exact["four_cross_conditions_equivalent"]
        assert exact["mobius_allocation_identity_exact"]
        assert exact["primitive_product_indicator"] == exact["allocation_value"]

    adapter = getattr(
        coverage_audit,
        "collapsed_coprimality_allocation_audit",
        None,
    )
    assert adapter is not None, "collapsed coprimality audit is missing"
    audit = adapter()
    assert audit.cross_coprimality_condition_count == 4
    assert audit.mobius_allocation_divisor_count == 4
    assert audit.product_gcd_factorization_exact
    assert audit.allocation_is_finite_reindexing
    assert audit.positive_power_loss_exponent == F(0)
    assert audit.registered_logarithmic_loss == F(4)
    assert audit.four_variable_superposition_exact
    assert audit.collapsed_coefficients_independent_of_long_variables
    assert not audit.standard_bombieri_vinogradov_adapter_applies
    assert not audit.coupled_ratio_mellin_type_ii_bound_proved
    assert not audit.whole_signed_hard_face_covered


def test_equal_collapsed_product_face_contains_fixed_shift_chowla() -> None:
    helper = getattr(
        coverage_audit,
        "collapsed_equal_product_chowla_identity",
        None,
    )
    assert helper is not None, "collapsed Chowla-face helper is missing"

    exact = helper(x=12, y=11, u=5, v=7, j=7, k=5)
    assert exact["collapsed_products_equal"]
    assert exact["fixed_shift"] == 1
    assert exact["determinant_equals_collapsed_product"]
    assert exact["primitive_product_condition_holds"]
    assert exact["primitive_condition_does_not_exclude_face"]

    adapter = getattr(
        coverage_audit,
        "collapsed_chowla_face_audit",
        None,
    )
    assert adapter is not None, "collapsed Chowla-face audit is missing"
    endpoint = adapter(outer_scale_exponent=F(1))
    assert endpoint.long_mobius_variable_exponent == F(1)
    assert endpoint.collapsed_product_variable_exponent == F(1)
    assert endpoint.equal_face_raw_exponent == F(2)
    assert endpoint.required_inner_bound_exponent == F(2)
    assert endpoint.positive_power_margin == F(0)
    assert endpoint.equal_collapsed_product_face_present
    assert endpoint.determinant_reduces_to_fixed_shift
    assert not endpoint.primitive_gcd_excludes_face
    assert endpoint.pointwise_zero_ratio_coefficient_is_mobius
    assert endpoint.face_contains_two_point_chowla
    assert not endpoint.ordinary_two_point_chowla_available_unconditionally
    assert endpoint.logarithmic_little_o_required
    assert not endpoint.uniform_ratio_frequency_triangle_gate_admissible
    assert endpoint.joint_ratio_integral_must_remain_coupled
    assert not endpoint.coupled_ratio_mellin_type_ii_bound_proved
    assert not endpoint.whole_signed_hard_face_covered


def test_physical_primitive_equal_face_coefficient_survives_recombination() -> None:
    helper = getattr(
        coverage_audit,
        "primitive_equal_face_divisor_coefficient",
        None,
    )
    assert helper is not None, "physical equal-face coefficient helper is missing"
    exact = helper(
        cutoff=5,
        left_cofactor=10,
        right_cofactor=10,
        collapsed_product=35,
        x=12,
        y=11,
        allowed_left_factors=(5, 7),
        allowed_right_factors=(5, 7),
    )
    assert exact["fixed_shift"] == 1
    assert exact["primitive_terms_only"]
    assert exact["coefficient"] == 4
    assert exact["nonzero_primitive_equal_face_coefficient"]
    assert set(exact["contributing_factor_pairs"]) == {(5, 7), (7, 5)}

    adapter = getattr(
        coverage_audit,
        "physical_joint_ratio_recombination_audit",
        None,
    )
    assert adapter is not None, "physical ratio-recombination audit is missing"
    audit = adapter()
    assert audit.ratio_mellin_recombines_to_finite_divisor_kernel
    assert audit.primitive_equal_face_coefficient_can_be_nonzero
    assert audit.witness_equal_face_coefficient == 4
    assert not audit.joint_ratio_integration_alone_annihilates_chowla_face
    assert not audit.arbitrary_smooth_weight_enlargement_admissible
    assert not audit.allocationwise_triangle_inequality_admissible
    assert not audit.equal_face_separate_bound_available_unconditionally
    assert audit.full_outer_scale_and_kernel_sum_must_remain_coupled
    assert not audit.centered_coupled_dispersion_bound_proved
    assert not audit.whole_signed_hard_face_covered


def test_collapsed_gcd_layer_centered_kernel_has_exact_scale() -> None:
    helper = getattr(
        coverage_audit,
        "collapsed_gcd_layer_parameterization",
        None,
    )
    assert helper is not None, "collapsed gcd-layer helper is missing"
    exact = helper(c=70, d=105, shift=35, x=8, y=5)
    assert exact["common_gcd"] == 35
    assert exact["primitive_left"] == 2
    assert exact["primitive_right"] == 3
    assert exact["primitive_shift"] == 1
    assert exact["primitive_coprime"]
    assert exact["original_determinant"] == 35
    assert exact["primitive_determinant"] == 1
    assert exact["equation_equivalent"]

    adapter = getattr(
        coverage_audit,
        "collapsed_gcd_layer_centered_kernel_audit",
        None,
    )
    assert adapter is not None, "collapsed gcd-layer audit is missing"
    audit = adapter(
        collapsed_exponent=F(1),
        gcd_exponent=F(3, 5),
    )
    assert audit.cofactor_exponent == F(2, 5)
    assert audit.product_length_exponent == F(7, 5)
    assert audit.primitive_shift_exponent == F(2, 5)
    assert audit.raw_dyadic_layer_exponent == F(12, 5)
    assert audit.global_target_exponent == F(2)
    assert audit.required_saving_exponent == F(2, 5)
    assert audit.fourier_inner_target_exponent == F(8, 5)
    assert audit.shift_weight_vanishes_near_zero
    assert audit.product_diagonal_annihilated_exactly
    assert audit.constant_fourier_mode_centered_exactly
    assert audit.full_g_sum_retained
    assert audit.full_allocation_and_ratio_sum_retained
    assert not audit.pointwise_fixed_affine_chowla_bound_assumed
    assert not audit.published_averaged_chowla_adapter_applies
    assert not audit.centered_coupled_dispersion_bound_proved
    assert not audit.whole_signed_hard_face_covered

    endpoint = adapter(
        collapsed_exponent=F(1),
        gcd_exponent=F(1),
    )
    assert endpoint.cofactor_exponent == 0
    assert endpoint.required_saving_exponent == 0
    assert endpoint.top_equal_product_face
    assert endpoint.fixed_affine_chowla_must_remain_inside_g_sum


def test_primitive_equal_product_face_has_outer_pnt_cancellation() -> None:
    factor = getattr(
        coverage_audit,
        "primitive_equal_product_factorization",
        None,
    )
    assert factor is not None, "primitive equal-product helper is missing"
    exact = factor(u=5, v=7, j=14, k=10)
    assert exact["primitive_coprime"]
    assert exact["equal_product"]
    assert exact["quotient"] == 2
    assert exact["j_equals_vq"]
    assert exact["k_equals_uq"]
    assert exact["collapsed_product"] == 70
    assert exact["factorization_exact"]

    interval = getattr(
        coverage_audit,
        "truncated_signed_atom_interval_convolution",
        None,
    )
    assert interval is not None, "signed-atom interval helper is missing"
    atom = interval(cutoff=5, cofactor=10, atom=35)
    assert atom["direct_coefficient"] == -2
    assert atom["direct_coefficient"] == atom["interval_convolution"]
    assert atom["interval_convolution_exact"]
    assert atom["lower_strict_numerator"] == 5
    assert atom["lower_strict_denominator"] == 10

    adapter = getattr(
        coverage_audit,
        "top_equal_product_outer_pnt_audit",
        None,
    )
    assert adapter is not None, "top equal-product PNT audit is missing"
    audit = adapter()
    assert audit.signed_atom_exponent == F(1, 2)
    assert audit.poisson_quotient_exponent == 0
    assert audit.outer_pair_raw_exponent == 1
    assert audit.long_correlation_trivial_exponent == 1
    assert audit.face_raw_exponent == 2
    assert audit.face_target_exponent == 2
    assert audit.power_margin == 0
    assert audit.primitive_equal_product_factorization_exact
    assert audit.signed_atom_interval_convolution_exact
    assert audit.balanced_cutoff_ratios_verified
    assert audit.uniform_coprime_pnt_log_saving_available
    assert audit.coprime_euler_factor_loss_only_polylogarithmic
    assert audit.long_mobius_correlation_used_only_trivially
    assert not audit.fixed_affine_chowla_estimate_required
    assert audit.top_equal_product_face_closed_unconditionally
    assert not audit.whole_signed_hard_face_covered


def test_primitive_unequal_product_refactorization_closes_polylog_collar() -> None:
    helper = getattr(
        coverage_audit,
        "primitive_unequal_product_factorization",
        None,
    )
    assert helper is not None, "primitive unequal-product helper is missing"
    exact = helper(a=6, b=35, u=10, v=21, j=9, k=25)
    assert exact["primitive_slopes"]
    assert exact["primitive_hidden_factors"]
    assert exact["left_cross_gcd"] == 2
    assert exact["right_cross_gcd"] == 7
    assert exact["cross_gcd_product"] == 14
    assert exact["cross_gcd_identity"]
    assert exact["quotient"] == 1
    assert exact["j_formula"] == 9
    assert exact["k_formula"] == 25
    assert exact["common_collapsed_gcd"] == 15
    assert exact["left_collapsed_product"] == 90
    assert exact["right_collapsed_product"] == 525
    assert exact["factorization_exact"]

    adapter = getattr(
        coverage_audit,
        "polylog_gcd_collar_outer_pnt_audit",
        None,
    )
    assert adapter is not None, "polylog gcd-collar PNT audit is missing"
    audit = adapter(polylog_depth=5)
    assert audit.polylog_depth == 5
    assert audit.cofactor_power_exponent == 0
    assert audit.cross_gcd_power_exponent == 0
    assert audit.poisson_quotient_power_exponent == 0
    assert audit.required_power_saving_exponent == 0
    assert audit.primitive_unequal_product_factorization_exact
    assert audit.cross_gcd_product_identity_exact
    assert audit.prescribed_divisibility_coprime_pnt_available
    assert audit.arbitrary_log_saving_absorbs_polylog_variables
    assert audit.long_affine_mobius_sum_used_only_trivially
    assert audit.polylog_gcd_collar_closed_unconditionally
    assert not audit.strict_positive_power_gcd_layers_covered
    assert not audit.whole_signed_hard_face_covered


def test_strict_power_gcd_core_has_one_exact_deficit_block() -> None:
    adapter = getattr(
        coverage_audit,
        "strict_power_gcd_core_audit",
        None,
    )
    assert adapter is not None, "strict-power gcd-core audit is missing"
    audit = adapter(
        collapsed_exponent=F(1),
        cofactor_exponent=F(2, 5),
        quotient_exponent=F(1, 5),
        left_cross_gcd_exponent=F(1, 4),
    )
    assert audit.gcd_exponent == F(3, 5)
    assert audit.right_cross_gcd_exponent == F(7, 20)
    assert audit.left_reduced_slope_exponent == F(3, 20)
    assert audit.right_reduced_slope_exponent == F(1, 20)
    assert audit.left_reduced_signed_exponent == F(1, 4)
    assert audit.right_reduced_signed_exponent == F(3, 20)
    assert audit.unsigned_reduced_block_exponent == F(2, 5)
    assert audit.signed_reduced_block_exponent == F(2, 5)
    assert audit.reconstructed_gcd_exponent == F(3, 5)
    assert audit.raw_core_exponent == F(12, 5)
    assert audit.target_core_exponent == F(2)
    assert audit.required_saving_exponent == F(2, 5)
    assert audit.exponent_polytope_feasible
    assert audit.unsigned_block_equals_full_deficit
    assert audit.all_allocations_and_ratio_integrals_retained
    assert audit.long_and_collapsed_arithmetic_weights_on_each_side
    assert audit.bblr_arbitrary_outer_coefficient_adapter_applies
    assert audit.centered_three_block_type_ii_required
    assert not audit.centered_three_block_type_ii_proved
    assert not audit.whole_signed_hard_face_covered


def test_strict_power_convolution_poisson_and_cauchy_ledgers_are_exact() -> None:
    adapter = getattr(
        coverage_audit,
        "strict_power_convolution_kloosterman_audit",
        None,
    )
    assert adapter is not None, "strict-power convolution audit is missing"
    audit = adapter(
        collapsed_exponent=F(1),
        cofactor_exponent=F(2, 5),
        quotient_exponent=F(1, 5),
        left_cross_gcd_exponent=F(1, 4),
    )
    assert audit.right_cross_gcd_exponent == F(7, 20)
    assert audit.left_convolved_outer_exponent == F(5, 4)
    assert audit.right_convolved_outer_exponent == F(27, 20)
    assert audit.left_inner_slope_exponent == F(3, 20)
    assert audit.right_inner_slope_exponent == F(1, 20)
    assert audit.side_product_exponent == F(7, 5)
    assert audit.remaining_outer_exponent == F(3, 5)
    assert audit.bblr_convolution_hypotheses_verified
    assert audit.bblr_ab_error_exponent == F(7, 2)
    assert audit.bblr_watt_error_exponent == F(81, 40)
    assert audit.bblr_inner_target_exponent == F(7, 5)
    assert audit.bblr_ab_deficit == F(21, 10)
    assert audit.bblr_watt_deficit == F(5, 8)
    assert not audit.bblr_convolution_route_covered
    assert audit.poisson_dual_exponent == F(6, 5)
    assert audit.poisson_numerator_exponent == F(8, 5)
    assert audit.poisson_normalization_exponent == F(-6, 5)
    assert audit.bc_first_total_exponent == F(1323, 400)
    assert audit.bc_second_total_exponent == F(551, 160)
    assert audit.bc_first_deficit == F(523, 400)
    assert audit.bc_second_deficit == F(231, 160)
    assert not audit.bc_poisson_route_covered
    assert audit.original_cross_diagonal_removed_by_centering
    assert audit.cauchy_tuple_diagonal_exponent == F(11, 5)
    assert audit.cauchy_grouped_diagonal_exponent == F(12, 5)
    assert audit.cauchy_diagonal_target_exponent == F(2)
    assert audit.cauchy_grouped_diagonal_deficit == F(2, 5)
    assert audit.cauchy_grouped_diagonal_is_raw_scale
    assert not audit.cauchy_grouped_diagonal_killed_by_centering
    assert not audit.near_frequency_type_ii_proved

    boundary = adapter(
        collapsed_exponent=F(1),
        cofactor_exponent=F(1),
        quotient_exponent=F(0),
        left_cross_gcd_exponent=F(1, 2),
    )
    assert boundary.gcd_exponent == 0
    assert boundary.cauchy_tuple_diagonal_exponent == F(3)
    assert boundary.cauchy_grouped_diagonal_exponent == F(3)
    assert boundary.cauchy_diagonal_target_exponent == F(2)
    assert boundary.cauchy_grouped_diagonal_deficit == F(1)
    assert boundary.cauchy_grouped_diagonal_is_raw_scale
    assert not boundary.cauchy_grouped_diagonal_killed_by_centering
    assert boundary.hard_vertex_inverse_zeta_square_variance


def test_strict_power_ratio_mellin_bandwidth_has_no_power_resolution() -> None:
    adapter = getattr(
        coverage_audit,
        "strict_power_ratio_mellin_bandwidth_audit",
        None,
    )
    assert adapter is not None, "strict-power ratio-Mellin audit is missing"
    audit = adapter(
        collapsed_exponent=F(1),
        cofactor_exponent=F(2, 5),
        quotient_exponent=F(1, 5),
        left_cross_gcd_exponent=F(1, 4),
    )
    assert audit.left_hidden_fibre_exponent == F(1, 4)
    assert audit.right_hidden_fibre_exponent == F(3, 20)
    assert audit.total_hidden_fibre_exponent == F(2, 5)
    assert audit.height_phase_log_derivative_power_exponent == 0
    assert audit.ratio_weight_log_derivative_power_exponent == 0
    assert audit.effective_mellin_frequency_power_exponent == 0
    assert audit.left_adjacent_resolution_frequency_exponent == F(1, 4)
    assert audit.right_adjacent_resolution_frequency_exponent == F(3, 20)
    assert audit.mellin_power_tail_is_rapid
    assert audit.scaled_T_tau_not_independent_bandwidth
    assert not audit.height_phase_creates_second_power_coordinate
    assert not audit.ratio_mellin_resolves_positive_hidden_fibres
    assert not audit.ratio_mellin_supplies_required_delta_saving
    assert audit.pre_cauchy_joint_kernel_still_required

    hard_vertex = adapter(
        collapsed_exponent=F(1),
        cofactor_exponent=F(1),
        quotient_exponent=F(0),
        left_cross_gcd_exponent=F(1, 2),
    )
    assert hard_vertex.total_hidden_fibre_exponent == 0
    assert hard_vertex.effective_mellin_frequency_power_exponent == 0
    assert hard_vertex.ratio_mellin_resolves_positive_hidden_fibres
    assert not hard_vertex.ratio_mellin_supplies_required_delta_saving
    assert hard_vertex.remaining_cauchy_deficit_exponent == F(1)


def test_strict_power_double_poisson_resonance_ledger_is_exact() -> None:
    adapter = getattr(
        coverage_audit,
        "strict_power_double_poisson_resonance_audit",
        None,
    )
    assert adapter is not None, "strict-power double-Poisson audit is missing"
    audit = adapter(
        collapsed_exponent=F(1),
        cofactor_exponent=F(2, 5),
        quotient_exponent=F(1, 5),
        left_cross_gcd_exponent=F(1, 4),
    )
    assert audit.left_slope_exponent == F(3, 20)
    assert audit.right_slope_exponent == F(1, 20)
    assert audit.left_modulus_exponent == F(5, 4)
    assert audit.right_modulus_exponent == F(27, 20)
    assert audit.left_dual_exponent == F(17, 20)
    assert audit.right_dual_exponent == F(19, 20)
    assert audit.dual_side_product_exponent == F(11, 5)
    assert audit.resonance_shift_exponent == F(6, 5)
    assert audit.poisson_amplitude_exponent == F(1, 5)
    assert audit.overlap_integral_exponent == F(-1)
    assert audit.transformed_absolute_inner_exponent == F(13, 5)
    assert audit.original_inner_raw_exponent == F(9, 5)
    assert audit.absolute_transform_loss_exponent == F(4, 5)
    assert audit.transformed_global_absolute_exponent == F(16, 5)
    assert audit.global_target_exponent == F(2)
    assert audit.transformed_required_saving_exponent == F(6, 5)
    assert audit.resonance_identity_exact
    assert audit.two_poisson_scales_exact
    assert audit.absolute_transform_loss_is_one_minus_delta_plus_theta
    assert not audit.absolute_double_poisson_route_covered
    assert audit.pre_cauchy_signed_resonance_estimate_required
    assert audit.bblr_sharp_range_verified
    assert audit.bblr_ab_before_normalization_exponent == F(43, 10)
    assert audit.bblr_watt_before_normalization_exponent == F(129, 40)
    assert audit.transform_normalization_exponent == F(-4, 5)
    assert audit.bblr_ab_total_exponent == F(41, 10)
    assert audit.bblr_watt_total_exponent == F(121, 40)
    assert audit.bblr_ab_deficit == F(21, 10)
    assert audit.bblr_watt_deficit == F(41, 40)
    assert audit.original_bblr_ab_deficit == F(21, 10)
    assert audit.original_bblr_watt_deficit == F(5, 8)
    assert audit.bblr_ab_deficit_is_invariant
    assert audit.bblr_watt_extra_deficit == F(2, 5)
    assert audit.bblr_watt_extra_deficit_is_nonnegative
    assert not audit.double_poisson_improves_bblr

    hard_vertex = adapter(
        collapsed_exponent=F(1),
        cofactor_exponent=F(1),
        quotient_exponent=F(0),
        left_cross_gcd_exponent=F(1, 2),
    )
    assert hard_vertex.left_dual_exponent == F(1, 2)
    assert hard_vertex.right_dual_exponent == F(1, 2)
    assert hard_vertex.absolute_transform_loss_exponent == 0
    assert hard_vertex.transformed_required_saving_exponent == F(1)
    assert not hard_vertex.absolute_double_poisson_route_covered
    assert hard_vertex.bblr_ab_deficit == F(5, 2)
    assert hard_vertex.bblr_watt_deficit == F(1)
    assert hard_vertex.bblr_ab_deficit_is_invariant
    assert hard_vertex.bblr_watt_extra_deficit == 0
    assert not hard_vertex.double_poisson_improves_bblr


def test_transition_line_fourier_identity_and_microarc_gate_are_exact() -> None:
    helper = getattr(
        coverage_audit,
        "transition_line_finite_fourier_identity",
        None,
    )
    assert helper is not None, "line Fourier identity helper is missing"
    exact = helper(a=5, b=7, r1=13, r2=18, h=1, modulus=101)
    assert exact["line_defect"] == 0
    assert exact["congruence_indicator"] == 1
    assert exact["integer_equality_indicator"] == 1
    assert exact["finite_fourier_detects_integer_equality"]

    off = helper(a=5, b=7, r1=13, r2=18, h=2, modulus=101)
    assert off["line_defect"] == -1
    assert off["congruence_indicator"] == 0
    assert off["integer_equality_indicator"] == 0
    assert off["finite_fourier_detects_integer_equality"]

    adapter = getattr(
        coverage_audit,
        "transition_line_fourier_microarc_audit",
        None,
    )
    assert adapter is not None, "line Fourier microarc audit is missing"
    balanced = adapter(denominator_gcd_exponent=F(1, 2))
    assert balanced.denominator_cofactor_exponent == F(1, 2)
    assert balanced.h_window_exponent == F(1, 2)
    assert balanced.product_phase_scale_exponent == F(3, 2)
    assert balanced.full_frequency_window_exponent == F(-1, 2)
    assert balanced.constant_phase_microarc_exponent == F(-3, 2)
    assert balanced.microarcs_in_full_window_exponent == F(1)
    assert balanced.fixed_g_raw_line_exponent == F(2)
    assert balanced.fixed_g_target_exponent == F(3, 2)
    assert balanced.required_fixed_g_saving_exponent == F(1, 2)
    assert balanced.separated_mertens_product_trivial_exponent == F(3, 2)
    assert balanced.separated_mertens_product_target_exponent == F(5, 4)
    assert balanced.required_mertens_product_saving_exponent == F(1, 4)
    assert balanced.finite_fourier_orthogonality_exact
    assert balanced.h_window_poisson_localization_exact
    assert not balanced.actual_coupled_weight_tensor_separated
    assert not balanced.nonzero_constant_tensor_mode_verified
    assert not balanced.microarc_mertens_reduction_is_actual_gate
    assert not balanced.whole_line_family_covered

    general = adapter(denominator_gcd_exponent=F(1, 4))
    assert general.denominator_cofactor_exponent == F(3, 4)
    assert general.product_phase_scale_exponent == F(7, 4)
    assert general.constant_phase_microarc_exponent == F(-7, 4)
    assert general.fixed_g_raw_line_exponent == F(5, 2)
    assert general.fixed_g_target_exponent == F(7, 4)
    assert general.required_fixed_g_saving_exponent == F(3, 4)
    assert general.required_mertens_product_saving_exponent == F(3, 8)


def test_transition_balanced_mobius_convolution_gate_is_exact() -> None:
    helper = getattr(
        coverage_audit,
        "transition_balanced_convolution_identity",
        None,
    )
    assert helper is not None, "balanced convolution identity is missing"
    exact = helper(
        factor_pairs=((2, 5, -1), (3, 4, 1), (4, 3, -2), (5, 2, 3)),
        shift_length=5,
    )
    assert exact["coefficient_expansion"] == exact["factor_expansion"]
    assert (
        exact["short_interval_overlap_integral"]
        == exact["coefficient_expansion"]
    )
    assert exact["autocorrelation_reindex_exact"]
    assert exact["fejer_short_interval_identity_exact"]

    adapter = getattr(
        coverage_audit,
        "transition_balanced_mobius_convolution_audit",
        None,
    )
    assert adapter is not None, "balanced convolution adapter is missing"
    balanced = adapter(denominator_gcd_exponent=F(1, 2))
    assert balanced.cofactor_length_exponent == F(1, 2)
    assert balanced.product_center_exponent == F(3, 2)
    assert balanced.product_difference_exponent == F(1, 2)
    assert balanced.raw_autocorrelation_exponent == F(2)
    assert balanced.diagonal_scale_target_exponent == F(3, 2)
    assert balanced.required_variance_saving_exponent == F(1, 2)
    assert balanced.optimistic_mangerel_bound_exponent == F(2)
    assert balanced.optimistic_mangerel_power_deficit == F(1, 2)
    assert balanced.endpoint_taper_count_in_square == 4
    assert balanced.product_energy_log_loss == 1
    assert balanced.net_endpoint_log_saving == 3
    assert balanced.finite_autocorrelation_identity_exact
    assert balanced.fejer_short_interval_identity_exact
    assert not balanced.balanced_coefficient_is_multiplicative
    assert balanced.exact_mellin_twisted_convolution_available
    assert balanced.actual_coprimality_layers_aggregated
    assert balanced.actual_coupled_kernel_nuclear_norm_verified
    assert not balanced.published_square_root_variance_proved
    assert not balanced.whole_line_family_covered

    top = adapter(denominator_gcd_exponent=F(0))
    assert top.cofactor_length_exponent == F(1)
    assert top.product_center_exponent == F(2)
    assert top.raw_autocorrelation_exponent == F(3)
    assert top.diagonal_scale_target_exponent == F(2)
    assert top.required_variance_saving_exponent == F(1)
    assert top.optimistic_mangerel_power_deficit == F(1)


def test_transition_coprimality_layers_reduce_to_weighted_variance() -> None:
    identity = getattr(
        coverage_audit,
        "transition_line_coprimality_layer_identity",
        None,
    )
    assert identity is not None, "coprimality layer identity is missing"
    coprime = identity(a=5, b=7, r1=11, r2=13, g=2, q=3)
    assert coprime["original_indicator"] == 1
    assert coprime["expanded_indicator"] == 1
    assert coprime["three_indicator_expansion_exact"]

    noncoprime = identity(a=5, b=10, r1=15, r2=14, g=3, q=7)
    assert noncoprime["original_indicator"] == 0
    assert noncoprime["expanded_indicator"] == 0
    assert noncoprime["three_indicator_expansion_exact"]

    q_blocked = identity(a=5, b=7, r1=11, r2=13, g=2, q=11)
    assert q_blocked["q_one_variable_factor"] == 0
    assert q_blocked["original_indicator"] == 0
    assert q_blocked["expanded_indicator"] == 0

    density = getattr(
        coverage_audit,
        "transition_line_coprimality_layer_density",
        None,
    )
    assert density is not None, "coprimality layer density is missing"
    layer = density(d0=6, d1=10, d2=21, g=35)
    assert layer["e1"] == 5
    assert layer["e2"] == 7
    assert layer["f1"] == 2
    assert layer["f2"] == 3
    assert layer["a_modulus"] == 6
    assert layer["b_modulus"] == 6
    assert layer["r1_modulus"] == 10
    assert layer["r2_modulus"] == 21
    assert layer["density_denominator"] == 7560
    assert layer["density"] == F(1, 7560)
    assert layer["factorization_exact"]

    adapter = getattr(
        coverage_audit,
        "transition_coprimality_layer_audit",
        None,
    )
    assert adapter is not None, "coprimality layer adapter is missing"
    audit = adapter(denominator_gcd_exponent=F(1, 2))
    assert audit.cofactor_length_exponent == F(1, 2)
    assert audit.exact_three_indicator_expansion
    assert audit.non_g_prime_p2_coefficient == 3
    assert audit.non_g_prime_p3_coefficient == 2
    assert audit.non_g_prime_p4_coefficient == 2
    assert audit.non_g_absolute_euler_product_converges
    assert audit.g_prime_loss_is_subpolylogarithmic
    assert audit.lifted_kernel_dimension == 5
    assert audit.fourier_derivative_order == 10
    assert audit.determinant_cutoff_derivative_power_cost == F(0)
    assert audit.lifted_kernel_fourier_nuclear_norm_verified
    assert audit.layer_density_aggregation_verified
    assert audit.required_layer_variance_saving_exponent == F(1, 2)
    assert not audit.published_layer_variance_proved
    assert audit.actual_line_family_reduced_to_layered_variance
    assert not audit.whole_line_family_covered


def test_transition_variance_is_a_mixed_mobius_fourth_moment_gate() -> None:
    """Catch a lost X/T normalization or a false published-coverage claim."""
    identity = getattr(
        coverage_audit,
        "transition_mobius_dirichlet_product_identity",
        None,
    )
    assert identity is not None, "Dirichlet product identity is missing"
    exact = identity(
        left_terms=((2, -1), (3, 2)),
        right_terms=((5, 3), (7, -2)),
        integer_power=2,
    )
    assert exact["left_dirichlet_sum"] == F(-1, 36)
    assert exact["right_dirichlet_sum"] == F(97, 1225)
    assert exact["product_dirichlet_sum"] == F(-97, 44100)
    assert exact["convolution_dirichlet_sum"] == F(-97, 44100)
    assert exact["dirichlet_product_identity_exact"]

    adapter = getattr(
        coverage_audit,
        "transition_mobius_dirichlet_fourth_moment_audit",
        None,
    )
    assert adapter is not None, "mixed fourth-moment adapter is missing"
    middle = adapter(denominator_gcd_exponent=F(1, 2))
    assert middle.cofactor_length_exponent == F(1, 2)
    assert middle.long_mobius_polynomial_exponent == F(1)
    assert middle.product_polynomial_exponent == F(3, 2)
    assert middle.physical_height_exponent == F(1)
    assert middle.dcv_coefficient_target_exponent == F(3, 2)
    assert middle.moment_target_exponent == F(1)
    assert middle.generic_mean_value_exponent == F(3, 2)
    assert middle.generic_mean_value_power_deficit == F(1, 2)
    assert middle.coefficient_to_moment_normalization_exponent == F(-1, 2)
    assert middle.exact_dirichlet_product_identity
    assert middle.exact_scaled_log_coordinate_kernel_inversion
    assert middle.transform_is_schwartz_localized_at_height_T
    assert not middle.separated_transform_compactly_excludes_zero_frequency
    assert middle.coprimality_layers_already_aggregated
    assert middle.dcv_exact_mixed_fourth_moment_superposition
    assert middle.uniform_mixed_fourth_moment_sufficient_for_dcv
    assert not middle.dcv_implies_each_separated_moment
    assert not middle.published_mixed_fourth_moment_proved
    assert not middle.whole_line_family_covered

    top = adapter(denominator_gcd_exponent=F(0))
    assert top.cofactor_length_exponent == F(1)
    assert top.product_polynomial_exponent == F(2)
    assert top.moment_target_exponent == F(1)
    assert top.generic_mean_value_exponent == F(2)
    assert top.generic_mean_value_power_deficit == F(1)
    assert top.coefficient_to_moment_normalization_exponent == F(-1)
    assert top.symmetric_top_face_is_mobius_fourth_moment


def test_generic_large_values_do_not_prove_the_mobius_fourth_moment() -> None:
    """Catch any adapter that spends a logarithmic theorem as a power saving."""
    adapter = getattr(
        coverage_audit,
        "transition_mobius_large_value_audit",
        None,
    )
    assert adapter is not None, "Möbius large-value adapter is missing"

    boundary = adapter(amplitude_exponent=F(1, 2))
    assert boundary.unnormalized_fourth_moment_target_exponent == F(3)
    assert boundary.required_large_value_count_exponent == F(1)
    assert boundary.classical_large_value_count_exponent == F(1)
    assert boundary.classical_fourth_contribution_exponent == F(3)
    assert boundary.best_published_fourth_contribution_exponent == F(3)
    assert boundary.best_published_power_deficit == F(0)
    assert boundary.power_boundary_covered

    medium = adapter(amplitude_exponent=F(2, 3))
    assert medium.required_large_value_count_exponent == F(1, 3)
    assert medium.classical_large_value_count_exponent == F(2, 3)
    assert medium.classical_fourth_contribution_exponent == F(10, 3)
    assert medium.guth_maynard_term1_contribution_exponent == F(10, 3)
    assert medium.guth_maynard_term2_contribution_exponent == F(18, 5)
    assert medium.guth_maynard_term3_contribution_exponent == F(17, 5)
    assert medium.guth_maynard_fourth_contribution_exponent == F(18, 5)
    assert medium.best_published_fourth_contribution_exponent == F(10, 3)
    assert medium.best_published_power_deficit == F(1, 3)
    assert medium.menon_positive_power_saving_exponent == F(0)
    assert not medium.mobius_large_value_theorem_proved
    assert not medium.power_boundary_covered

    high = adapter(amplitude_exponent=F(4, 5))
    assert high.required_large_value_count_exponent == F(-1, 5)
    assert high.required_count_exponent_is_negative
    assert high.componentwise_fourth_moment_pointwise_threshold == F(3, 4)
    assert high.best_published_power_deficit == F(3, 5)
    assert not high.original_signed_dcv_requires_componentwise_large_values
    assert not high.whole_line_family_covered


def test_long_cutoff_quotient_split_hits_the_exact_bv_boundary() -> None:
    """The small divisor sector reaches, but must not cross, level 1/2."""
    adapter = getattr(
        coverage_audit,
        "long_cutoff_quotient_split_audit",
        None,
    )
    assert adapter is not None, "long-cutoff quotient split audit is missing"

    hard = boundary_witnesses()["balanced_max_a"]
    endpoint = adapter(
        hard,
        cutoff_exponent=F(401, 200),
        b_exponent=F(199, 200),
        dual_v_exponent=F(1, 2),
    )
    assert endpoint.a_exponent == F(401, 200)
    assert endpoint.small_divisor_level_exponent == F(1, 200)
    assert endpoint.expanded_modulus_endpoint == F(3, 2)
    assert endpoint.large_cofactor_max_exponent == F(2)
    assert endpoint.strict_bv_log_slack_required
    assert endpoint.gcd_reduction_only_decreases_modulus
    assert endpoint.large_sector_retains_two_mobius_weights
    assert not endpoint.standard_bv_coupled_hypotheses_verified
    assert not endpoint.published_coverage

    other_end = adapter(
        hard,
        cutoff_exponent=F(401, 200),
        b_exponent=F(0),
        dual_v_exponent=F(1, 2),
    )
    assert other_end.small_divisor_level_exponent == F(1)
    assert other_end.expanded_modulus_endpoint == F(3, 2)
    assert other_end.large_cofactor_max_exponent == F(2)


def test_ideal_bdh_still_misses_the_quotient_gate_at_square_root_level() -> None:
    """Even an optimistic common-weight BDH model leaves a power gap."""
    adapter = getattr(
        coverage_audit,
        "long_cutoff_quotient_bdh_audit",
        None,
    )
    assert adapter is not None, "long-cutoff quotient BDH audit is missing"

    hard = boundary_witnesses()["balanced_max_a"]
    endpoint = adapter(
        hard,
        b_exponent=F(199, 200),
        d_exponent=F(1, 200),
        dual_v_exponent=F(1, 2),
        dual_j_exponent=F(1, 2),
    )
    assert endpoint.modulus_exponent == F(3, 2)
    assert endpoint.query_family_exponent == F(9, 2)
    assert endpoint.progression_length_exponent == F(3, 2)
    assert endpoint.total_cardinality_exponent == F(6)
    assert endpoint.residue_multiplicity_exponent == F(3, 2)
    assert endpoint.outer_coefficient_l2_squared_exponent == F(6)
    assert endpoint.ideal_bdh_variance_exponent == F(9, 2)
    assert endpoint.optimistic_bdh_bound_exponent == F(21, 4)
    assert endpoint.farey_gate_target_exponent == F(3499, 1000)
    assert endpoint.bdh_remaining_deficit == F(1751, 1000)
    assert endpoint.completion_conversion_exponent == F(1, 2)
    assert endpoint.max_centered_product_phase_saving == F(1)
    assert endpoint.optimistic_centered_bound_exponent == F(19, 4)
    assert endpoint.completed_gate_target_exponent == F(3999, 1000)
    assert endpoint.centered_remaining_deficit == F(751, 1000)
    assert not endpoint.common_weight_hypothesis_verified
    assert not endpoint.centered_geometric_saving_proved
    assert not endpoint.published_coverage

    zero_modulus = adapter(
        hard,
        b_exponent=F(0),
        d_exponent=F(0),
        dual_v_exponent=F(0),
        dual_j_exponent=F(1, 2),
    )
    assert zero_modulus.optimistic_bdh_bound_exponent == F(9, 2)
    assert zero_modulus.centered_remaining_deficit == F(501, 1000)


def test_pascadi_incomplete_kloosterman_regular_term_is_too_large() -> None:
    adapter = getattr(
        coverage_audit,
        "pascadi_incomplete_kloosterman_audit",
        None,
    )
    assert adapter is not None, "Pascadi Corollary 18 audit is missing"

    result = adapter(boundary_witnesses()["balanced_max_a"])
    assert result.product_n_exponent == F(5)
    assert result.incomplete_d_exponent == F(3)
    assert result.modulus_c_exponent == F(3)
    assert result.coefficient_l2_exponent == F(5, 2)
    assert result.regular_i_squared_exponent == F(11)
    assert result.exceptional_i_squared_exponent == F(11)
    assert result.i_exponent == F(11, 2)
    assert result.optimistic_bound_exponent == F(8)
    assert result.gate_target_exponent == F(3499, 1000)
    assert result.remaining_deficit == F(4501, 1000)
    assert result.product_coefficient_separated_optimistically
    assert not result.assumption_14_verified
    assert not result.direct_corollary_hypotheses_verified
    assert not result.published_coverage


def test_centered_e_poisson_recloses_the_original_determinant_gate() -> None:
    adapter = getattr(
        coverage_audit,
        "centered_quotient_poisson_audit",
        None,
    )
    assert adapter is not None, "centered quotient Poisson audit is missing"

    result = adapter(boundary_witnesses()["balanced_max_a"])
    assert result.e_cofactor_max_exponent == F(2)
    assert result.squarefree_e_support_required
    assert result.coprimality_e_support_required
    assert result.squarefree_divisor_expansion_exact
    assert result.nonzero_frequency_mass_equals_theta_00
    assert not result.centered_minus_one_vanishes_separately
    assert not result.unweighted_e_poisson_valid
    assert result.joint_c_v_orthogonality_recloses_original_kernel
    assert result.determinant_gate_unchanged
    assert not result.new_conductor_reduction
    assert not result.published_coverage


def test_hecke_mobius_euler_factor_is_exact_but_not_a_qct_adapter() -> None:
    local_factor = getattr(
        coverage_audit,
        "hecke_mobius_local_factor",
        None,
    )
    adapter = getattr(
        coverage_audit,
        "hecke_mobius_spectral_audit",
        None,
    )
    assert local_factor is not None, "Hecke--Mobius local factor is missing"
    assert adapter is not None, "Hecke--Mobius spectral audit is missing"

    factor = local_factor(F(3, 2), F(1))
    assert factor.mobius_factor == (F(1), F(-3, 2))
    assert factor.inverse_l_factor == (F(1), F(-3, 2), F(1))
    assert factor.correction_numerator == factor.mobius_factor
    assert factor.correction_denominator == factor.inverse_l_factor
    assert factor.correction_minus_one_numerator == (F(0), F(0), F(-1))
    assert factor.euler_factor_identity_exact

    result = adapter(
        polynomial_length_exponent=F(3),
        conductor_exponent_witness=F(1),
        required_log_saving_power=8,
    )
    assert result.polynomial_length_exponent == F(3)
    assert result.conductor_exponent_witness == F(1)
    assert result.required_log_saving_power == 8
    assert result.local_euler_factor_exact
    assert result.knightly_li_has_one_fixed_hecke_index
    assert result.linear_superposition_formally_creates_one_mobius_hecke_sum
    assert not result.qct_geometry_identified_with_generalized_kloosterman_family
    assert not result.two_mobius_weights_derived_as_hecke_polynomials
    assert result.classical_polynomial_conductor_saving_only_constant
    assert result.thorner_polynomial_conductor_saving_tends_to_one
    assert not result.spectral_conductor_verified
    assert not result.uniform_zero_free_log_saving_verified
    assert not result.published_coverage


def test_determinant_orbit_sends_the_hecke_index_to_delta_not_r_or_s() -> None:
    phase_identity = getattr(
        coverage_audit,
        "determinant_orbit_phase_identity",
        None,
    )
    adapter = getattr(
        coverage_audit,
        "determinant_orbit_hecke_index_audit",
        None,
    )
    assert phase_identity is not None, "determinant orbit identity is missing"
    assert adapter is not None, "determinant orbit Hecke audit is missing"

    for r, s, v, j, h in (
        (2, 5, 3, 1, 7),
        (5, 7, 4, -2, 3),
        (8, 9, -5, 4, -6),
    ):
        assert phase_identity(r=r, s=s, v=v, j=j, h=h)

    result = adapter()
    assert result.matrix_entries == ("r", "j", "s", "v")
    assert result.determinant_symbol == "delta"
    assert result.modulus_symbol == "s"
    assert result.residue_pair == ("r", "v")
    assert result.hecke_operator_index_symbol == "delta"
    assert result.kloosterman_fourier_indices == ("0", "-h")
    assert result.original_phase_reduces_to_linear_orbit_phase
    assert result.r_mobius_weights_residue_entry
    assert result.s_mobius_weights_modulus
    assert not result.delta_mobius_weight_present
    assert not result.knightly_li_superposition_targets_existing_mobius_weight
    assert not result.two_existing_mobius_weights_become_hecke_polynomials
    assert not result.qct_kernel_is_unweighted_complete_orbit
    assert not result.published_coverage


def test_fixed_modulus_kloosterman_completion_still_has_a_power_deficit() -> None:
    adapter = getattr(
        coverage_audit,
        "fixed_modulus_kloosterman_completion_audit",
        None,
    )
    assert adapter is not None, "fixed-modulus Kloosterman audit is missing"

    result = adapter(boundary_witnesses()["balanced_max_a"])
    assert result.modulus_exponent == F(3)
    assert result.h_exponent == F(5, 2)
    assert result.delta_exponent == F(5, 2)
    assert result.r_fourier_l2_exponent == F(3)
    assert result.h_coefficient_l2_exponent == F(5, 4)
    assert result.bp_57_dimensionless_factor_exponent == F(1, 2)
    assert result.bp_57_fixed_delta_s_exponent_before_completion == F(31, 4)
    assert result.completion_normalization_exponent == F(-3)
    assert result.bp_57_global_bound_exponent == F(41, 4)
    assert result.original_cardinality_exponent == F(11)
    assert result.bp_57_saving_exponent == F(3, 4)
    assert result.ck_gate_target_exponent == F(5999, 1000)
    assert result.remaining_deficit == F(4251, 1000)
    assert result.product_residue_energy_exponent == F(7)
    assert result.product_residue_l2_exponent == F(7, 2)
    assert result.kloosterman_operator_norm_exponent == F(3)
    assert result.orthogonality_global_bound_exponent == F(19, 2)
    assert result.orthogonality_saving_exponent == F(3, 2)
    assert result.orthogonality_remaining_deficit == F(3501, 1000)
    assert result.best_registered_route == "exact_kloosterman_orthogonality"
    assert result.mqw_size_lhs_exponent == F(13, 2)
    assert result.mqw_size_rhs_exponent == F(9, 2)
    assert result.mqw_size_condition_deficit == F(2)
    assert result.finite_r_completion_exact
    assert result.full_additive_fourier_support_required
    assert result.kernel_separated_optimistically
    assert not result.delta_unit_mod_s_verified
    assert not result.h_coprimality_mod_s_verified
    assert not result.mqw_direct_hypotheses_verified
    assert not result.direct_published_coverage


def test_v_equals_j_equals_one_is_an_exact_average_chowla_witness() -> None:
    box = boundary_witnesses()["balanced_max_a"]
    scales = h_poisson_subbox_scales(box, v=F(0), j=F(0))
    assert scales.volume == F(11, 2)
    assert scales.target == F(7, 2)
    assert scales.gate_target == F(3499, 1000)
    assert scales.required_saving == F(2001, 1000)
    assert scales.square_root_margin == F(749, 1000)


def test_wright_rejects_a_box_without_a_fixed_denominator_factor() -> None:
    box = boundary_witnesses()["balanced_max_a"]
    result = wright_fixed_factor_adapter(box, fixed_factor=None)
    assert not result.applicable
    assert result.reason == "no_fixed_denominator_factor"


def test_primary_route_is_unique_and_residual_is_explicit() -> None:
    small = ExponentBox(F(1), F(1), F(0), F(0), F(0), F(0), F(2))
    assert route_box(small).route == "bcr"

    balanced = boundary_witnesses()["balanced_max_a"]
    residual = route_box(balanced)
    assert residual.route == "mobius_farey_trilinear"
    assert residual.reason == "new_farey_trilinear_estimate_required"
    assert residual.saving is None


def test_farey_route_requires_a_shift_window_shorter_than_s() -> None:
    balanced = farey_trilinear_adapter(
        boundary_witnesses()["balanced_max_a"]
    )
    assert balanced.reason == "new_farey_trilinear_estimate_required"
    assert "j unique after splitting the sign of delta" in balanced.conditions

    r_long = farey_trilinear_adapter(boundary_witnesses()["r_long"])
    assert r_long.reason == "shift_window_not_shorter_than_s"
    assert route_box(boundary_witnesses()["r_long"]).route == (
        "global_coupled_operator"
    )


def test_hard_box_is_stationary_but_has_no_large_phase_parameter() -> None:
    scales = joint_phase_scales(boundary_witnesses()["balanced_max_a"])
    assert scales.stationary_h == F(5, 2)
    assert scales.on_stationary_face
    assert scales.t_phase_variation == F(0)
    assert scales.fourier_phase_variation == F(0)
    assert scales.same_sign_derivative_parameter == F(0)
    assert not scales.same_sign_power_saving


def test_bounded_dual_cell_requires_power_scale_kernel_spread() -> None:
    scales = dual_cell_isolation_scales(
        boundary_witnesses()["balanced_max_a"], dual_v=F(0)
    )
    assert scales.fourier_window == F(-1, 2)
    assert scales.normalized_h_spread == F(1, 2)
    assert scales.physical_h_support == F(3)
    assert scales.seminorm_cost_per_derivative == F(1, 2)
    assert not scales.uniform_in_original_kernel_class


def test_maximal_dual_scale_isolates_without_power_seminorm_loss() -> None:
    scales = dual_cell_isolation_scales(
        boundary_witnesses()["balanced_max_a"], dual_v=F(1, 2)
    )
    assert scales.fourier_window == F(0)
    assert scales.normalized_h_spread == F(0)
    assert scales.physical_h_support == F(5, 2)
    assert scales.uniform_in_original_kernel_class


def test_maximal_dual_box_is_at_the_farey_critical_scale() -> None:
    scales = farey_critical_scales(
        boundary_witnesses()["balanced_max_a"], dual_v=F(1, 2)
    )
    assert scales.j_interval == F(-1, 2)
    assert scales.at_most_one_j
    assert scales.rational_approximation == F(-1)
    assert scales.farey_spacing == F(-1)
    assert scales.approximation_minus_spacing == F(0)


def test_finite_residue_completion_has_exact_hard_box_gate() -> None:
    scales = farey_completion_scales(
        boundary_witnesses()["balanced_max_a"]
    )
    assert scales.v == F(1, 2)
    assert scales.residue_frequency == F(1, 2)
    assert scales.product_frequency == F(1)
    assert scales.residue_density_prefactor == F(-1, 2)
    assert scales.two_dimensional_completion_prefactor == F(2)
    assert scales.both_coordinate_axes_empty
    assert scales.farey_gate_target == F(3499, 1000)
    assert scales.normalized_gate_target == F(3999, 1000)
    assert scales.normalized_volume == F(7)
    assert scales.required_saving == F(3001, 1000)
    assert scales.square_root_margin == F(499, 1000)
    assert scales.generic_bcr_bound == F(67, 10)
    assert scales.generic_bcr_deficit == F(2701, 1000)
    assert scales.optimistic_distinct_large_sieve_bound == F(13, 2)
    assert scales.optimistic_distinct_large_sieve_deficit == F(2501, 1000)
    assert scales.fraction_multiplicity_exponent == F(1)
    assert scales.separated_additive_large_sieve_bound == F(7)
    assert scales.separated_additive_large_sieve_deficit == F(3001, 1000)
    assert scales.zero_residue_forces_centering


def test_mobius_trace_theorem_rejects_the_centered_cfk_family() -> None:
    audit = mobius_trace_function_audit(
        boundary_witnesses()["balanced_max_a"],
        modulus_is_prime=False,
        trace_is_nonexceptional=False,
    )
    assert audit.length_margin == F(3, 2)
    assert audit.length_hypothesis
    assert not audit.theorem_applicable
    assert not audit.power_target_covered
    assert audit.reasons == (
        "requires_prime_modulus",
        "linear_additive_trace_is_exceptional",
        "only_logarithmic_saving",
    )


def test_averaged_chowla_keeps_an_exact_three_power_hard_box_deficit() -> None:
    """Catch treating a logarithmic averaged-Chowla gain as a power gain."""
    adapter = getattr(coverage_audit, "averaged_chowla_shift_audit", None)
    assert adapter is not None, "averaged-Chowla adapter is missing"

    audit = adapter(boundary_witnesses()["balanced_max_a"])
    assert audit.shift == F(3)
    assert audit.product_frequency == F(1)
    assert audit.correlation_volume == F(7)
    assert audit.logarithmic_gate_target == F(4)
    assert audit.power_deficit == F(3)
    assert audit.unit_linear_slopes
    assert audit.zero_shift_excluded
    assert not audit.theorem_applicable
    assert audit.reasons == (
        "joint_s_shift_frequency_coefficient",
        "averaged_chowla_saves_only_logarithms",
        "positive_power_deficit",
    )


def test_linnik_centering_does_not_identify_a_linear_zero_mode_with_the_quadratic_diagonal() -> None:
    """Catch using the existing minus-one term as a Parseval subtraction."""
    adapter = getattr(
        coverage_audit,
        "linnik_dispersion_centering_audit",
        None,
    )
    assert adapter is not None, "Linnik-dispersion centering audit is missing"

    audit = adapter(
        boundary_witnesses()["balanced_max_a"],
        gate_log_power=F(8),
    )
    assert audit.parseval_diagonal_exponent == F(4)
    assert audit.logarithmic_gate_target_exponent == F(4)
    assert audit.power_margin == F(0)
    assert audit.gate_log_power == F(8)
    assert audit.aggregation_log_loss == F(7)
    assert audit.net_log_saving == F(1)
    assert audit.minus_one_homogeneity_degree == F(1)
    assert audit.parseval_homogeneity_degree == F(2)
    assert audit.minus_one_removes_fourier_zero_mode
    assert not audit.minus_one_subtracts_parseval_diagonal
    assert audit.variance_expansion_retains_signed_off_diagonal
    assert not audit.diagonal_only_majorant_closes
    assert audit.separate_quadratic_main_term_required
    assert not audit.subtracting_diagonal_after_cauchy_sufficient
    assert audit.signed_off_diagonal_must_cancel_diagonal
    assert audit.amplitude_level_projection_is_alternative
    assert audit.pre_cauchy_signed_subtraction_required
    assert not audit.published_coverage


def test_centered_resonance_collar_gains_twice_the_cutoff_slack() -> None:
    """Catch losing the squared resonance width in the centered sum."""
    adapter = getattr(coverage_audit, "centered_resonance_scales", None)
    assert adapter is not None, "centered-resonance adapter is missing"

    scales = adapter(
        boundary_witnesses()["balanced_max_a"],
        slack=F(1, 1000),
    )
    assert scales.product_frequency == F(1)
    assert scales.coefficient_first_moment == F(2)
    assert scales.resonance_cutoff == F(999, 1000)
    assert scales.phase_variation_at_cutoff == F(-1001, 1000)
    assert scales.near_resonance_bound == F(1999, 500)
    assert scales.logarithmic_gate_target == F(4)
    assert scales.saving == F(1, 500)
    assert scales.nonempty_collar


def test_centered_resonance_log_cutoff_pays_the_full_global_ledger() -> None:
    """Catch spending the logarithmic cutoff only once after summing shifts."""
    adapter = getattr(
        coverage_audit,
        "centered_resonance_log_budget",
        None,
    )
    assert adapter is not None, "centered-resonance log adapter is missing"

    budget = adapter(
        boundary_witnesses()["balanced_max_a"],
        gate_log_power=F(8),
    )
    assert budget.resonance_power_cutoff == F(1)
    assert budget.resonance_log_cutoff == F(4)
    assert budget.near_bound_power == F(4)
    assert budget.near_bound_log_saving == F(8)
    assert budget.aggregation_log_loss == F(7)
    assert budget.global_log_margin == F(1)
    assert budget.power_matches_gate
    assert budget.centered_completion_applicable
    assert budget.nonempty_log_collar
    assert budget.produces_little_o

    uncentered = adapter(
        boundary_witnesses()["r_long"],
        gate_log_power=F(8),
    )
    assert not uncentered.centered_completion_applicable
    assert not uncentered.produces_little_o

    empty = adapter(
        boundary_witnesses()["s_long"],
        gate_log_power=F(8),
    )
    assert empty.centered_completion_applicable
    assert not empty.nonempty_log_collar
    assert not empty.produces_little_o


def test_endpoint_tapers_expand_the_logarithmic_resonance_collar() -> None:
    """Catch counting two endpoint factors twice in the cutoff exponent."""
    adapter = getattr(
        coverage_audit,
        "endpoint_centered_resonance_log_budget",
        None,
    )
    assert adapter is not None, "endpoint-centered log adapter is missing"
    box = boundary_witnesses()["balanced_max_a"]

    budget = adapter(
        box,
        gate_log_power=F(8),
        endpoint_factors=2,
    )
    assert budget.resonance_power_cutoff == F(1)
    assert budget.endpoint_log_saving == F(2)
    assert budget.analytic_log_saving_required == F(6)
    assert budget.resonance_log_cutoff == F(3)
    assert budget.total_near_bound_log_saving == F(8)
    assert budget.global_log_margin == F(1)
    assert budget.full_power_collar_global_log_margin == F(-5)
    assert budget.endpoint_power_face
    assert budget.produces_little_o

    one_factor = adapter(
        box,
        gate_log_power=F(8),
        endpoint_factors=1,
    )
    assert one_factor.resonance_log_cutoff == F(7, 2)

    off_endpoint = adapter(
        boundary_witnesses()["s_long"],
        gate_log_power=F(8),
        endpoint_factors=2,
    )
    assert not off_endpoint.endpoint_power_face
    assert not off_endpoint.produces_little_o


def test_endpoint_critical_face_uses_a_cardinal_q_aggregation() -> None:
    """Catch treating the q-loss as harmonic after the absolute bound."""
    adapter = getattr(
        coverage_audit,
        "endpoint_critical_aggregation_budget",
        None,
    )
    assert adapter is not None, (
        "endpoint-critical aggregation adapter is missing"
    )
    box = boundary_witnesses()["balanced_max_a"]

    budget = adapter(
        box,
        endpoint_factors=2,
        q_logarithmic_depth=F(0),
        frequency_logarithmic_depth=F(0),
    )
    assert budget.raw_dyadic_log_loss == F(6)
    assert budget.endpoint_rs_removed == F(2)
    assert budget.ratio_k_removed == F(1)
    assert budget.critical_hl_removed == F(2)
    assert budget.remaining_dyadic_log_loss == F(1)
    assert budget.q_logarithmic_depth == F(0)
    assert budget.frequency_logarithmic_depth == F(0)
    assert budget.q_aggregation_is_cardinal
    assert budget.total_log_power_loss == F(1)
    assert budget.endpoint_log_saving == F(2)
    assert budget.net_log_power == F(1)
    assert budget.polyloglog_loss_exponent == F(2)
    assert budget.critical_face
    assert not budget.extra_log_saving_required
    assert budget.absolute_bound_produces_little_o

    logarithmic_q = adapter(
        box,
        endpoint_factors=2,
        q_logarithmic_depth=F(1),
        frequency_logarithmic_depth=F(0),
    )
    assert logarithmic_q.net_log_power == F(0)
    assert logarithmic_q.extra_log_saving_required
    assert not logarithmic_q.absolute_bound_produces_little_o

    off_face = adapter(
        boundary_witnesses()["s_long"],
        endpoint_factors=2,
        q_logarithmic_depth=F(0),
        frequency_logarithmic_depth=F(0),
    )
    assert not off_face.critical_face
    assert not off_face.absolute_bound_produces_little_o

    positive_q_power = adapter(
        boundary_witnesses()["large_q_endpoint"],
        endpoint_factors=2,
        q_logarithmic_depth=F(0),
        frequency_logarithmic_depth=F(0),
    )
    assert not positive_q_power.critical_face
    assert not positive_q_power.absolute_bound_produces_little_o


def test_fixed_slope_transfer_reaches_total_log_depth_below_three_halves() -> None:
    """Catch retaining MRT's 1/3000 exponent after Menon's improvement."""
    adapter = getattr(
        coverage_audit,
        "improved_averaged_chowla_shell_audit",
        None,
    )
    assert adapter is not None, (
        "improved averaged-Chowla shell adapter is missing"
    )
    box = boundary_witnesses()["balanced_max_a"]

    transferred = adapter(
        box,
        q_logarithmic_depth=F(5, 4),
        frequency_logarithmic_depth=F(0),
    )
    assert transferred.mrt_log_saving == F(1, 3000)
    assert transferred.unit_slope_improved_log_saving == F(1)
    assert transferred.fixed_slope_black_box_log_saving == F(1, 2)
    assert transferred.improved_polyloglog_loss_exponent == F(2)
    assert transferred.fixed_slope_polyloglog_loss_exponent == F(1)
    assert transferred.endpoint_absolute_log_margin == F(-1, 4)
    assert transferred.mrt_log_margin == F(-749, 3000)
    assert transferred.unit_slope_log_margin == F(3, 4)
    assert transferred.all_sector_log_margin == F(1, 4)
    assert transferred.all_sector_subface_covered
    assert transferred.fixed_slope_black_box_proved
    assert not transferred.fixed_slope_extension_required
    assert transferred.bv_separation_proved
    assert not transferred.bv_separation_required
    assert transferred.joint_coefficient_accepted
    assert not transferred.coprimality_transfer_required
    assert transferred.coprimality_transfer_proved
    assert transferred.published_coverage
    assert transferred.source == (
        "Menon, arXiv:2607.15574v1, "
        "Theorems improved_exp_sum and improved_avg_chowla"
    )

    boundary = adapter(
        box,
        q_logarithmic_depth=F(3, 2),
        frequency_logarithmic_depth=F(0),
    )
    assert boundary.unit_slope_log_margin == F(1, 2)
    assert boundary.all_sector_log_margin == F(0)
    assert not boundary.all_sector_subface_covered
    assert not boundary.published_coverage

    beyond = adapter(
        box,
        q_logarithmic_depth=F(2),
        frequency_logarithmic_depth=F(0),
    )
    assert beyond.unit_slope_log_margin == F(0)
    assert beyond.all_sector_log_margin == F(-1, 2)
    assert not beyond.all_sector_subface_covered
    assert not beyond.published_coverage


def test_completion_weight_bv_cost_is_amortized_on_retained_regimes() -> None:
    """Catch charging mixed BV derivatives twice against the same x*y loss."""
    adapter = getattr(
        coverage_audit,
        "completion_weight_bv_audit",
        None,
    )
    assert adapter is not None, "completion-weight BV adapter is missing"
    box = boundary_witnesses()["balanced_max_a"]

    low = adapter(box, x_log_scale=F(-1, 2), y_log_scale=F(-1, 2))
    assert low.kernel_first_derivative_log_cost == F(0)
    assert low.kernel_mixed_derivative_log_cost == F(0)
    assert low.absolute_frequency_log_depth == F(1)
    assert low.bv_net_log_depth == F(1)
    assert low.bv_extra_log_depth == F(0)
    assert low.low_variation_regime
    assert not low.stationary_log_face
    assert not low.offstationary_ibp_available
    assert low.centered_phase_power_slack == F(1)
    assert low.raw_first_moment_scale_preserved
    assert low.bv_preserves_global_log_depth

    stationary_high = adapter(
        box,
        x_log_scale=F(1, 2),
        y_log_scale=F(1, 2),
    )
    assert stationary_high.kernel_first_derivative_log_cost == F(1, 2)
    assert stationary_high.kernel_mixed_derivative_log_cost == F(1)
    assert stationary_high.amplitude_log_gain == F(1)
    assert stationary_high.absolute_frequency_log_depth == F(0)
    assert stationary_high.bv_net_log_depth == F(0)
    assert stationary_high.bv_extra_log_depth == F(0)
    assert not stationary_high.low_variation_regime
    assert stationary_high.stationary_log_face
    assert not stationary_high.raw_first_moment_scale_preserved
    assert stationary_high.bv_preserves_global_log_depth

    offstationary = adapter(
        box,
        x_log_scale=F(1, 2),
        y_log_scale=F(-1, 2),
    )
    assert offstationary.kernel_mixed_derivative_log_cost == F(1)
    assert offstationary.amplitude_log_gain == F(0)
    assert offstationary.bv_net_log_depth == F(1)
    assert offstationary.bv_extra_log_depth == F(1)
    assert offstationary.offstationary_log_gap == F(1)
    assert offstationary.offstationary_ibp_available
    assert not offstationary.retained_after_phase_partition
    assert not offstationary.raw_first_moment_scale_preserved
    assert not offstationary.bv_preserves_global_log_depth


def test_coprimality_transfer_has_d_squared_tail_and_polylog_twist() -> None:
    """Catch a d^-1 tail or a non-polylogarithmic restricted modulus."""
    adapter = getattr(
        coverage_audit,
        "coprimality_restricted_menon_audit",
        None,
    )
    assert adapter is not None, "coprimality Menon adapter is missing"
    box = boundary_witnesses()["balanced_max_a"]

    audit = adapter(
        box,
        q_logarithmic_depth=F(5, 4),
        frequency_logarithmic_depth=F(0),
        common_divisor_cutoff_log_depth=F(4),
    )
    assert audit.common_divisor_volume_decay == F(2)
    assert audit.common_divisor_tail_log_saving == F(4)
    assert audit.common_divisor_tail_log_margin == F(15, 4)
    assert audit.restricted_modulus_log_depth == F(21, 4)
    assert audit.fixed_slope_log_saving == F(1, 2)
    assert audit.all_sector_log_margin == F(1, 4)
    assert audit.exact_gcd_reindex_proved
    assert audit.tail_is_summable
    assert audit.principal_character_twist
    assert audit.polylog_twist_uniformity_proved
    assert audit.coprimality_transfer_proved
    assert audit.subface_covered

    boundary = adapter(
        box,
        q_logarithmic_depth=F(3, 2),
        frequency_logarithmic_depth=F(0),
        common_divisor_cutoff_log_depth=F(4),
    )
    assert boundary.all_sector_log_margin == F(0)
    assert boundary.coprimality_transfer_proved
    assert not boundary.subface_covered

    untruncated = adapter(
        box,
        q_logarithmic_depth=F(5, 4),
        frequency_logarithmic_depth=F(0),
        common_divisor_cutoff_log_depth=F(0),
    )
    assert untruncated.common_divisor_tail_log_margin == F(-1, 4)
    assert not untruncated.common_divisor_tail_produces_little_o
    assert not untruncated.subface_covered


def test_far_resonance_shell_has_the_exact_piecewise_power_deficit() -> None:
    """Catch dropping the centered phase before it saturates at distance T^2."""
    adapter = getattr(
        coverage_audit,
        "far_resonance_shell_scales",
        None,
    )
    assert adapter is not None, "far-resonance shell adapter is missing"
    box = boundary_witnesses()["balanced_max_a"]

    expected = {
        F(1): (F(-1), F(4), F(0), True),
        F(3, 2): (F(-1, 2), F(5), F(1), False),
        F(2): (F(0), F(6), F(2), False),
        F(5, 2): (F(0), F(13, 2), F(5, 2), False),
        F(3): (F(0), F(7), F(3), False),
    }
    for distance, want in expected.items():
        scales = adapter(box, distance=distance)
        assert scales.phase_amplitude == want[0]
        assert scales.absolute_bound == want[1]
        assert scales.required_power_saving == want[2]
        assert scales.at_power_barrier is want[3]
        assert scales.logarithmic_gate_target == F(4)


def test_inverse_resonance_bcr_deficit_worsens_across_the_shells() -> None:
    """Catch mapping the inverse variable back to length R instead of D."""
    adapter = getattr(
        coverage_audit,
        "inverse_resonance_bcr_scales",
        None,
    )
    assert adapter is not None, "inverse-resonance BCR adapter is missing"
    box = boundary_witnesses()["balanced_max_a"]

    expected = {
        F(1): (F(89, 10), F(75, 8), F(27, 8)),
        F(3, 2): (F(363, 40), F(153, 16), F(57, 16)),
        F(2): (F(37, 4), F(39, 4), F(15, 4)),
        F(5, 2): (F(387, 40), F(163, 16), F(67, 16)),
        F(3): (F(101, 10), F(85, 8), F(37, 8)),
    }
    for distance, want in expected.items():
        audit = adapter(box, distance=distance)
        assert audit.inverse_length == distance
        assert audit.modulus_length == F(3)
        assert audit.numerator_product_length == F(5)
        assert audit.term_1 == want[0]
        assert audit.term_2 == want[1]
        assert audit.deficit == want[2]
        assert audit.gate_target == F(6)
        assert not audit.joint_coefficient_accepted
        assert not audit.published_coverage


def test_primitive_fraction_large_sieve_improves_the_two_largest_shells() -> None:
    """Catch reintroducing product-frequency multiplicity for reduced w/s."""
    adapter = getattr(
        coverage_audit,
        "primitive_fraction_large_sieve_scales",
        None,
    )
    assert adapter is not None, "primitive-fraction large-sieve adapter is missing"
    box = boundary_witnesses()["balanced_max_a"]

    expected = {
        F(1): (F(15, 2), F(6), F(0), False),
        F(3, 2): (F(31, 4), F(7), F(1), False),
        F(2): (F(8), F(8), F(2), False),
        F(5, 2): (F(33, 4), F(33, 4), F(9, 4), True),
        F(3): (F(17, 2), F(17, 2), F(5, 2), True),
    }
    for distance, want in expected.items():
        audit = adapter(box, distance=distance)
        assert audit.large_sieve_bound == want[0]
        assert audit.best_unconditional_bound == want[1]
        assert audit.remaining_power_saving == want[2]
        assert audit.improves_absolute_bound is want[3]
        assert audit.gate_target == F(6)
        assert audit.fraction_multiplicity == F(0)
        assert audit.primitive_fraction_spacing == F(-6)


def test_reciprocal_clustering_flattens_the_middle_large_shell_deficit() -> None:
    """Catch omitting the S/D cluster multiplicity after reciprocity."""
    adapter = getattr(
        coverage_audit,
        "reciprocal_cluster_large_sieve_scales",
        None,
    )
    assert adapter is not None, "reciprocal-cluster adapter is missing"
    box = boundary_witnesses()["balanced_max_a"]

    expected = {
        F(2): (F(1), F(8), F(8), F(2), False),
        F(5, 2): (F(1, 2), F(8), F(8), F(2), True),
        F(3): (F(0), F(17, 2), F(17, 2), F(5, 2), False),
    }
    for distance, want in expected.items():
        audit = adapter(box, distance=distance)
        assert audit.cluster_multiplicity == want[0]
        assert audit.clustered_large_sieve_bound == want[1]
        assert audit.best_unconditional_bound == want[2]
        assert audit.remaining_power_saving == want[3]
        assert audit.improves_primitive_bound is want[4]
        assert audit.correction_within_resolution
        assert audit.farey_center_spacing == -2 * distance


def test_prime_factor_trace_twists_cannot_pay_the_far_shell_power_deficit() -> None:
    """Catch extrapolating FKM's small trace saving to the full shell gate."""
    adapter = getattr(
        coverage_audit,
        "prime_factor_trace_twist_audit",
        None,
    )
    assert adapter is not None, "prime-factor trace-twist adapter is missing"
    box = boundary_witnesses()["balanced_max_a"]

    maximal = adapter(
        box,
        distance=F(3),
        prime_factor_exponent=F(3),
        applications=2,
        eta=F(1, 25),
    )
    assert maximal.fkm_eta_ceiling == F(1, 24)
    assert maximal.interval_over_modulus_penalty == F(0)
    assert maximal.one_sided_power_saving == F(3, 25)
    assert maximal.optimistic_total_power_saving == F(6, 25)
    assert maximal.current_far_shell_deficit == F(5, 2)
    assert maximal.optimistic_residual_deficit == F(113, 50)
    assert maximal.trace_is_nonexceptional
    assert maximal.prime_modulus_hypothesis
    assert not maximal.nonzero_prime_frequency_uniform
    assert not maximal.uniform_prime_factor_available
    assert not maximal.joint_cofactor_accepted
    assert not maximal.optimistic_gate_covered
    assert not maximal.published_coverage

    middle = adapter(
        box,
        distance=F(2),
        prime_factor_exponent=F(2),
        applications=2,
        eta=F(1, 25),
    )
    assert middle.one_sided_power_saving == F(2, 25)
    assert middle.optimistic_total_power_saving == F(4, 25)
    assert middle.current_far_shell_deficit == F(2)
    assert middle.optimistic_residual_deficit == F(46, 25)

    with pytest.raises(ValueError, match="eta must be strictly below 1/24"):
        adapter(
            box,
            distance=F(3),
            prime_factor_exponent=F(3),
            applications=2,
            eta=F(1, 24),
        )


def test_squarefree_linear_completion_stalls_on_long_factor_subboxes() -> None:
    """Catch treating the Type-I quotient as an unrestricted geometric sum."""
    adapter = getattr(
        coverage_audit,
        "squarefree_linear_completion_audit",
        None,
    )
    assert adapter is not None, "squarefree linear-completion adapter is missing"
    box = boundary_witnesses()["balanced_max_a"]

    favorable = adapter(
        box,
        distance=F(3),
        short_factor_total=F(0),
    )
    assert favorable.long_quotient_interval == F(3)
    assert favorable.reduced_denominator_lower_bound == F(2)
    assert favorable.optimistic_theorem_bound == F(2)
    assert favorable.power_saving == F(1)
    assert favorable.remaining_shell_deficit == F(2)
    assert not favorable.factor_subbox_covered

    transition = adapter(
        box,
        distance=F(3),
        short_factor_total=F(1),
    )
    assert transition.long_quotient_interval == F(2)
    assert transition.optimistic_theorem_bound == F(2)
    assert transition.power_saving == F(0)
    assert transition.remaining_shell_deficit == F(3)
    assert not transition.factor_subbox_covered

    worst = adapter(
        box,
        distance=F(3),
        short_factor_total=F(2),
    )
    assert worst.long_quotient_interval == F(1)
    assert worst.optimistic_theorem_bound == F(1)
    assert worst.power_saving == F(0)
    assert worst.squarefree_support_retained
    assert not worst.coprimality_progressions_charged
    assert not worst.published_coverage


def test_type_ii_cauchy_identity_diagonal_exceeds_the_spectral_target() -> None:
    """Catch bounding the positive identity diagonal after Cauchy in b."""
    adapter = getattr(
        coverage_audit,
        "type_ii_cauchy_diagonal_audit",
        None,
    )
    assert adapter is not None, "Type-II Cauchy diagonal adapter is missing"
    box = boundary_witnesses()["balanced_max_a"]

    expected = {
        F(1): (F(2749, 250), F(-1, 250), F(6), F(1, 500)),
        F(3, 2): (F(2624, 250), F(-63, 125), F(25, 4), F(63, 250)),
        F(2): (F(2499, 250), F(-251, 250), F(13, 2), F(251, 500)),
    }
    for beta, want in expected.items():
        audit = adapter(box, b_exponent=beta)
        assert audit.identity_diagonal_exponent == F(11)
        assert audit.spectral_target_exponent == want[0]
        assert audit.spectral_target_margin == want[1]
        assert audit.post_cauchy_diagonal_exponent == want[2]
        assert audit.post_cauchy_target_deficit == want[3]
        assert audit.b_exponent_range == (F(1), F(2))
        assert audit.exact_identity_diagonal_present
        assert audit.dispersion_subtraction_required
        assert not audit.separate_diagonal_majorant_closes
        assert not audit.published_coverage


def test_zero_ray_has_exact_global_convolution_centering_but_local_residual() -> None:
    """Catch declaring the full mu*c_U zero after imposing factor boxes."""
    adapter = getattr(
        coverage_audit,
        "zero_ray_convolution_centering_audit",
        None,
    )
    assert adapter is not None, "zero-ray convolution audit is missing"
    box = boundary_witnesses()["balanced_max_a"]

    audit = adapter(box, b_exponent=F(3, 2))
    assert audit.a_exponent == F(3, 2)
    assert audit.product_ray_exponent == F(9, 2)
    assert audit.cutoff_exponent == F(1)
    assert audit.product_above_cutoff
    assert audit.full_convolution_vanishes_exactly
    assert audit.type_sector_convolution_equals_negative_mobius
    assert not audit.type_sector_convolution_vanishes
    assert audit.factorization_anchor_may_depend_only_on_product
    assert audit.factorization_anchor_leaves_explicit_mobius_main
    assert audit.dyadic_factor_localization_breaks_exact_zero
    assert audit.fixed_factor_phase_breaks_product_invariance
    assert audit.joint_gram_gate_required
    assert audit.joint_gram_target_exponent == F(2624, 250)
    assert audit.explicit_mobius_main_squared_exponent == F(11)
    assert audit.explicit_main_target_margin == F(-63, 125)
    assert not audit.separate_explicit_main_majorant_closes
    assert audit.joint_cross_term_required
    assert not audit.published_coverage


def test_primitive_slope_square_root_only_covers_the_large_slope_cells() -> None:
    """Catch spending nonexistent k-Möbius cancellation on a zero ray."""
    adapter = getattr(
        coverage_audit,
        "primitive_slope_zero_ray_audit",
        None,
    )
    assert adapter is not None, "primitive-slope zero-ray audit is missing"
    box = boundary_witnesses()["balanced_max_a"]

    expected = {
        F(0): (F(5), F(9, 2), False),
        F(1, 2): (F(9, 2), F(4), False),
        F(3, 5): (F(22, 5), F(39, 10), True),
        F(9, 2): (F(1, 2), F(0), True),
    }
    for theta, (g_exp, k_exp, closes) in expected.items():
        audit = adapter(box, b_exponent=F(3, 2), slope_exponent=theta)
        assert audit.slope_exponent_range == (F(0), F(9, 2))
        assert audit.common_n_factor_exponent == g_exp
        assert audit.common_y_factor_exponent == k_exp
        assert audit.primitive_pair_cardinality_exponent == 2 * theta
        assert audit.explicit_main_cardinality_exponent == F(11)
        assert audit.joint_gram_target_exponent == F(2624, 250)
        assert audit.required_power_saving == F(63, 125)
        assert audit.double_square_root_saving == theta
        assert audit.double_square_root_has_exponent_slack == closes
        assert audit.low_slope_benchmark_obstruction == (not closes)
        assert audit.primitive_slope_mobius_pair_retained
        assert not audit.common_k_mobius_cancellation_available
        assert not audit.primitive_slope_reciprocal_conductor_present
        assert not audit.published_coverage


def test_long_mobius_cutoff_removes_only_the_cardinality_diagonal_gap() -> None:
    """Catch fixing U=T, or claiming that a longer U proves off-diagonal."""
    adapter = getattr(
        coverage_audit,
        "long_mobius_cutoff_audit",
        None,
    )
    assert adapter is not None, "long Möbius-cutoff audit is missing"
    box = boundary_witnesses()["balanced_max_a"]

    original = adapter(
        box,
        cutoff_exponent=F(1),
        squared_target_saving=F(1, 250),
    )
    assert original.complementary_factor_max_exponent == F(2)
    assert original.worst_diagonal_margin == F(-251, 250)
    assert not original.all_factor_boxes_have_diagonal_power_slack
    assert not original.entire_zero_ray_cardinality_has_power_slack

    critical = adapter(
        box,
        cutoff_exponent=F(2),
        squared_target_saving=F(1, 250),
    )
    assert critical.complementary_factor_max_exponent == F(1)
    assert critical.identity_diagonal_exponent == F(11)
    assert critical.worst_spectral_target_exponent == F(2749, 250)
    assert critical.worst_diagonal_margin == F(-1, 250)
    assert not critical.all_factor_boxes_have_diagonal_power_slack

    optimized = adapter(
        box,
        cutoff_exponent=F(401, 200),
        squared_target_saving=F(1, 250),
    )
    assert optimized.complementary_factor_max_exponent == F(199, 200)
    assert optimized.long_factor_min_exponent == F(401, 200)
    assert optimized.identity_diagonal_exponent == F(11)
    assert optimized.worst_spectral_target_exponent == F(11001, 1000)
    assert optimized.worst_diagonal_margin == F(1, 1000)
    assert optimized.all_factor_boxes_have_diagonal_power_slack
    assert optimized.entire_zero_ray_cardinality_has_power_slack
    assert optimized.exact_single_sector_identity
    assert optimized.v_split_omitted_exactly
    assert optimized.reciprocal_modulus_exponent == F(3)
    assert not optimized.reciprocal_conductor_reduced
    assert optimized.zero_completion_endpoint_c_exponent == F(901, 100)
    assert optimized.full_off_diagonal_imposes_b_divides_delta is False
    assert not optimized.published_off_diagonal_coverage


def test_short_b_does_not_license_poisson_before_the_a_phase() -> None:
    """Catch absorbing a positive-power fixed-a frequency into a smooth weight."""
    adapter = getattr(
        coverage_audit,
        "long_cutoff_h_completion_audit",
        None,
    )
    assert adapter is not None, "long-cutoff h-completion audit is missing"
    box = boundary_witnesses()["balanced_max_a"]

    endpoint = adapter(box, b_exponent=F(199, 200))
    assert endpoint.a_exponent == F(401, 200)
    assert endpoint.common_b_period_surplus == F(301, 200)
    assert endpoint.fixed_a_normalized_frequency == F(599, 200)
    assert endpoint.full_modulus_period_surplus == F(-1, 2)
    assert not endpoint.fixed_a_phase_is_smooth_for_b_poisson
    assert not endpoint.b_only_poisson_valid
    assert endpoint.full_phase_modulus_exponent == F(3)
    assert not endpoint.published_coverage

    smallest_b = adapter(box, b_exponent=F(0))
    assert smallest_b.common_b_period_surplus == F(5, 2)
    assert smallest_b.fixed_a_normalized_frequency == F(2)
    assert not smallest_b.b_only_poisson_valid


def test_bc_fixed_determinant_corollary_is_worse_than_direct_counting() -> None:
    """Catch applying the published fixed-shift corollary in its wrong aspect."""
    adapter = getattr(
        coverage_audit,
        "bc_fixed_determinant_audit",
        None,
    )
    assert adapter is not None, "BC fixed-determinant audit is missing"
    box = boundary_witnesses()["balanced_max_a"]

    audit = adapter(box)
    assert audit.short_variable_exponents == (F(1, 2), F(1, 2))
    assert audit.long_variable_exponents == (F(3), F(3))
    assert audit.determinant_scale_exponent == F(7, 2)
    assert audit.fixed_shift_trivial_exponent == F(7, 2)
    assert audit.bc_corollary_error_exponent == F(111, 10)
    assert not audit.bc_corollary_beats_trivial
    assert audit.shift_range_exponent == F(5, 2)
    assert audit.summed_trivial_exponent == F(6)
    assert audit.global_target_exponent == F(3499, 1000)
    assert audit.required_mobius_saving == F(2501, 1000)
    assert audit.full_shift_average_required
    assert audit.coupled_kernel_separated_optimistically
    assert not audit.direct_corollary_hypotheses_verified
    assert not audit.published_coverage


def test_averaged_chowla_fails_already_on_the_logarithmic_shell_face() -> None:
    """Catch treating MRT's 1/3000 log saving as enough for the B>7 gate."""
    adapter = getattr(
        coverage_audit,
        "averaged_chowla_shell_audit",
        None,
    )
    assert adapter is not None, "averaged-Chowla shell adapter is missing"
    box = boundary_witnesses()["balanced_max_a"]

    critical = adapter(box, distance=F(1), gate_log_power=F(8))
    assert critical.required_power_saving == F(0)
    assert critical.theorem_log_saving == F(1, 3000)
    assert critical.required_log_saving == F(8)
    assert critical.log_shortfall == F(23999, 3000)
    assert not critical.theorem_applicable
    assert critical.reasons == (
        "joint_s_shift_frequency_coefficient",
        "insufficient_logarithmic_saving",
    )

    power_shell = adapter(box, distance=F(3, 2), gate_log_power=F(8))
    assert power_shell.required_power_saving == F(1)
    assert "positive_power_deficit" in power_shell.reasons
    assert not power_shell.theorem_applicable


def test_coverage_report_emits_the_minimal_far_shell_gate(capsys) -> None:
    """Catch a deterministic report which hides the narrowed residual theorem."""
    coverage_audit.main()
    output = capsys.readouterr().out
    assert (
        "balanced_max_a: linnik_centering=diagonal=4 target=4 "
        "linear_degree=1 energy_degree=2 minus_one_is_diagonal=False "
        "post_cauchy_subtraction_sufficient=False "
        "signed_cancellation=True net_log=1 covered=False"
    ) in output
    assert (
        "balanced_max_a: determinant_line_mobius="
        "0:n=5/2,volume=6,saving=2501/1000;"
        "1/4:n=11/4,volume=23/4,saving=2251/1000;"
        "1/2:n=3,volume=11/2,saving=2001/1000 "
        "growing_slopes=False coupled_weight=False covered=False"
    ) in output
    assert (
        "balanced_max_a: determinant_line_square_root="
        "0:margin=-1/1000,residual=1/1000;"
        "1/1000:margin=0,residual=0;"
        "1/2:margin=499/1000,residual=0 "
        "unimodular=True proved=False covered=False"
    ) in output
    assert (
        "balanced_max_a: mobius_progression_variance="
        "0:Q=1/2,dh_deficit=5/2,gs_margin=1,gs_range=True;"
        "1/2:Q=0,dh_deficit=3,gs_margin=3/2,gs_range=False "
        "second_mu=False coupled_weight=False covered=False"
    ) in output
    assert (
        "balanced_max_a: determinant_slope_square_function="
        "0:slopes=1,cauchy=1/2,diag=6,bound=7/2;"
        "1/4:slopes=1/2,cauchy=1/4,diag=11/2,bound=7/2;"
        "1/2:slopes=0,cauchy=0,diag=5,bound=7/2 "
        "endpoint_taper=2 square_log=4 endpoint_loss=1 "
        "diagonal_ok=True net_log=1 proved=False covered=False"
    ) in output
    assert (
        "balanced_max_a: endpoint_slope_offdiagonal="
        "0:ambient=11,saving=5,sqrt_margin=1/2,delta_max=5;"
        "1/4:ambient=21/2,saving=9/2,sqrt_margin=3/4,delta_max=5;"
        "1/2:ambient=10,saving=4,sqrt_margin=1,delta_max=5 "
        "square_log=4 four_mu=True proved=False covered=False"
    ) in output
    assert (
        "balanced_max_a: endpoint_cokernel_character="
        "0:required=5,char_sqrt=5/2,residual=5/2;"
        "1/4:required=9/2,char_sqrt=5/2,residual=2;"
        "1/2:required=4,char_sqrt=5/2,residual=3/2 "
        "smith=1,Delta chars=Delta not_Delta2=True proved=False covered=False"
    ) in output
    assert (
        "large_q_endpoint: endpoint_unpoisson="
        "solutions=1 denominator=3 per_q=-1 q_count=2 total=1 "
        "shift_log=0 taper_log=2 net_log=2 all_h=True zero_mode=True "
        "mobius=False bounded_subface=True whole_cell=False"
    ) in output
    assert (
        "large_q_endpoint: endpoint_critical_q_first="
        "shift_log=2 q_error=1/2 gcd_decay=2 menon=False "
        "fixed_zeta=True fixed_f=True two_limit=True covered=False "
        "above=False whole_cell=False"
    ) in output
    assert (
        "large_q_endpoint: growing_zeta_product_lift="
        "shift_log=2 taper_log=2 absolute_power=1 local_gate=T*L*o(1) "
        "gcd_log=False exact_lift=True centered=True published=False "
        "covered=False"
    ) in output
    assert (
        "large_q_endpoint: height_phase="
        "shift_log=2 zeta_log=3/2 ratio_log=1/2 pre_phase_log=0 "
        "arbitrary_decay=True retained=True "
        "covered=True boundary=False whole_cell=False"
    ) in output
    assert (
        "large_q_endpoint: boundary_reflection="
        "shift_log=2 zeta_log=2 q_free_prime_power=True prime_forced=True "
        "main_main=True mixed=True cross_scale=False formal_tail=tail*tail "
        "tail_phase=False "
        "covered=False"
    ) in output
    assert (
        "large_q_endpoint: subcritical_afe_completion="
        "gap=1/10 left_shift=1/8 remainder_save=1/80 local_power=1 "
        "local_residue=True regrouped=False divisor_completion=False "
        "crosses_transition=True endpoint_full=False covered=False"
    ) in output
    assert (
        "large_q_endpoint: transition_mellin_divisor="
        "common_z=True right_line=True absolute_right=True euler=True "
        "z0_lambda=True nonzero_sparse=False gaussian=True "
        "absolute_left=False cutoff_factor=False gate=False "
        "proved=False covered=False"
    ) in output
    assert (
        "large_q_transition: compact_mellin="
        "compact=True line=0 inversion=True rapid=True power_growth=0 "
        "twisted_divisor=True coprimality=True reflected_tail=True "
        "product=3/2 shift=1/2 absolute=3/2 critical_save=1/2 "
        "gate_save=501/1000 "
        "gate=True proved=False covered=False"
    ) in output
    assert (
        "large_q_transition: type_ii_diagonal="
        "1/3:diag=3,target=2747/750,margin=497/750;"
        "2/3:diag=3,target=2497/750,margin=247/750 "
        "subtraction=False diagonal_closes=True offdiag_gate=True "
        "proved=False covered=False"
    ) in output
    assert (
        "large_q_transition: kim_average_shifted="
        "X=3/2 H=1/2 b1=1 b2=1 h_power=2/3 bound=11/6 "
        "target=1499/1000 deficit=1003/3000 multiplicative=False "
        "mellin_uniform=False applicable=False covered=False"
    ) in output
    assert (
        "large_q_transition: type_ii_determinant="
        "1/3:zero=3,target=2747/750,margin=497/750,delta=8/3,"
        "y_modulus=10/3,y_sqrt=5/3,y_b_gap=4/3,y_dual=3;"
        "2/3:zero=3,target=2497/750,margin=247/750,delta=7/3,"
        "y_modulus=8/3,y_sqrt=4/3,y_b_gap=2/3,y_dual=2 "
        "zero_closes=True b_completion=False nonzero_gate=True "
        "proved=False covered=False"
    ) in output
    assert (
        "large_q_transition: type_ii_lcm_completion="
        "generic:beta=2/3,gcd=0,lcm=2,sqrt=1,b_gap=1/3,"
        "b_surplus=0,dual=4/3,required=501/250,remain=501/250,"
        "bp_loss=1/2;"
        "high_gcd:beta=2/3,gcd=3/4,lcm=5/4,sqrt=5/8,b_gap=0,"
        "b_surplus=1/24,dual=7/12,required=627/500,"
        "remain=3637/3000,bp_loss=5/16 "
        "lcm_phase=True smooth_b=False b_closes=False bp_closes=False "
        "covered=False"
    ) in output
    assert (
        "large_q_transition: long_cutoff_mobius_trace="
        "eta=1/10,beta=1/20,U=9/10,a=19/20,reflected=1/20,"
        "trace_margin=9/20,ambient=3,target=999/500,"
        "power_deficit=501/500 identity=True prime_modulus=False "
        "nonexceptional_uniform=False two_logs_close=False covered=False"
    ) in output
    assert (
        "large_q_transition: reciprocal_cluster_closure="
        "Dmax=1/2,A=1,cluster_bound=2,target=2,power_gap=0,"
        "taper_log=2,energy_log=1/2,shell_log=1,kernel_log=0,"
        "net_log=1/2,global_power=1 low_union=True "
        "residual=(1/2,1],top_save=1/2 whole_face=False"
    ) in output
    assert (
        "large_q_transition: far_shell_mobius_gate="
        "theta=1,bound=5/2,target=1999/1000,required=501/1000,"
        "fkm_eta=1/25,fkm_apps=2,fkm_save=2/25,"
        "fkm_residual=421/1000 two_mu=True coupled=True "
        "prime_factor=False frequency=False cofactor=False "
        "new_joint=True proved=False covered=False"
    ) in output
    assert (
        "large_q_transition: far_shell_factor_box="
        "theta=1,beta=2/3,U=1/3,V=1/3,a=1/3,"
        "cluster=5/2,target=999/500,required=251/500,"
        "diag=3,square_target=2497/750,diag_margin=247/750 "
        "shifted=True phase=True diag_closes=True nonzero_joint=True "
        "proved=False covered=False"
    ) in output
    assert (
        "large_q_transition: factor_square_geometry="
        "theta=1,beta=2/3,Gamma_max=4/3,zero=3,"
        "square_target=2497/750,zero_margin=247/750 "
        "cross_relation=True primitive_zero=True n_offdiag=True "
        "cluster_l2=True zero_closes=True nonzero_gate=True "
        "proved=False covered=False"
    ) in output
    assert (
        "large_q_transition: nonzero_gamma_shell="
        "theta=1,beta=2/3,xi=4/3,gamma=0,alpha=0,"
        "lcm=2,bdual=4/3,astep=1/3,orbit=2/3,"
        "cluster_square=13/3,target=2497/750,required=251/250 "
        "reciprocity_mod=1,reduces=False two_mu=True n_pair=True "
        "coupled=True exact_orbit=True square_proved=False required_gate=True "
        "proved=False covered=False"
    ) in output
    assert (
        "large_q_transition: gamma_graph_energy="
        "theta=3/4,beta=2/3,xi=1/3,fiber=0,degree=1/3,"
        "vertex_l2=11/4,bound=37/12,target=2497/750,"
        "margin=123/500,lhs=3/4,threshold=249/250 "
        "mobius=False phase=False covered=True"
    ) in output
    assert (
        "large_q_transition: gamma_graph_residual="
        "theta=3/4,beta=2/3,xi=13/12,fiber=3/4,"
        "bound=23/6,margin=-63/125 covered=False"
    ) in output
    assert (
        "large_q_transition: gamma_gcd_graph_top="
        "theta=1,beta=2/3,xi=4/3,gamma=1,alpha=1/100,"
        "raw_fiber=1,reduced_fiber=0,degree=97/300,"
        "bound=997/300,target=2497/750,margin=3/500,"
        "lhs=99/100,threshold=249/250 covered=True"
    ) in output
    assert (
        "large_q_transition: gamma_gcd_graph_primitive="
        "theta=1,beta=2/3,xi=4/3,gamma=0,alpha=0,"
        "reduced_fiber=1,degree=4/3,bound=13/3,"
        "margin=-251/250 covered=False"
    ) in output
    assert (
        "large_q_transition: cross_determinant_lattice="
        "theta=1,beta=2/3,xi=1/4,degree=1/4,vertex_l2=3,"
        "bound=13/4,target=2497/750,margin=119/1500,"
        "lhs=5/4,threshold=997/750 gcd_k=True fiber=True "
        "mobius=False covered=True"
    ) in output
    assert (
        "large_q_transition: cross_determinant_residual="
        "theta=1,beta=2/3,xi=1/3,bound=10/3,"
        "margin=-1/250 covered=False"
    ) in output
    assert (
        "large_q_transition: farey_hecke_orbit="
        "theta=1,beta=2/3,xi=1/3,hecke=1,entry=1,modulus=1,"
        "frequency=1,target=2497/750 determinant=True phase=True "
        "b_in_index=True mu_b_squared=True mu_index=False "
        "entry_mu=True cofactor_joint=True arch=True coupled=True "
        "kuznetsov=False new_entry_hecke=True proved=False covered=False"
    ) in output
    assert (
        "large_q_transition: farey_hecke_maximal="
        "theta=1,beta=2/3,xi=4/3,hecke=2 covered=False"
    ) in output
    assert (
        "large_q_transition: entry_mobius_factor="
        "theta=1,beta=2/3,eta=2/3,c=1/3,d=2/3,"
        "wright_size=True,wright_saving=-1,target=1/500,"
        "deficit=501/500 factor=True double_recip=True "
        "cofactor_joint=True shift_joint=True coupled=True "
        "hypotheses=False two_entry=True proved=False covered=False"
    ) in output
    assert (
        "large_q_transition: entry_mobius_short="
        "theta=1,eta=1/3,wright_size=False covered=False"
    ) in output
    assert (
        "large_q_transition: cross_gcd_lattice="
        "theta=1,beta=2/3,xi=1/3,alpha=1/100,omega=0,"
        "reduced=97/300,degree=97/300,bound=997/300,"
        "target=2497/750,margin=3/500,lhs=397/300,"
        "threshold=997/750 combined=True fiber=True "
        "mobius=False covered=True"
    ) in output
    assert (
        "large_q_transition: cross_gcd_maximal="
        "theta=1,beta=2/3,xi=4/3,alpha=1/3,omega=3/4,"
        "reduced=1/4,bound=13/4,margin=119/1500 covered=True"
    ) in output
    assert (
        "large_q_transition: cross_gcd_primitive="
        "theta=1,beta=2/3,xi=4/3,alpha=0,omega=0,"
        "reduced=4/3,bound=13/3,margin=-251/250 covered=False"
    ) in output
    assert (
        "large_q_transition: triple_gcd_lattice="
        "theta=1,beta=2/3,xi=1/3,alpha=0,gamma=1/100,omega=0,"
        "reduced=97/300,bound=997/300,target=2497/750,"
        "margin=3/500 triple=True mobius=False covered=True"
    ) in output
    assert (
        "large_q_transition: triple_gcd_maximal="
        "theta=1,beta=2/3,xi=4/3,alpha=1/3,gamma=1/3,"
        "omega=5/12,reduced=1/4,bound=13/4,"
        "margin=119/1500 covered=True"
    ) in output
    assert (
        "large_q_transition: triple_gcd_primitive="
        "theta=1,beta=2/3,xi=4/3,alpha=0,gamma=0,omega=0,"
        "reduced=4/3,bound=13/3,margin=-251/250 covered=False"
    ) in output
    assert (
        "large_q_transition: final_two_entry_gate="
        "theta=1,beta=2/3,xi=4/3,gcd=0,reduced=4/3,"
        "graph=13/3,sqrt_save=1,required=10/3,raw_target=10/3,"
        "margin=0,identity=True critical=True taper_log=4,"
        "energy_log=1,post_cauchy_log=3/2,beta_log=1,"
        "global_log=1/2,global_power=1 required_gate=True "
        "proved=False whole=False"
    ) in output
    assert (
        "large_q_transition: final_two_entry_slack="
        "theta=3/4,beta=2/3,xi=13/12,gcd=0,"
        "required=17/6,raw_target=10/3,margin=1/2 critical=False"
    ) in output
    assert (
        "large_q_transition: h_poisson_line_critical="
        "theta=1,gamma=0,H=1/2,v=1/2,j=1/2,delta0=1/2,n=1/2,"
        "inner=1,outer=1,pre=2,post=5/2,target=2,required=1/2,"
        "sqrt=1/2,margin=0,unimodular=True,critical=True,"
        "fixed_proved=False,square_function_proved=False,whole=False"
    ) in output
    assert (
        "large_q_transition: h_poisson_line_slack="
        "theta=3/4,gamma=0,j=1/4,post=9/4,required=1/4,"
        "sqrt=1/2,margin=1/4 critical=False"
    ) in output
    assert (
        "large_q_transition: h_poisson_line_maximal_gcd="
        "theta=1,gamma=1/2,delta0=0,n=1,post=2,required=0,"
        "absolute_target=True,tapers_close=True"
    ) in output
    assert (
        "large_q_transition: h_poisson_square_offdiagonal="
        "slope_pair=1,inner=1,expanded=3,diagonal=2,target=2,"
        "required=1,Delta_max=1,cokernel=1,char_sqrt=1/2,"
        "entry_remaining=1/2,zero_is_diagonal=True,cramer=True,"
        "cyclic=True,four_mu=True,hybrid_proved=False,square_proved=False"
    ) in output
    assert (
        "large_q_transition: delta_lattice_poisson="
        "kappa=1,delta_area=1,covolume=1,zero_density=0,"
        "entry_shell=3,zero_absolute=3,target=2,required=1,"
        "dual_long_spacing=-1/2,dual_transverse_spacing=1/2,"
        "active_long=1/2,active_transverse=0,primitive_exact=True,"
        "primitive_layers_worse=False,zero_separable=False,"
        "jacobian=True,gram=True,psd=True,offdiag_subtract=True,"
        "kernel_zero=False,sufficient_only=True,zero_proved=False,whole=False"
    ) in output
    assert (
        "large_q_transition: published_kloosterman_entry="
        "modulus=1,interval=1/2,required=1/2,"
        "bp=1/32,bp_deficit=15/32,mqw=1/100,mqw_deficit=49/100,"
        "pascadi=1/12,pascadi_deficit=5/12,four_bp=1/8,"
        "four_bp_deficit=3/8,sqrt_range=True,arbitrary=True,"
        "kernel=False,separable=False,fixed_modulus=False,"
        "pascadi_uniform=False,covered=False"
    ) in output
    assert (
        "large_q_transition: bourgain_garaev_multilinear="
        "modulus=1,atom=1/4,n=4,required=1/2,"
        "thm9=1/16,deficit9=7/16,thm10=1/24,deficit10=11/24,"
        "thm11_nmin=7,product=True,count=False,section10_4_Cmin=144,"
        "published_C=4,thm12_threshold=1/4,thm12_length=False,"
        "thm13_product=1,thm13_threshold=1/2,thm13_margin=1/2,"
        "thm13_product_holds=True,thm13_explicit=False,"
        "thm13_half_power=False,prime_required=True,all_prime=False,"
        "product_intervals=False,separable=False,phase=False,covered=False"
    ) in output
    assert (
        "large_q_transition: bourgain_garaev_iterated="
        "atom=1/4,subatoms=2,subatom=1/8,formal_n=8,nmin=7,"
        "formal_count=True,formal_product=True,thm11_half_power=False,"
        "prime_balanced=False,"
        "forces_seven=False,phase=False,all_prime=False,covered=False"
    ) in output
    assert (
        "large_q_transition: mobius_hecke_reciprocal_l="
        "line=1/2,required=1/2,k_first_degree=3,local_exact=True,"
        "k_converges=True,balanced_exact=True,L_factors=2,zeta_factors=3,"
        "balanced_k_first_degree=3,hecke_index_shift=True,"
        "mobius_entries_not_indices=True,conditional=True,"
        "kuznetsov=False,negative_moment=False,"
        "half_power=False,covered=False"
    ) in output
    assert (
        "large_q_transition: entry_weighted_relative_trace="
        "prime_bound=7,primes=2,3,5,7,level=210,log_level_scale=1,"
        "primorial=True,spherical_constant=True,entry_noninvariant=True,"
        "depth2=True,hecke_index_shift=True,polynomial=False,"
        "published=False,covered=False"
    ) in output
    assert (
        "large_q_transition: small_prime_spectral_hybrid="
        "factor_cap=7,fixed_cutoff=1/8,level_exponent=2,required=1/2,"
        "rough_power=0,deficit=1/2,log_cutoff_polynomial=True,"
        "log_cutoff_fixed_count=False,fixed_count_superpoly=True,"
        "published=False,covered=False"
    ) in output
    assert (
        "large_q_transition: general_cutoff_line_gate="
        "kappa=1,gamma=1/2,alpha=1/2,u=2/3,v=1/4,U=1/3,V=1/8,"
        "e_left=1/42,e_right=1/8,signed_sqrt=143/336,"
        "unsigned_sqrt=25/336,required=1/2,total=1/2,margin=0,"
        "identity=True,cutoff_slack=False,covered=False"
    ) in output
    assert (
        "large_q_transition: bblr_quadratic_divisor="
        "hard:gamma=0,alpha=1,P=2,s1=0,s2=0,S=0,M=0,X=2,"
        "sharp=False,general1=5/2,h2=2,best=5/2,target=2,"
        "margin=-1/2,global_margin=-1/2;"
        "subcritical:gamma=4/5,alpha=1/5,P=6/5,s1=1/5,s2=1/5,"
        "S=2/5,M=1/5,X=1,sharp=True,e_ab=11/10,e_watt=23/20,"
        "best=23/20,target=6/5,margin=1/20,main=False,covered=False"
    ) in output
    assert (
        "large_q_transition: bblr_unsigned_recombination="
        "one=-1,four=1,outer_recombination=True;"
        "lemma15:d0:z=5/2,x=0,dcount=0,layer=5/2;"
        "d1:z=-1,x=1,dcount=1,layer=1;"
        "global=5/2,target=2,margin=-1/2,improved=False"
    ) in output
    assert (
        "large_q_transition: banks_shparlinski_pre_cauchy="
        "entry=1,v=1/2,j=1/2,slopes=1,shift=1/2,fixed_count=1,"
        "theorem=3/2,best=1,H=1/2,aggregate=5/2,target=2,"
        "margin=-1/2,short_threshold=5/8,short_actual=1/2,"
        "short_margin=-1/8,fix_slopes=True,shift_mu=False,"
        "convolution=True,convolution_power=False,hypotheses=False,"
        "covered=False"
    ) in output
    assert (
        "large_q_transition: ramare_medium_prime="
        "proper:alpha=1,lower=1/4,upper=3/4,required=1,"
        "prime_exception=1,log_density=1,power_density=0,deficit=1,"
        "reaches=False,exceptional=True,in_sum=False;"
        "full:upper=1,reaches=True,in_sum=True,prime_factor=1,cofactor=0,"
        "positive_factors=1,forces_two=False,covered=False"
    ) in output
    assert (
        "large_q_transition: prime_kloosterman="
        "q=1,X=1,required=1/2,unrestricted_bound=17/18,"
        "unrestricted_save=1/18,progression_bound=191/192,"
        "progression_save=1/192,progression_modulus_cap=1/100,"
        "four_unrestricted=2/9,unrestricted_deficit=5/18,"
        "four_progression=1/48,progression_deficit=23/48,"
        "fixed_prime=True,actual_prime=False,kernel=False,separable=False,"
        "covered=False"
    ) in output
    assert (
        "balanced_max_a: centered_log_cutoff_power=1 "
        "centered_log_cutoff_log=4 near_bound_log=8 "
        "global_log_margin=1"
    ) in output
    assert (
        "balanced_max_a: endpoint_log_cutoff_power=1 "
        "endpoint_log_cutoff_log=3 endpoint_log_saving=2 "
        "full_collar_global_margin=-5"
    ) in output
    assert (
        "balanced_max_a: endpoint_critical_log_loss=1 "
        "endpoint_taper=2 net_log_power=1 polyloglog_loss=2 "
        "q_aggregation=cardinal absolute_little_o=True"
    ) in output
    assert (
        "balanced_max_a: improved_chowla_total_depths="
        "0:3/2,5/4:1/4,3/2:0,2:-1/2 "
        "covered_all_slopes_beta_plus_gamma_lt_3/2=True "
        "joint_weight=True coprimality=True"
    ) in output
    assert (
        "balanced_max_a: completion_bv_regimes="
        "low:depth=1,extra=0,keep=True;"
        "stationary_high:depth=0,extra=0,keep=True;"
        "offstationary:depth=1,extra=1,keep=False"
    ) in output
    assert (
        "balanced_max_a: coprimality_transfer="
        "d_decay=2 d_tail=4 modulus_log=21/4 "
        "margin=1/4 covered=True"
    ) in output
    assert (
        "balanced_max_a: centered_far_shell_required_savings="
        "1:0,3/2:1,2:2,5/2:5/2,3:3 "
        "mrt_critical_log_shortfall=23999/3000"
    ) in output
    assert (
        "balanced_max_a: primitive_ls_best_remaining="
        "1:0,3/2:1,2:2,5/2:9/4,3:5/2"
    ) in output
    assert (
        "balanced_max_a: reciprocal_cluster_best_remaining="
        "2:2,5/2:2,3:5/2"
    ) in output
    assert (
        "balanced_max_a: optimistic_prime_trace_twists="
        "2:save=4/25,remain=46/25;"
        "3:save=6/25,remain=113/50 covered=False"
    ) in output
    assert (
        "balanced_max_a: squarefree_linear_completion="
        "0:save=1,remain=2;1:save=0,remain=3;"
        "2:save=0,remain=3 covered=False"
    ) in output
    assert (
        "balanced_max_a: type_ii_cauchy_diagonal="
        "1:margin=-1/250,post_deficit=1/500;"
        "3/2:margin=-63/125,post_deficit=63/250;"
        "2:margin=-251/250,post_deficit=251/500 "
        "subtraction=True"
    ) in output
    assert (
        "balanced_max_a: zero_ray_convolution_centering="
        "product=9/2 cutoff=1 full_zero=True "
        "sector_main=-mu main_sq=11 cross=True joint_gate=True"
    ) in output
    assert (
        "balanced_max_a: primitive_slope_zero_ray="
        "0:need=63/125,sqrt=0,slack=False;"
        "1/2:need=63/125,sqrt=1/2,slack=False;"
        "3/5:need=63/125,sqrt=3/5,slack=True;"
        "9/2:need=63/125,sqrt=9/2,slack=True "
        "proved=False k_mu=False slope_phase=False"
    ) in output
    assert (
        "balanced_max_a: long_mobius_cutoff="
        "1:bmax=2,margin=-251/250,diag=False;"
        "2:bmax=1,margin=-1/250,diag=False;"
        "401/200:bmax=199/200,margin=1/1000,diag=True "
        "zero_ray=True offdiag=False recip=3 zero_c_endpoint=901/100 "
        "global_b_divides_delta=False"
    ) in output
    assert (
        "balanced_max_a: long_cutoff_h_completion="
        "0:b_surplus=5/2,a_freq=2,valid=False;"
        "199/200:b_surplus=301/200,a_freq=599/200,valid=False "
        "full_surplus=-1/2 proved=False"
    ) in output
    assert (
        "balanced_max_a: long_cutoff_quotient_split="
        "0:dlevel=1,modulus=3/2,emax=2;"
        "199/200:dlevel=1/200,modulus=3/2,emax=2 "
        "gcd_reduces=True direct_bv=False covered=False"
    ) in output
    assert (
        "balanced_max_a: quotient_bdh="
        "0:bdh=9/2,bdh_deficit=1001/1000,"
        "centered=9/2,centered_deficit=501/1000;"
        "3/2:bdh=21/4,bdh_deficit=1751/1000,"
        "centered=19/4,centered_deficit=751/1000 "
        "common=False phase=False covered=False"
    ) in output
    assert (
        "balanced_max_a: pascadi_incomplete="
        "i2_regular=11 i2_exceptional=11 bound=8 "
        "target=3499/1000 deficit=4501/1000 "
        "assumption14=False direct=False covered=False"
    ) in output
    assert (
        "balanced_max_a: centered_quotient_poisson="
        "emax=2 squarefree=True coprime=True "
        "nonzero_mass=theta00 minus_one=False unweighted=False "
        "recloses=True conductor=False covered=False"
    ) in output
    assert (
        "balanced_max_a: hecke_mobius_spectral="
        "x=3 conductor_witness=1 B=8 euler=True fixed_index=True "
        "one_polynomial=True qct_geometry=False two_polynomials=False "
        "classical_constant=True thorner_to_one=True conductor=False "
        "zero_free=False covered=False"
    ) in output
    assert (
        "balanced_max_a: determinant_orbit_hecke="
        "det=delta modulus=s residues=r,v hecke_index=delta "
        "fourier=0,-h phase=True mu_r=entry mu_s=modulus mu_delta=False "
        "superposition=False two_polynomials=False complete_orbit=False "
        "covered=False"
    ) in output
    assert (
        "balanced_max_a: fixed_modulus_kloosterman="
        "rhat_l2=3 h_l2=5/4 bp_factor=1/2 fixed=31/4 "
        "global=41/4 saving=3/4 target=5999/1000 "
        "deficit=4251/1000 energy=7 orth_global=19/2 "
        "orth_deficit=3501/1000 best=exact_kloosterman_orthogonality "
        "mqw=13/2>9/2 mqw_deficit=2 "
        "full_fourier=True delta_unit=False h_coprime=False direct=False"
    ) in output
    assert (
        "balanced_max_a: bc_fixed_determinant="
        "error=111/10 fixed_trivial=7/2 summed_trivial=6 "
        "target=3499/1000 mobius_save=2501/1000 "
        "direct=False covered=False"
    ) in output


def test_coverage_note_has_hypothesis_and_residual_ledgers() -> None:
    text = COVERAGE_NOTE.read_text()
    for marker in (
        "## 2. Exact BCR adapter",
        "## 3. Completion adapters",
        r"v=k s+\delta\bar r",
        r"\delta=rv-js",
        r"\mathrm{SM}_{1/1000}",
        r"T^{7/2-1/1000}",
        r"\mathrm{RES}_{1,1}",
        r"T^{11/2}",
        r"T^{2+1/1000}",
        r"\mathrm{CFK}_{\epsilon,1/1000}",
        r"T^{4-1/1000}",
        r"2701/1000",
        r"\sum_{c\bmod s}\Omega(c)=0",
        r"e(crv/s)-1",
        "linear_additive_trace_is_exceptional",
        r"\mathrm{CMT}_{\epsilon,1/1000}",
        r"\Gamma_{r,s,\epsilon}(a)",
        r"2501/1000",
        "fraction can occur with multiplicity",
        r"\mathfrak S_q[\Psi]=\frac{HL}{S}\mathfrak D_q^{(2)}[\Theta]",
        r"\sum_c\Theta(c,v)=\sum_v\Theta(c,v)=0",
        r"d e b v-j s=\delta",
        r"D_{B,V}=\frac{S^{1/2}}{4BV\mathscr L^{C_0}}",
        r"\mathrm{QBV}_{\epsilon}",
        r"\mathrm{QII}_{\epsilon}",
        "standard Bombieri--Vinogradov hypotheses are not verified",
        "Pascadi, arXiv:2404.04239v3, Corollary 18",
        r"T^8",
        r"\frac{4501}{1000}",
        "## 4. Wright fixed-factor adapter",
        "## 5. Exact residual witnesses",
        "published coverage result: residual cells remain",
    ):
        assert marker in text
    assert "-37/8" in text
    assert "no_fixed_denominator_factor" in text


def test_alternative_routes_note_records_the_endpoint_critical_ledger() -> None:
    text = ALTERNATIVE_ROUTES_NOTE.read_text()
    for marker in (
        "## 4.9 Exact endpoint-critical aggregation ledger",
        r"\kappa+\rho=\kappa+\sigma=3",
        r"k+\sigma=m+\rho",
        r"h=\sigma-m",
        r"\ell=m+\rho-1",
        r"(\log\log T)^2",
        r"\mathscr L^{-1/3000}",
        "## 4.10 Improved averaged-Chowla subface",
        "arXiv:2607.15574v1",
        r"\frac{(\log\log X)^2}{\log X}",
        r"0\le\beta+\gamma<2",
        "fixed-slope square-root transfer",
        "proved from the exponential-sum theorem",
        "### 4.13 Prime-factor trace twists",
        "arXiv:1211.6043v3, Theorem 1.7",
        r"\frac{113}{50}",
        "### 4.14 Linear completion",
        "arXiv:1105.1616v1, Theorem 3",
        r"\tau=u+\beta\ge1",
        "published coverage remains false",
        "### 4.15 Hecke--Möbius Euler product and the missing spectral adapter",
        r"D_{f,p}(z)=1-\lambda_f(p)p^{-z}",
        r"\frac{H_f(z)}{L(z,f)}",
        "Knightly--Li, arXiv:1202.0189, Theorem 7.14",
        r"\eta_T\log X\ge B\log\log T",
        "Thorner, arXiv:2608.12257v1, Theorem 1.1",
        "does not supply the required logarithmic saving",
        "### 4.16 Exact determinant orbit: the Hecke index is the shift",
        r"M=\begin{pmatrix}r&j\\s&v\end{pmatrix}",
        r"rv\equiv\delta\pmod s",
        r"S(0,-h;\delta;s)",
        "the Hecke-operator index is",
        r"the shift \(\delta\)",
        "not either of the two Möbius variables",
        "### 4.17 Fixed-modulus completion and the 2026 bilinear bounds",
        r"\frac1s\sum_{m\bmod s}\widehat F_s(m)",
        r"S(-h\delta,m;s)",
        "Blomer--Pascadi, arXiv:2607.24311v1, Theorem 5.7",
        r"T^{41/4+o(1)}",
        r"\frac{4251}{1000}",
        r"\sum_{a\bmod s}|A_s(a)|^2",
        r"\ll T^{7+\varepsilon}",
        r"T^{19/2+\varepsilon}",
        r"\frac{3501}{1000}",
        "Milićević--Qin--Wu, arXiv:2511.07550v1, Theorem 1.1",
        r"T^{13/2}>T^{9/2}",
        "### 4.18 Exact Linnik-centering audit",
        r"Z(z\Theta)=zZ(\Theta)",
        r"E(z\Theta)=|z|^2E(\Theta)",
        r"\mathcal V=\mathcal D+\mathcal O",
        r"\mathcal O=-\mathcal D+",
        r"RCV=T^4",
        r"B>7",
        "linnik_dispersion_centering_audit",
        "published_coverage=False",
        "### 4.19 Exact determinant-line form",
        r"r_n=r_0+j_0n",
        r"s_n=s_0+v_0n",
        r"\mu(r_0+j_0n)\mu(s_0+v_0n)",
        r"\mathbf1_{(r_n,s_n)=1}",
        r"6-\gamma",
        r"\frac{2501}{1000}-\gamma",
        r"\frac{2001}{1000}",
        "determinant_line_mobius_audit",
        "### 4.20 Unimodular two-variable square-root gate",
        r"xv_0+yj_0=1",
        r"\mathrm{USR}_{B}(g,j_0,v_0)",
        r"T^{7/2-\gamma}",
        r"\gamma-\frac1{1000}",
        r"T^{1/1000-\gamma}",
        "determinant_line_square_root_audit",
        "### 4.21 Möbius progression variance",
        r"\frac6{\pi^2}XQ",
        r"X(\log X)^{-A}\le Q\le X",
        r"X=T^3",
        r"Q=T^{1/2-\gamma}",
        r"T^{5/2+\gamma}",
        r"Q_1=X(\log X)^{-C}",
        r"\ll_A X^2(\log X)^{-A}",
        r"T^6(\log T)^{-A}",
        "arXiv:1703.06865v2",
        r"1+\gamma",
        "mobius_progression_variance_audit",
        "### 4.22 Endpoint determinant slope square function",
        r"6-2\gamma",
        "is impossible",
        r"\mathrm{EDSSF}(g)",
        r"T^6(\log(2T))^{-4}",
        r"T^\gamma T^{1/2-\gamma}T^3",
        r"T^{7/2}(\log(2T))^{-2}",
        r"\tau_Q(d)",
        "determinant_slope_square_function_audit",
        "arbitrary_log_saving_below_diagonal_requested=False",
        "square_function_estimate_proved=False",
        "### 4.23 Cross-determinant expansion of EDSSF",
        r"\Delta_{12}=r_1s_2-r_2s_1",
        r"v_0=\frac{\delta_1s_2-\delta_2s_1}{\Delta_{12}}",
        r"j_0=\frac{\delta_1r_2-\delta_2r_1}{\Delta_{12}}",
        r"11-2\gamma",
        r"5-2\gamma",
        r"\frac12+\gamma",
        r"|\Delta_{12}|\ll T^5",
        r"\mathrm{ODSF}(g)",
        "signed four-Möbius",
        "endpoint_slope_offdiagonal_audit",
        "offdiagonal_estimate_proved=False",
        "### 4.24 Smith normal form and the single cokernel character family",
        r"\operatorname{SNF}(B)=\operatorname{diag}(1,|\Delta_{12}|)",
        r"|B^{-T}\mathbb Z^2/\mathbb Z^2|=|\Delta_{12}|",
        r"\frac1{|\Delta_{12}|}",
        "not two independent congruences",
        r"T^{5/2}",
        "hybrid character--entry",
        "endpoint_cokernel_character_audit",
        "hybrid_character_entry_estimate_proved=False",
        "### 4.25 Unconditional large-q bounded-zeta endpoint",
        r"\mathcal U^{\ne0}_{q;R,S,K,M,L}",
        r"m_1s-m_2r=\delta",
        r"O_{K,M,L}(R)",
        r"\ll_W\frac{T}{q}(\log(2T))^{-2}",
        r"\sum_{q\asymp T^2}",
        "covered_by_endpoint_unpoisson",
        "large_q_endpoint_unpoisson_audit",
        r"0\le\lambda<2",
        "does not promote the entire",
        "unconditional_coverage=True",
        "### 4.26 q-first Euler factorization audit at the critical shift depth",
        r"\mathfrak g(n)=\prod_{p\mid n}\left(1+\frac1p\right)^{-1}",
        r"f=\mu*h",
        r"h(p^a)=\frac1{p+1}",
        r"\sum_{n\ge1}\frac{|h(n)|}{n^\sigma}<\infty",
        r"H_D(n):=\sum_{\substack{a\mid n\\a>D}}|h(a)|",
        r"\sum_{d>D}\frac1{d^2}+\frac{\log(2L)}{L}",
        r"\lambda=2",
        "q_restriction_removed_before_correlation=True",
        "fixed_zeta_scales_required=True",
        "large_q_endpoint_critical_shift_audit",
        "full_height_phase_must_remain_in_correlation=True",
        "critical_shift_subface_covered=False",
        "### 4.27 Growing zeta scales: exact product lift and centered energy gate",
        r"A_{P,\nu}(n):=\sum_{\substack{ms=n",
        r"m_1s-m_2r=\delta",
        r"\mathfrak C_{P,L}",
        r"o_W(TL)",
        "gcd_divisibility_removes_spurious_log_loss=True",
        "large_q_growing_zeta_product_lift_audit",
        "centered_product_energy_estimate_proved=False",
        "### 4.28 Height-phase closure below the product-scale boundary",
        r"T\left(1+\frac{|\delta|}{M}\right)^{-A}",
        r"\mathscr L^{\lambda-2}",
        r"\mathscr L^\pi",
        r"\pi<2",
        "large_q_height_phase_audit",
        "strict_subface_covered=True",
        "### 4.29 Restricted divisor completion and the reflected-tail boundary",
        r"n^{(q)}",
        r"\Lambda(n^{(q)})",
        "squarefree_reduced_variable_forces_prime=True",
        "large_q_boundary_reflection_audit",
        r"\mathfrak C^{\mathrm{tail}\times\mathrm{tail}}_{P,L}",
        "cross_scale_aggregation_proved=False",
        "reflected_tail_energy_estimate_proved=False",
        "### 4.30 Subcritical AFE residue and the remaining cross-scale obstruction",
        r"m_1m_2\le T^{1-\eta}",
        r"T^{-c\eta}",
        "large_q_subcritical_afe_completion_audit",
        "local_endpoint_afe_weight_replaced_by_residue=True",
        "subcritical_cross_scale_aggregation_proved=False",
        "full_divisor_completion_crosses_afe_transition=True",
        "full_endpoint_cross_scale_aggregation_proved=False",
        "### 4.31 Why one left-line twisted-divisor energy is not exact",
        r"P_a(z):=\prod_{p\mid a}(1-p^z)",
        r"\log X\,P_{n^{(q)}}(z)-P'_{n^{(q)}}(z)",
        "large_q_transition_mellin_divisor_audit",
        "transition_reduced_to_one_twisted_divisor_energy=False",
        "twisted_divisor_energy_estimate_proved=False",
        "### 4.32 Scale-stable transition gate on the zero Mellin line",
        r"D_{q,X,i\tau}(n)",
        "coprime_divisor_pair_identity",
        "large_q_transition_compact_mellin_audit",
        "transition_reduced_to_compact_mellin_energy=True",
        "compact_mellin_energy_estimate_proved=False",
        "### 4.33 Transition Type-II diagonal and the nonzero Gram gate",
        r"4-\beta-\frac1{250}",
        r"\frac{247}{750}",
        "transition_type_ii_nonzero_gram_estimate_proved=False",
        "### 4.34 Published average-shift theorem still has a power deficit",
        "arXiv:2509.24152v2, Theorem 1.2",
        r"\frac{1003}{3000}",
        "transition_kim_average_shifted_convolution_audit",
        "### 4.35 Exact transition determinant gate after Type-II Cauchy",
        r"\Delta=n_1y_2-n_2y_1",
        r"T^{4-2\beta}",
        "transition_type_ii_determinant_audit",
        "### 4.36 Minimal common-b conductor is the lcm modulus",
        r"\ell=[s_1,s_2]",
        r"\frac{314}{375}",
        "arXiv:2607.24311v1, Theorem 5.7",
        "transition_type_ii_lcm_completion_audit",
        "### 4.37 Long-cutoff Möbius trace route has only logarithmic saving",
        "arXiv:1804.01337v2, Theorem 2.1",
        r"\frac{501}{500}",
        "transition_long_cutoff_mobius_trace_audit",
        "### 4.38 Unconditional square-root difference collar at transition",
        r"\sum_a|\nu(a)|^2\ll_W HL\log(2\min(H,L))",
        r"T(\log T)^{-1/2}",
        "transition_reciprocal_cluster_closure_audit",
        "### 4.39 The remaining transition far-shell trilinear gate",
        r"\mathrm{TFS}_{\theta}",
        r"\theta-\frac12+\frac1{1000}",
        r"\frac{421}{1000}",
        "transition_far_shell_mobius_gate_audit",
        "### 4.40 Exact Type-I/II factor boxes for the far-shell gate",
        r"ab-ks=w",
        r"\mathcal F_{\theta,\beta}",
        "transition_far_shell_factor_box_audit",
        "### 4.41 Full zero geometric Gram closes after factorization",
        r"\Gamma=a_1s_2-a_2s_1",
        r"a_2w_1-a_1w_2=k\Gamma",
        "transition_factor_square_geometry_audit",
        "### 4.42 Exact nonzero determinant shells and affine orbit",
        r"s_i=s_i^{(0)}+u_i t",
        r"2\theta-1+\frac1{250}",
        "transition_nonzero_gamma_shell_audit",
        "### 4.43 Unconditional low-determinant graph-energy region",
        r"\sum_{\{x,y\}\in E}|z_xz_y|",
        r"\theta+\lambda\le\frac{249}{250}",
        "transition_gamma_graph_energy_audit",
        "### 4.44 Gcd-sensitive graph-degree sharpening",
        r"\lambda_\gamma",
        r"\theta-\alpha+\lambda_\gamma\le\frac{249}{250}",
        "transition_gamma_gcd_graph_energy_audit",
        "### 4.45 Primitive cross-determinant lattice removes the rounding loss",
        r"(a_i,w_i)=(a_i,ks_i)\mid k",
        r"\theta+\xi\le2-\beta-\frac1{250}",
        "transition_cross_determinant_lattice_audit",
        "### 4.46 Exact Farey--Hecke orbit of the remaining band",
        r"x_1W_2-x_2W_1",
        r"a_i=\frac{\epsilon_i(W_i+kx_i)}b",
        "transition_farey_hecke_orbit_audit",
        "### 4.47 Second Möbius factorization and exact double reciprocity",
        r"x=\epsilon cd",
        r"\frac{501}{500}",
        "transition_entry_mobius_factorization_audit",
        "### 4.48 Combined factor/shift gcd reduction",
        r"d_w=(w_1,w_2)",
        r"\theta+(\xi-\alpha-\omega)_+",
        "transition_cross_gcd_lattice_audit",
        "### 4.49 Triple-gcd determinant-value reduction",
        r"d_ad_sd_w",
        r"(\xi-\alpha-\gamma-\omega)_+",
        "transition_triple_gcd_lattice_audit",
        "### 4.50 One final two-entry square-root theorem",
        r"2(1-\theta)+(1-\beta+\theta-\xi)+g",
        r"(\log T)^{-1/2}",
        "transition_final_two_entry_gate_audit",
        "### 4.51 Critical h-Poisson determinant line",
        r"wv-js=\delta",
        r"\det\begin{pmatrix}",
        "transition_h_poisson_line_audit",
        "### 4.52 Cross-determinant expansion of the critical slope square",
        r"\Delta=r_1s_2-r_2s_1",
        r"T^{1/2}",
        "transition_h_poisson_square_offdiagonal_audit",
        "### 4.53 Published Kloosterman bilinear bounds do not close the entry gate",
        r"\frac1{32}",
        r"\frac{15}{32}",
        "transition_published_kloosterman_entry_audit",
        "### 4.54 Exact two-dimensional Poisson formula for the critical shift lattice",
        r"\operatorname{covol}(B\mathbb Z^2)=|\Delta|",
        r"c_W(T):=\sum_{1\le d\le C_WT^{1/2}}\frac{\mu(d)}{d^2}",
        "transition_delta_lattice_poisson_audit",
        "### 4.55 Denominator-gcd extraction leaves one two-Möbius line-family gate",
        r"br_1-ar_2=h",
        r"\mu(ga)\mu(gb)=\mu(a)\mu(b)",
        r"\mathfrak Z_{q,k}(D,G)",
        "transition_denominator_gcd_line_audit",
        "### 4.56 Exact half-cutoff Type-I/II polytope inside the line-family gate",
        r"a=d_1e_1y_1",
        r"M_{\rm sign}=\pi_1+\beta_1+\pi_2+\beta_2",
        r"C_{\rm comp}",
        "transition_denominator_mobius_type_ii_audit",
        "### 4.57 Bourgain--Garaev multilinear Kloosterman audit at the balanced cell",
        r"\frac12-\frac1{16}=\frac7{16}",
        r"\frac12-\frac1{24}=\frac{11}{24}",
        r"N>p^{4/4^2}=p^{1/4}",
        r"\prod_{i=1}^n |I_i|>p^{1/2+\varepsilon}",
        r"n_{\rm formal}=8\ge7",
        "transition_bourgain_garaev_multilinear_audit",
        "### 4.58 Exact line Fourier window and the constant-phase microarc",
        r"\mathbf1_{br_1-ar_2=h}",
        r"|\alpha|\ll(AT)^{-1}",
        r"|M_U(A)M_V(T)|\ll T\sqrt A",
        "transition_line_fourier_microarc_audit",
        "### 4.59 Balanced Möbius convolution and the exact short-interval variance gate",
        r"c_{U,V}(n)",
        r"\frac1A\int_{\mathbb R}",
        r"\frac1{\zeta(s+i\tau)\zeta(s+i\upsilon)}",
        "transition_balanced_mobius_convolution_audit",
        "### 4.60 Exact coprimality layers and a bounded lifted-kernel nuclear norm",
        r"\omega_g(d_0,d_1,d_2)",
        r"1+\frac3{p^2}+\frac2{p^3}+\frac2{p^4}",
        r"(1+p^{-1})^2(1+p^{-2})",
        r"\tag{DCV\(_\gamma\)}",
        "transition_coprimality_layer_audit",
        "### 4.63 Exact Möbius--Hecke Euler factor and the reciprocal-\\(L\\) spectral gate",
        r"\frac{K_f(s)}{\zeta(2s)L(s,f)}",
        r"L(s+i\tau,f)L(s+i\upsilon,f)",
        "transition_mobius_hecke_reciprocal_l_audit",
        ):
        assert marker in text
