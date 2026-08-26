import sys
from fractions import Fraction as F
from math import gcd
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
    assert audit.pascadi_uniform_saving_exponent == F(1, 700)
    assert audit.pascadi_uniform_deficit == F(349, 700)
    assert audit.pascadi_one_bounded_saving_exponent == F(1, 276)
    assert audit.pascadi_one_bounded_deficit == F(137, 276)
    assert audit.pascadi_factorable_saving_exponent == F(1, 12)
    assert audit.pascadi_factorable_deficit == F(5, 12)
    assert audit.pascadi_averaged_common_divisor_exponent == F(0)
    assert audit.pascadi_averaged_modulus_saving_exponent == F(0)
    assert audit.optimistic_four_bp_applications_saving_exponent == F(1, 8)
    assert audit.optimistic_four_bp_deficit == F(3, 8)
    assert audit.bp_square_root_length_condition_holds
    assert audit.bp_arbitrary_sequences_allowed
    assert not audit.standard_kloosterman_kernel_verified
    assert not audit.coefficients_separate_from_matrix_entries
    assert not audit.fixed_modulus_before_entry_sum_verified
    assert audit.pascadi_uniform_for_all_moduli
    assert audit.primitive_determinant_common_divisor_is_one
    assert not audit.pascadi_averaged_modulus_power_saving
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


def test_poisson_resonant_gram_isolates_the_only_positive_power_deficit() -> None:
    adapter = getattr(
        coverage_audit,
        "transition_poisson_resonant_gram_audit",
        None,
    )
    assert adapter is not None, "Poisson resonant-Gram audit is missing"

    audit = adapter()
    assert audit.discrete_identity_diagonal_exponent == F(2)
    assert audit.continuous_self_gram_exponent == F(2)
    assert audit.sampling_correction_bound_exponent == F(2)
    assert audit.sampling_correction_power_deficit == F(0)
    assert audit.continuous_full_gram_trivial_exponent == F(3)
    assert audit.square_function_target_exponent == F(2)
    assert audit.required_continuous_gram_saving_exponent == F(1)
    assert audit.poisson_covolume_cancels_jacobian
    assert audit.offdiagonal_zero_mode_is_sign_indefinite
    assert audit.resonant_recombination_exact
    assert audit.sampling_correction_has_no_positive_power_obstruction
    assert not audit.endpoint_logarithmic_aggregation_closed
    assert not audit.continuous_mobius_gram_bound_proved
    assert not audit.whole_poisson_zero_mode_covered


def test_resonant_gram_is_a_mobius_farey_microcluster_square_function() -> None:
    adapter = getattr(
        coverage_audit,
        "transition_poisson_tube_cluster_audit",
        None,
    )
    assert adapter is not None, "Poisson tube-cluster audit is missing"

    audit = adapter()
    assert audit.tube_longitudinal_length_exponent == F(1, 2)
    assert audit.tube_transverse_width_exponent == F(-1, 2)
    assert audit.angular_resolution_exponent == F(-1)
    assert audit.primitive_direction_family_exponent == F(2)
    assert audit.angular_cluster_count_exponent == F(1)
    assert audit.entries_per_cluster_exponent == F(1)
    assert audit.coherent_cluster_energy_exponent == F(3)
    assert audit.square_root_cluster_energy_exponent == F(2)
    assert audit.square_function_target_exponent == F(2)
    assert audit.square_root_margin_exponent == F(0)
    assert audit.cluster_coefficient == "mu(s)*mu(k*s+w)"
    assert audit.same_cluster_implies_determinant_collar
    assert audit.determinant_collar_implies_adjacent_clusters
    assert audit.angular_interaction_has_bounded_cluster_multiplicity
    assert audit.critical_sector_is_single_beatty_graph
    assert audit.primitive_mobius_product_fold_exact
    assert audit.vector_kernel_prevents_scalar_product_collapse
    assert audit.additive_fourier_interface_reappears_after_strip_transform
    assert not audit.additive_local_moment_input_is_unconditional
    assert audit.sector_character_parseval_exact
    assert audit.sector_principal_mode_absorbable
    assert audit.remaining_resonant_gate_has_only_nonzero_sector_characters
    assert audit.single_mobius_log_derivative_exact
    assert not audit.nonzero_character_automatic_frequency_decay
    assert audit.pre_cauchy_type_dispersion_required
    assert not audit.nonzero_character_type_bound_proved
    assert audit.requires_vector_valued_two_mobius_cancellation
    assert not audit.unweighted_farey_equidistribution_matches
    assert not audit.one_mobius_nilsequence_theorem_matches
    assert not audit.published_coverage


def test_farey_sector_partition_has_an_exact_determinant_collar_ledger() -> None:
    ledger = getattr(coverage_audit, "farey_sector_pair_ledger", None)
    assert ledger is not None, "exact Farey sector-pair ledger is missing"

    for q in range(1, 9):
        for s1 in range(1, 9):
            for s2 in range(1, 9):
                for w1 in range(0, 9):
                    for w2 in range(0, 9):
                        pair = ledger(q=q, w1=w1, s1=s1, w2=w2, s2=s2)
                        if pair.same_sector:
                            assert q * pair.absolute_determinant < s1 * s2
                        if q * pair.absolute_determinant < s1 * s2:
                            assert pair.sector_distance <= 1
                        assert pair.same_sector_implies_collar
                        assert pair.collar_implies_adjacent_sectors


def test_critical_farey_sector_fiber_is_a_single_beatty_graph() -> None:
    fiber = getattr(coverage_audit, "farey_sector_fiber_ledger", None)
    assert fiber is not None, "exact Farey sector-fiber ledger is missing"

    for q in range(1, 13):
        for b in range(0, 13):
            for s in range(1, q + 1):
                row = fiber(q=q, b=b, s=s)
                brute = tuple(
                    w
                    for w in range(0, (b + 2) * s + 2)
                    if b * s <= q * w < (b + 1) * s
                )
                assert row.members == brute
                assert row.member_count <= 1
                assert row.unique_when_s_at_most_q
                if row.members:
                    assert row.members == (row.beatty_candidate,)


def test_primitive_two_mobius_entry_folds_to_one_product_coordinate() -> None:
    fold = getattr(
        coverage_audit,
        "farey_primitive_product_coordinate_ledger",
        None,
    )
    assert fold is not None, "primitive product-coordinate ledger is missing"

    for q in range(1, 8):
        for k in range(1, 5):
            for s in range(1, 16):
                for r in range(k * s, (k + 3) * s + 1):
                    if gcd(r, s) != 1:
                        continue
                    row = fold(q=q, k=k, r=r, s=s)
                    assert row.primitive_entry
                    assert row.mobius_product_fold_exact
                    assert row.sector_product_inequality_exact
                    assert row.product_coordinate == r * s
                    assert row.second_entry_recovered_from_divisor == r


def test_banded_sector_gram_reduces_global_energy_to_cluster_square_function() -> None:
    sides = getattr(coverage_audit, "banded_sector_gram_sides", None)
    assert sides is not None, "finite banded sector-Gram helper is missing"

    result = sides(
        cluster_vectors={
            0: (F(1), F(1), F(0)),
            1: (F(0), F(2), F(1)),
            2: (F(0), F(0), F(3)),
        },
        bandwidth=1,
    )
    assert result["far_cluster_inner_products_vanish"]
    assert result["direct_global_energy"] == F(26)
    assert result["expanded_global_energy"] == F(26)
    assert result["cluster_square_function"] == F(16)
    assert result["bounded_overlap_constant"] == 3
    assert result["bounded_overlap_upper_bound"] == F(48)
    assert result["global_energy_bounded_by_cluster_square_function"]


def test_sector_character_parseval_splits_off_the_original_gram_over_m() -> None:
    sides = getattr(coverage_audit, "sector_character_parseval_sides", None)
    assert sides is not None, "finite sector-character Parseval helper is missing"

    result = sides(
        entries=(
            (0, F(1), (F(1),)),
            (0, F(2), (F(1),)),
            (2, F(3), (F(1),)),
        ),
        modulus=7,
    )
    assert result["no_sector_aliasing"]
    assert result["cluster_square_function"] == F(18)
    assert result["normalized_all_character_energy"] == F(18)
    assert result["finite_parseval_exact"]
    assert result["original_global_gram"] == F(36)
    assert result["principal_character_energy"] == F(36, 7)
    assert result["nonprincipal_character_energy"] == F(90, 7)
    assert result["nonprincipal_character_energy_nonnegative"]
    assert result["entry_self_diagonal_energy"] == F(14)
    assert result["nonprincipal_entry_diagonal_energy"] == F(12)
    assert result["nonprincipal_offdiagonal_energy"] == F(6, 7)
    assert result["nonprincipal_diagonal_split_exact"]
    assert result["sector_character_is_trivial_on_entry_diagonal"]


def test_sector_diagonal_recombines_outer_packets_with_one_original_entry_id() -> None:
    result = coverage_audit.sector_character_parseval_sides(
        entries=(
            (0, F(1), (F(1),)),
            (0, F(2), (F(1),)),
            (2, F(3), (F(1),)),
        ),
        modulus=7,
        original_entry_ids=("entry-0", "entry-0", "entry-2"),
    )
    assert result["original_entry_groups_recombined"]
    assert result["entry_self_diagonal_energy"] == F(18)
    assert result["nonprincipal_entry_diagonal_energy"] == F(108, 7)
    assert result["nonprincipal_offdiagonal_energy"] == -F(18, 7)
    assert result["nonprincipal_diagonal_split_exact"]


def test_sector_principal_mode_is_absorbed_into_the_original_gram() -> None:
    audit = getattr(coverage_audit, "sector_principal_absorption_audit", None)
    assert audit is not None, "sector-principal absorption audit is missing"

    result = audit(modulus=7, bandwidth=1)
    assert result["bounded_overlap_constant"] == 3
    assert result["principal_feedback_coefficient"] == F(3, 7)
    assert result["absorption_denominator"] == F(4, 7)
    assert result["exact_nonprincipal_multiplier"] == F(21, 4)
    assert result["twice_overlap_upper_multiplier"] == F(6)
    assert result["principal_mode_absorbable"]
    assert result["zero_sector_frequency_requires_separate_bound"] is False


def test_mobius_log_derivative_identity_is_exact_in_every_prime_coordinate() -> None:
    identity = getattr(
        coverage_audit,
        "mobius_log_derivative_prime_coordinate_identity",
        None,
    )
    assert identity is not None, "finite Möbius log-derivative helper is missing"

    for n in range(1, 151):
        result = identity(n=n)
        assert result["prime_coordinate_identity_exact"]
        assert result["left_prime_log_coefficients"] == result[
            "right_prime_log_coefficients"
        ]


def test_single_mobius_type_split_retains_the_exact_farey_entry() -> None:
    identity = getattr(
        coverage_audit,
        "farey_single_mobius_type_identity",
        None,
    )
    assert identity is not None, "Farey one-Möbius Type identity is missing"

    result = identity(q=11, b=14, k=2, s=7)
    assert result["sector_fiber_nonempty"]
    assert result["w"] == 9
    assert result["r"] == 23
    assert result["sector_membership_exact"]
    assert result["retained_first_mobius"] == -1
    assert result["prime_coordinate_identity_exact"]
    assert result["one_mobius_factor_only"]
    assert result["sector_character_label_retained"] == 14


def test_global_farey_type_packet_retains_every_sector_and_both_mobius_weights() -> None:
    partition = getattr(
        coverage_audit,
        "farey_global_mobius_type_partition",
        None,
    )
    assert partition is not None, "global Farey Type partition is missing"

    result = partition(
        q=5,
        k=1,
        sector_character=2,
        denominators=(3, 5),
        h=2,
        delta=-3,
        short_cutoff=2,
        packet_label="afe-plus",
    )

    assert result["primitive_entries"] == (
        (1, 3, 1, 4),
        (3, 3, 2, 5),
        (1, 5, 1, 6),
        (2, 5, 2, 7),
        (3, 5, 3, 8),
        (4, 5, 4, 9),
    )
    assert result["product_frequency"] == -6
    assert result["nonzero_sector_character_retained"]
    assert result["packet_label_retained"] == "afe-plus"
    assert result["all_sector_fibers_reassemble_primitive_wedge"]
    assert result["left_prime_coordinates"] == result[
        "right_prime_coordinates"
    ]
    assert result["global_log_identity_exact"]
    assert result["squarefree_left_prime_coordinates"] == result[
        "squarefree_right_prime_coordinates"
    ]
    assert result["squarefree_supported_global_identity_exact"]
    assert result["type_i_term_count"] == 10
    assert result["type_ii_term_count"] == 1
    assert result["all_type_terms_partitioned_without_remainder"]
    assert result["nonzero_mollifier_support_term_count"] == 4
    assert result["prime_power_is_prime_on_nonzero_mollifier_support"]

    type_ii = result["type_ii_terms"][0]
    assert type_ii == {
        "packet_label": "afe-plus",
        "sector_character": 2,
        "sector": 4,
        "denominator": 5,
        "shifted_numerator": 4,
        "numerator": 9,
        "type_divisor": 3,
        "prime_power": 3,
        "denominator_mobius": -1,
        "divisor_mobius": -1,
        "prime": 3,
        "h": 2,
        "delta": -3,
        "product_frequency": -6,
        "type_class": "II",
    }
    assert result["two_mobius_weights_retained_in_every_type_term"]
    assert not result["type_estimate_proved"]


def test_global_farey_type_scale_ledger_exposes_each_half_power_gate() -> None:
    ledger = getattr(
        coverage_audit,
        "farey_global_type_scale_ledger",
        None,
    )
    assert ledger is not None, "global Farey Type scale ledger is missing"

    result = ledger(numerator_exponent=F(1), cutoff_exponent=F(1, 3))
    assert result["type_i_short_factor_range"] == (F(0), F(1, 3))
    assert result["type_i_long_factor_range"] == (F(2, 3), F(1))
    assert result["type_ii_divisor_range"] == (F(1, 3), F(2, 3))
    assert result["type_ii_prime_range"] == (F(1, 3), F(2, 3))
    assert result["coherent_cluster_energy_exponent"] == F(3)
    assert result["square_function_target_exponent"] == F(2)
    assert result["required_energy_saving_exponent"] == F(1)
    assert result["required_unsquared_saving_exponent"] == F(1, 2)
    assert result["product_frequency_retained"] == "h*delta"
    assert result["two_mobius_weights_retained"] == "mu(s)*mu(d)"
    assert result["type_ii_prime_bearing_on_squarefree_support"]
    assert not result["type_i_bound_proved"]
    assert not result["type_ii_bound_proved"]
    assert not result["combined_gate_proved"]


def test_unit_divisor_type_i_reassembles_as_moving_weight_shifted_primes() -> None:
    reassemble = getattr(
        coverage_audit,
        "farey_type_i_unit_divisor_shifted_prime_reassembly",
        None,
    )
    assert reassemble is not None, "unit-divisor shifted-prime adapter is missing"

    result = reassemble(
        q=11,
        sector_character=3,
        denominators=tuple(range(2, 12)),
        h=2,
        delta=-3,
        packet_label="afe-plus",
    )

    assert result["unit_divisor_entries"] == (
        (5, 2, 1, 3, -1),
        (7, 3, 2, 5, -1),
        (4, 5, 2, 7, -1),
        (1, 6, 1, 7, 1),
        (9, 6, 5, 11, 1),
        (6, 7, 4, 11, -1),
        (9, 7, 6, 13, -1),
        (1, 10, 1, 11, 1),
        (3, 10, 3, 13, 1),
        (7, 10, 7, 17, 1),
        (9, 10, 9, 19, 1),
        (2, 11, 2, 13, -1),
        (6, 11, 6, 17, -1),
        (8, 11, 8, 19, -1),
    )
    assert result["shifted_prime_reassembly_exact"]
    assert result["prime_equals_denominator_plus_shift"]
    assert result["mobius_is_negative_prime_shift_exact"]
    assert result["product_frequency"] == -6
    assert result["packet_label_retained"] == "afe-plus"
    assert result["shift_one_sector_labels"] == (1, 5)
    assert result["sector_phase_varies_after_fixing_shift"]
    assert not result["lichtman_fixed_weight_hypothesis_matched"]


def test_lichtman_shifted_prime_bound_is_logarithmic_and_misses_type_i_gate() -> None:
    audit = getattr(
        coverage_audit,
        "lichtman_shifted_prime_type_i_coverage_audit",
        None,
    )
    assert audit is not None, "Lichtman Type-I coverage audit is missing"

    result = audit(
        prime_length_exponent=F(1),
        shift_length_exponent=F(1),
        required_unsquared_saving_exponent=F(1, 2),
    )

    assert result["published_average_norm"] == "L1 over shifts"
    assert result["required_average_norm"] == "vector cluster L2"
    assert result["published_saving_kind"] == "logarithmic"
    assert result["published_power_saving_exponent"] == F(0)
    assert result["remaining_power_deficit"] == F(1, 2)
    assert not result["strict_shift_range_h_less_x"]
    assert not result["fixed_weight_across_shifts"]
    assert not result["norm_hypothesis_matched"]
    assert not result["covers_type_i_gate"]


def test_nonzero_sector_character_has_no_automatic_frequency_decay() -> None:
    coefficients = getattr(
        coverage_audit,
        "sector_character_correlation_coefficients",
        None,
    )
    assert coefficients is not None, "sector-character correlation helper is missing"

    result = coefficients(
        cluster_vectors={
            0: (F(1), F(0), F(0)),
            1: (F(0), F(1), F(0)),
            2: (F(0), F(0), F(1)),
        }
    )
    assert result["correlation_coefficients"] == {0: F(3)}
    assert result["offzero_correlations_vanish"]
    assert result["character_energy_is_frequency_independent"]
    assert result["constant_character_energy"] == F(3)
    assert not result["nonzero_character_alone_supplies_saving"]


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


def test_bblr_h_first_completion_closes_the_hard_unsigned_error() -> None:
    adapter = getattr(
        coverage_audit,
        "transition_bblr_hard_h_completion_audit",
        None,
    )
    assert adapter is not None, "BBLR h-first completion audit is missing"

    bottom = adapter(poisson_gcd_exponent=F(0))
    assert bottom.reduced_h_length_exponent == F(1)
    assert bottom.reduced_modulus_exponent == F(1)
    assert bottom.h_length_matches_modulus
    assert bottom.nonzero_l_cutoff_exponent == F(0)
    assert not bottom.positive_power_gcd_shell_has_no_nonzero_l
    assert bottom.reduced_n1_count_exponent == F(1)
    assert bottom.completed_m1_h_exponent == F(1)
    assert bottom.poisson_integral_exponent == F(0)
    assert bottom.fixed_gcd_value_exponent == F(2)
    assert bottom.poisson_gcd_count_exponent == F(0)
    assert bottom.dyadic_layer_exponent == F(2)
    assert bottom.global_nonzero_frequency_exponent == F(2)
    assert bottom.target_exponent == F(2)
    assert bottom.power_margin == F(0)
    assert bottom.inverse_map_is_permutation_on_units
    assert bottom.multiplier_fibre_bound_is_gcd
    assert bottom.nonzero_frequency_error_closed_with_epsilon_loss
    assert not bottom.poisson_main_term_controlled
    assert not bottom.whole_unsigned_cell_covered

    positive = adapter(poisson_gcd_exponent=F(1, 3))
    assert positive.reduced_h_length_exponent == F(2, 3)
    assert positive.reduced_modulus_exponent == F(2, 3)
    assert positive.nonzero_l_cutoff_exponent == F(-1, 3)
    assert positive.positive_power_gcd_shell_has_no_nonzero_l
    assert positive.poisson_integral_exponent == F(1, 3)
    assert positive.fixed_gcd_value_exponent == F(5, 3)
    assert positive.poisson_gcd_count_exponent == F(1, 3)
    assert positive.dyadic_layer_exponent == F(2)


def test_bblr_h_completion_inverse_multiplier_fibres_are_gcd_bounded() -> None:
    helper = getattr(
        coverage_audit,
        "inverse_multiplier_unit_fibre_max",
        None,
    )
    assert helper is not None, "inverse multiplier fibre helper is missing"

    for modulus in range(2, 80):
        for multiplier in range(1, 16):
            assert helper(modulus, multiplier) <= gcd(modulus, multiplier)


def test_bblr_frequency_gcd_sum_has_an_exact_divisor_expansion() -> None:
    helper = getattr(
        coverage_audit,
        "frequency_gcd_sum_identity",
        None,
    )
    assert helper is not None, "frequency gcd-sum identity is missing"

    identity = helper(modulus=12, cutoff=10)
    assert identity.direct_gcd_sum == 27
    assert identity.divisor_totient_sum == 27
    assert identity.divisor_count == 6
    assert identity.linear_divisor_bound == 60
    assert identity.direct_gcd_sum <= identity.linear_divisor_bound


def test_bblr_h_completion_gives_an_exact_type_subcell_coverage_test() -> None:
    adapter = getattr(
        coverage_audit,
        "transition_bblr_h_completion_subcell_audit",
        None,
    )
    assert adapter is not None, "general BBLR h-completion audit is missing"

    unsigned = adapter(
        outer_a_exponent=F(0),
        outer_b_exponent=F(0),
        m1_exponent=F(1),
        m2_exponent=F(1),
        n1_exponent=F(1),
        n2_exponent=F(1),
        shift_exponent=F(1),
    )
    assert unsigned.left_side_product_exponent == F(2)
    assert unsigned.right_side_product_exponent == F(2)
    assert unsigned.x_product_exponent == F(1)
    assert unsigned.y_modulus_exponent == F(1)
    assert unsigned.x_over_y_excess_exponent == F(0)
    assert unsigned.h_or_modulus_exponent == F(1)
    assert unsigned.nonzero_l_base_cutoff_exponent == F(0)
    assert unsigned.summed_frequency_gcd_exponent == F(0)
    assert unsigned.chosen_orientation_hypothesis_verified
    assert not unsigned.nonzero_frequency_family_empty
    assert unsigned.global_nonzero_frequency_exponent == F(2)
    assert unsigned.target_exponent == F(2)
    assert unsigned.nonzero_frequency_cell_covered
    assert unsigned.outer_coefficients_may_be_arbitrary
    assert unsigned.factorization_multiplicity_is_divisor_bounded
    assert unsigned.frequency_gcd_average_is_divisor_bounded
    assert not unsigned.poisson_main_term_controlled
    assert not unsigned.whole_type_subcell_covered

    signed = adapter(
        outer_a_exponent=F(1),
        outer_b_exponent=F(1),
        m1_exponent=F(1, 2),
        m2_exponent=F(1, 2),
        n1_exponent=F(1, 2),
        n2_exponent=F(1, 2),
        shift_exponent=F(1),
    )
    assert signed.x_product_exponent == F(3, 2)
    assert signed.y_modulus_exponent == F(3, 2)
    assert signed.h_or_modulus_exponent == F(3, 2)
    assert signed.nonzero_l_base_cutoff_exponent == F(1)
    assert signed.summed_frequency_gcd_exponent == F(1)
    assert signed.chosen_orientation_hypothesis_verified
    assert signed.global_nonzero_frequency_exponent == F(3)
    assert signed.target_exponent == F(2)
    assert signed.power_margin == F(-1)
    assert not signed.nonzero_frequency_cell_covered

    empty = adapter(
        outer_a_exponent=F(0),
        outer_b_exponent=F(1),
        m1_exponent=F(1, 4),
        m2_exponent=F(7, 4),
        n1_exponent=F(1, 2),
        n2_exponent=F(1, 2),
        shift_exponent=F(1),
    )
    assert empty.nonzero_l_base_cutoff_exponent == F(-1, 4)
    assert empty.summed_frequency_gcd_exponent == F(0)
    assert empty.nonzero_frequency_family_empty
    assert not empty.chosen_orientation_hypothesis_verified
    assert not empty.nonzero_frequency_cell_covered


def test_bblr_zero_main_term_has_exactly_one_shift_length_gap() -> None:
    adapter = getattr(
        coverage_audit,
        "transition_bblr_zero_main_term_audit",
        None,
    )
    assert adapter is not None, "BBLR zero-main-term audit is missing"

    bottom = adapter(
        side_product_exponent=F(2),
        shift_exponent=F(1),
        poisson_gcd_exponent=F(0),
    )
    assert bottom.fixed_gcd_exponent == F(3)
    assert bottom.dyadic_gcd_layer_exponent == F(3)
    assert bottom.global_raw_main_term_exponent == F(3)
    assert bottom.target_exponent == F(2)
    assert bottom.power_margin == F(-1)
    assert bottom.missing_saving_exponent == F(1)
    assert bottom.main_term_is_independent_of_shift_orientation
    assert not bottom.shift_orientations_cancel_internally
    assert not bottom.registered_zero_master_identification_proved

    positive_gcd = adapter(
        side_product_exponent=F(2),
        shift_exponent=F(1),
        poisson_gcd_exponent=F(1, 3),
    )
    assert positive_gcd.fixed_gcd_exponent == F(7, 3)
    assert positive_gcd.dyadic_gcd_layer_exponent == F(8, 3)
    assert positive_gcd.global_raw_main_term_exponent == F(3)


def test_bblr_h_completion_uses_the_better_left_right_orientation() -> None:
    adapter = getattr(
        coverage_audit,
        "transition_bblr_symmetric_h_completion_audit",
        None,
    )
    assert adapter is not None, "symmetric BBLR h-completion audit is missing"

    reversed_boundary = adapter(
        outer_a_exponent=F(0),
        outer_b_exponent=F(1, 2),
        m1_exponent=F(1, 2),
        m2_exponent=F(1),
        n1_exponent=F(1, 2),
        n2_exponent=F(1, 2),
        shift_exponent=F(1, 2),
    )
    assert reversed_boundary.left_prefix_exponent == F(1, 2)
    assert reversed_boundary.right_prefix_exponent == F(1)
    assert reversed_boundary.smaller_prefix_exponent == F(1, 2)
    assert reversed_boundary.cutoff_hyperplane_excess == F(0)
    assert reversed_boundary.chosen_orientation == "right_to_left"
    assert reversed_boundary.symmetric_nonzero_frequency_exponent == F(3, 2)
    assert reversed_boundary.target_exponent == F(3, 2)
    assert reversed_boundary.nonzero_frequency_cell_covered

    supercritical = adapter(
        outer_a_exponent=F(1),
        outer_b_exponent=F(1),
        m1_exponent=F(1, 2),
        m2_exponent=F(1, 2),
        n1_exponent=F(1, 2),
        n2_exponent=F(1, 2),
        shift_exponent=F(1),
    )
    assert supercritical.cutoff_hyperplane_excess == F(1)
    assert supercritical.symmetric_nonzero_frequency_exponent == F(3)
    assert supercritical.target_exponent == F(2)
    assert not supercritical.nonzero_frequency_cell_covered


def test_bblr_phase_group_budget_locates_the_extra_half_power() -> None:
    adapter = getattr(
        coverage_audit,
        "transition_bblr_phase_group_saving_audit",
        None,
    )
    assert adapter is not None, "BBLR phase-group saving audit is missing"

    hard = adapter(
        side_product_exponent=F(2),
        shift_exponent=F(1),
        left_prefix_exponent=F(3, 2),
        right_prefix_exponent=F(3, 2),
    )
    assert hard.nonzero_l_range_exponent == F(1)
    assert hard.raw_nonzero_frequency_exponent == F(3)
    assert hard.target_exponent == F(2)
    assert hard.required_l_range_saving_exponent == F(1)
    assert hard.square_root_l_saving_exponent == F(1, 2)
    assert hard.remaining_after_square_root_exponent == F(1, 2)
    assert hard.signed_phase_class_cross_terms_required
    assert not hard.product_frequency_partition_is_sufficient
    assert not hard.required_phase_class_cancellation_proved


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


def test_recent_amplified_fourth_moments_do_not_cover_the_mobius_gate() -> None:
    """Require length, coefficient, and integrand compatibility simultaneously."""
    adapter = getattr(
        coverage_audit,
        "published_mobius_fourth_moment_coverage_audit",
        None,
    )
    assert adapter is not None, "published fourth-moment coverage audit is missing"

    audit = adapter(target_length_exponent=F(1))
    assert audit.target_length_exponent == F(1)
    assert audit.target_height_exponent == F(1)
    assert audit.target_normalized_moment_exponent == F(1)

    assert audit.bhsj_amplifier_length_ceiling == F(1, 8)
    assert audit.bhsj_length_power_deficit == F(7, 8)
    assert not audit.bhsj_length_hypothesis_met
    assert not audit.bhsj_mobius_coefficient_class_matches
    assert not audit.bhsj_pure_fourth_moment_integrand_matches
    assert not audit.bhsj_direct_coverage

    assert audit.verjovsky_polynomial_is_additive_fourier
    assert not audit.verjovsky_polynomial_is_multiplicative_dirichlet
    assert audit.verjovsky_local_arc_exponent == F(-1)
    assert audit.verjovsky_subpolynomial_moment_bound_equivalent_to_rh
    assert not audit.verjovsky_unconditional_coverage

    assert not audit.direct_published_coverage


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


def test_kim_2026_ternary_bound_is_too_weak_and_excludes_mobius() -> None:
    ledger = coverage_audit.transition_kim_ternary_correlation_audit(
        ambient_length_exponent=F(3),
        shift_length_exponent=F(2),
        target_exponent=F(9, 2),
    )

    assert ledger.relative_shift_exponent == F(2, 3)
    assert ledger.theorem_alpha_zero_shift_floor == F(1, 2)
    assert ledger.theorem_buffer_multiplier == 100
    assert ledger.theorem_epsilon_ceiling == F(1, 600)
    assert ledger.ambient_sum_exponent == F(5)
    assert ledger.required_saving_exponent == F(1, 2)
    assert ledger.theorem_saving_ceiling == F(1, 600)
    assert ledger.residual_power_deficit == F(299, 600)
    assert ledger.mobius_dirichlet_series_is_reciprocal_l
    assert not ledger.mobius_holomorphic_halfplane_hypothesis
    assert not ledger.mobius_critical_line_second_moment_hypothesis
    assert not ledger.dyadic_convolution_is_one_multiplicative_function
    assert not ledger.theorem_applies_to_actual_packet
    assert not ledger.whole_line_family_covered


def test_doyle_2026_length_enters_but_moment_and_coefficient_do_not() -> None:
    ledger = coverage_audit.transition_doyle_kfree_moment_audit(
        product_center_exponent=F(2),
        short_interval_exponent=F(1),
    )

    assert ledger.relative_interval_exponent == F(1, 2)
    assert ledger.k_two_middle_part_exponent == F(105, 317)
    assert ledger.mobius_l1_threshold_exponent == F(315, 634)
    assert ledger.length_margin_exponent == F(1, 317)
    assert ledger.theorem_is_l1_lower_bound
    assert not ledger.theorem_is_variance_upper_bound
    assert ledger.middle_coefficient_uses_square_divisors
    assert not ledger.middle_coefficient_matches_balanced_two_mobius_convolution
    assert not ledger.theorem_applies_to_actual_packet
    assert not ledger.whole_line_family_covered


def test_shi_2026_bessel_phase_transition_misses_the_degenerate_orbit() -> None:
    ledger = coverage_audit.transition_shi_bessel_kuznetsov_audit(
        first_fourier_index=0,
        second_fourier_index=-1,
    )

    assert ledger.exact_orbit_first_fourier_index == 0
    assert ledger.exact_orbit_second_fourier_index == -1
    assert ledger.bessel_argument_is_zero
    assert ledger.paper_requires_positive_dyadic_bessel_argument
    assert not ledger.paper_linear_twist_identified_in_actual_orbit
    assert not ledger.classical_nondegenerate_kuznetsov_adapter_verified
    assert not ledger.subcritical_rapid_decay_applies
    assert not ledger.whole_line_family_covered


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
        "large_q_transition: published_kloosterman_entry="
        "modulus=1,interval=1/2,required=1/2,"
        "bp=1/32,bp_deficit=15/32,mqw=1/100,mqw_deficit=49/100,"
        "pascadi_uniform=1/700,pascadi_uniform_deficit=349/700,"
        "pascadi_one_bounded=1/276,pascadi_one_bounded_deficit=137/276,"
        "pascadi_factorable=1/12,pascadi_factorable_deficit=5/12,"
        "pascadi_average_q=0,pascadi_average_save=0,four_bp=1/8,"
        "four_bp_deficit=3/8,sqrt_range=True,arbitrary=True,"
        "kernel=False,separable=False,fixed_modulus=False,"
        "pascadi_uniform=True,primitive_q_one=True,"
        "pascadi_average_power=False,covered=False"
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
        "large_q_transition: unit_divisor_shifted_prime="
        "entries=14,exact=True,shift_identity=True,"
        "shift_one_sectors=1,5,phase_varies=True,"
        "fixed_weight=False,proved=False"
    ) in output
    assert (
        "large_q_transition: lichtman_type_i="
        "norm=L1_over_shifts,required=vector_cluster_L2,"
        "log_sup=1/3,power=0,deficit=1/2,H_lt_X=False,"
        "fixed_weight=False,norm_match=False,covered=False"
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
        "### 2.1 Exact mutually exclusive coverage cells",
        r"s_{\rm BC}:=\min(s_1,s_2)>\frac1{1000}",
        "A_rho_ge_sigma",
        "B_ell_zero",
        "D_sigma_gt_rho",
        "positive but smaller than",
        "### 2.2 Exact residual Type-I/II routing",
        r"\mu(r)\mu(s)",
        r"e\!\left(-\frac{h\delta\bar r}{s}\right)",
        "residual_type_i_ii_ledger",
        "residual_coupled_type_certificate",
        "the two D cells remain uncovered",
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
        r"a_{\rm AFE}:=h\delta",
        r"\mathcal A_\xi:=\sum_b e(\xi b/M)S_b",
        r"\mathcal N_{\ne0}"
        r"=\left(1-\frac1M\right)D_{\rm cont}"
        r"+\mathcal N_{\ne0}^{\rm off}",
        "sector_character_is_trivial_on_entry_diagonal",
        r"\sum_{\xi\ne0}\|\mathcal A_\xi\|_2^2",
        "### 4.63 Exact Möbius--Hecke Euler factor and the reciprocal-\\(L\\) spectral gate",
        r"\frac{K_f(s)}{\zeta(2s)L(s,f)}",
        r"L(s+i\tau,f)L(s+i\upsilon,f)",
        "transition_mobius_hecke_reciprocal_l_audit",
        "### 4.69 Kim's 2026 ternary-correlation theorem enters the shift range",
        r"\frac{299}{600}",
        "transition_kim_ternary_correlation_audit",
        "### 4.70 Doyle's 2026 short k-free theorem crosses the length line",
        r"\frac12-\frac{315}{634}=\frac1{317}",
        "transition_doyle_kfree_moment_audit",
        "### 4.71 The 2026 Bessel-Kuznetsov phase transition misses",
        r"x_{\rm Bes}=0",
        "transition_shi_bessel_kuznetsov_audit",
        "### 4.72 Beatty two-point Chowla is qualitative and fixed-slope",
        "arXiv:2303.12574",
        r"\frac{\alpha_2}{\alpha_1}=k+\frac bQ\in\mathbb Q",
        "logarithmic limit, not a uniform power-saving estimate",
        "moving rational slope family",
        ):
        assert marker in text
