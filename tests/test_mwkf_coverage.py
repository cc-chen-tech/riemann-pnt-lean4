from fractions import Fraction as F
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


def test_large_q_critical_shift_closes_after_q_first_menon_transfer() -> None:
    """At lambda=2, q-first Euler factorization leaves one fixed f=mu*h."""
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
    assert audit.menon_shift_average_tends_to_zero
    assert audit.two_limit_tail_tends_to_zero
    assert audit.critical_shift_subface_covered
    assert not audit.above_critical_subface_covered
    assert audit.unconditional_coverage

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
        "shift_log=2 q_error=1/2 gcd_decay=2 menon=True "
        "fixed_zeta=True fixed_f=True two_limit=True covered=True "
        "above=False whole_cell=False"
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
        "### 4.26 Critical shift depth at fixed zeta scales via q-first Euler factorization",
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
        "critical_shift_subface_covered=True",
    ):
        assert marker in text
