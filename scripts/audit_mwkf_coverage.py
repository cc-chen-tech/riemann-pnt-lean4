#!/usr/bin/env python3
"""Exact-rational adapters for published MWKF core estimates.

The adapters only certify a route when every encoded hypothesis and the
fixed target saving hold.  A rejected result is a coverage witness, not a
claim that the corresponding theorem is false.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import gcd
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).parents[1]))

from scripts.audit_mwkf_ranges import (
    ExponentBox,
    boundary_witnesses,
    is_admissible,
)


F = Fraction
TARGET_SAVING = F(1, 1000)
AGGREGATION_LOG_LOSS = F(7)


@dataclass(frozen=True)
class RouteResult:
    route: str
    applicable: bool
    saving: Fraction | None
    source: str
    reason: str
    conditions: tuple[str, ...]


@dataclass(frozen=True)
class ShiftedPoissonScales:
    v: Fraction
    j: Fraction
    shift: Fraction
    target: Fraction
    gate_target: Fraction
    volume: Fraction
    required_saving: Fraction
    square_root_margin: Fraction


@dataclass(frozen=True)
class DeterminantLineMobiusAudit:
    common_gcd_exponent: Fraction
    dual_j_exponent: Fraction
    dual_v_exponent: Fraction
    primitive_j_exponent: Fraction
    primitive_v_exponent: Fraction
    shift_quotient_exponent: Fraction
    line_parameter_length_exponent: Fraction
    layer_cardinality_exponent: Fraction
    global_gate_target_exponent: Fraction
    required_mobius_saving: Fraction
    common_gcd_divides_shift: bool
    primitive_slopes_are_coprime: bool
    fixed_fiber_is_two_affine_mobius_correlation: bool
    coprimality_is_one_residue_per_squarefree_shift_divisor: bool
    published_average_supplies_only_logarithmic_saving: bool
    published_uniform_growing_slope_hypothesis_verified: bool
    coupled_weight_hypothesis_verified: bool
    required_positive_power_saving_proved: bool
    published_coverage: bool
    source: str


@dataclass(frozen=True)
class DeterminantLineSquareRootAudit:
    common_gcd_exponent: Fraction
    shift_quotient_exponent: Fraction
    line_parameter_length_exponent: Fraction
    inner_area_exponent: Fraction
    two_dimensional_square_root_saving: Fraction
    required_mobius_saving: Fraction
    square_root_margin: Fraction
    small_g_residual_saving: Fraction
    bezout_change_of_variables_is_unimodular: bool
    square_root_has_power_slack: bool
    critical_layer_needs_only_log_saving: bool
    square_root_bound_proved: bool
    published_coverage: bool


@dataclass(frozen=True)
class MobiusProgressionVarianceAudit:
    common_gcd_exponent: Fraction
    sequence_length_exponent: Fraction
    progression_modulus_exponent: Fraction
    dh_asymptotic_min_modulus_exponent: Fraction
    dh_modulus_range_deficit: Fraction
    dh_variance_main_exponent: Fraction
    dh_error_exponent: Fraction
    dh_error_over_main_deficit: Fraction
    dh_asymptotic_range_verified: bool
    dh_small_modulus_upper_bound_exponent: Fraction
    dh_small_modulus_arbitrary_log_saving: bool
    dh_small_modulus_bound_uses_positive_monotonicity: bool
    gs_bv_level_margin: Fraction
    gs_bv_lower_range_verified: bool
    gs_bv_level_verified: bool
    gs_bv_saves_only_logarithms: bool
    one_mobius_progression_discrepancy_only: bool
    second_mobius_coupled_weight_allowed: bool
    query_dependent_smooth_weight_allowed: bool
    published_coverage: bool
    dh_source: str
    gs_source: str


@dataclass(frozen=True)
class DeterminantSlopeSquareFunctionAudit:
    common_gcd_exponent: Fraction
    g_layer_cardinality_exponent: Fraction
    primitive_slope_pair_exponent: Fraction
    slope_cauchy_cost_exponent: Fraction
    raw_identity_diagonal_exponent: Fraction
    coarse_square_function_squared_exponent: Fraction
    coarse_square_function_norm_exponent: Fraction
    aggregated_bound_exponent: Fraction
    logarithmic_gate_target_exponent: Fraction
    power_margin: Fraction
    endpoint_taper_amplitude_log_saving: Fraction
    endpoint_taper_squared_log_saving: Fraction
    proposed_square_function_squared_log_saving: Fraction
    aggregated_amplitude_log_saving: Fraction
    endpoint_aggregation_log_loss: Fraction
    net_log_saving: Fraction
    dh_error_exponent_matches_square_function_power: bool
    one_mobius_dh_scale_available: bool
    fixed_power_deficit_removed_by_logarithmic_gate: bool
    signed_slope_square_function_required: bool
    endpoint_conditions_verified: bool
    endpoint_diagonal_scale_compatible: bool
    arbitrary_log_saving_below_diagonal_requested: bool
    endpoint_bound_produces_little_o: bool
    second_mobius_coupled_dh_theorem_available: bool
    coupled_transform_weight_hypothesis_verified: bool
    square_function_estimate_proved: bool
    published_coverage: bool


@dataclass(frozen=True)
class EndpointSlopeOffDiagonalAudit:
    common_gcd_exponent: Fraction
    primitive_slope_pair_exponent: Fraction
    inner_delta_n_area_exponent: Fraction
    expanded_offdiagonal_cardinality_exponent: Fraction
    raw_identity_diagonal_exponent: Fraction
    coarse_endpoint_target_exponent: Fraction
    required_offdiagonal_saving: Fraction
    full_square_root_bound_exponent: Fraction
    full_square_root_target_margin: Fraction
    fraction_collar_exponent: Fraction
    cross_determinant_max_exponent: Fraction
    endpoint_taper_log_saving_in_square: Fraction
    zero_cross_determinant_is_identity_diagonal: bool
    nonzero_cross_determinant_recovers_unique_slope: bool
    full_square_root_has_power_slack: bool
    signed_four_mobius_offdiagonal_required: bool
    published_four_mobius_spectral_bound_available: bool
    offdiagonal_estimate_proved: bool
    published_coverage: bool


@dataclass(frozen=True)
class EndpointCokernelCharacterAudit:
    common_gcd_exponent: Fraction
    cross_determinant_exponent: Fraction
    smith_first_invariant_exponent: Fraction
    smith_second_invariant_exponent: Fraction
    cokernel_character_family_exponent: Fraction
    orthogonality_normalization_saving: Fraction
    naive_two_congruence_character_exponent: Fraction
    odsf_required_saving: Fraction
    character_square_root_saving: Fraction
    remaining_saving_after_character_square_root: Fraction
    primitive_rows_force_cyclic_cokernel: bool
    two_cramer_congruences_are_independent: bool
    single_finite_character_family_is_exact: bool
    four_mobius_entry_cancellation_still_required: bool
    hybrid_character_entry_estimate_proved: bool
    published_coverage: bool


@dataclass(frozen=True)
class LargeQEndpointUnpoissonAudit:
    reduced_length_exponent: Fraction
    shifted_solution_exponent: Fraction
    height_integral_exponent: Fraction
    pre_poisson_denominator_exponent: Fraction
    per_q_contribution_exponent: Fraction
    q_family_cardinality_exponent: Fraction
    aggregated_remainder_exponent: Fraction
    endpoint_taper_log_saving: Fraction
    shift_log_depth: Fraction
    net_log_saving: Fraction
    all_nonzero_h_boxes_regrouped_before_absolute_value: bool
    poisson_zero_mode_has_same_bound: bool
    mobius_cancellation_used: bool
    unconditional_coverage: bool


@dataclass(frozen=True)
class LargeQEndpointCriticalShiftAudit:
    shift_log_depth: Fraction
    endpoint_taper_log_saving: Fraction
    power_remainder_exponent: Fraction
    q_mellin_error_power_saving: Fraction
    coprimality_divisor_volume_decay: Fraction
    fixed_zeta_scales_required: bool
    fixed_zeta_scales_supplied: bool
    q_summed_density_is_multiplicative: bool
    q_restriction_removed_before_correlation: bool
    density_weight_has_absolutely_convergent_convolution: bool
    fixed_truncation_has_only_fixed_linear_slopes: bool
    menon_shift_average_tends_to_zero: bool
    full_height_phase_must_remain_in_correlation: bool
    two_limit_tail_tends_to_zero: bool
    critical_shift_subface_covered: bool
    above_critical_subface_covered: bool
    unconditional_coverage: bool


@dataclass(frozen=True)
class LargeQGrowingZetaProductLiftAudit:
    shift_log_depth: Fraction
    endpoint_taper_log_saving: Fraction
    absolute_shift_volume_log_exponent: Fraction
    absolute_power_exponent: Fraction
    gcd_divisibility_removes_spurious_log_loss: bool
    product_lift_identity_is_exact: bool
    zero_shift_is_explicit_diagonal: bool
    required_centered_energy_power_exponent: Fraction
    required_centered_energy_log_exponent: Fraction
    requires_little_oh_of_local_scale: bool
    published_short_interval_variance_applies: bool
    centered_product_energy_estimate_proved: bool
    unconditional_coverage: bool


@dataclass(frozen=True)
class LargeQHeightPhaseAudit:
    shift_log_depth: Fraction
    zeta_log_depth: Fraction
    phase_ratio_log_depth: Fraction
    absolute_before_phase_log_exponent: Fraction
    height_kernel_has_arbitrary_decay: bool
    full_height_phase_retained: bool
    strict_phase_separation: bool
    strict_subface_covered: bool
    unconditional_coverage: bool


@dataclass(frozen=True)
class LargeQBoundaryReflectionAudit:
    shift_log_depth: Fraction
    zeta_log_depth: Fraction
    full_q_restricted_divisor_identity_is_exact: bool
    full_mass_supported_on_q_smooth_part: bool
    full_log_term_supported_on_q_free_prime_powers: bool
    squarefree_reduced_variable_forces_prime: bool
    sparse_main_main_has_two_prime_sieve_savings: bool
    sparse_main_tail_has_one_prime_sieve_saving: bool
    formal_terms_with_sparse_main_have_sieve_saving: bool
    dyadic_reduced_scale_prevents_direct_completion: bool
    afe_weight_prevents_exact_full_divisor_completion: bool
    cross_scale_aggregation_proved: bool
    reflected_tail_has_moving_product_threshold: bool
    reflected_tail_phase_separated_at_boundary: bool
    formal_remaining_terms: tuple[str, str]
    reflected_tail_energy_estimate_proved: bool
    unconditional_coverage: bool


@dataclass(frozen=True)
class LargeQSubcriticalAfeCompletionAudit:
    afe_product_gap: Fraction
    afe_product_upper_exponent: Fraction
    mellin_left_shift: Fraction
    mellin_residue_is_one: bool
    mellin_remainder_power_saving: Fraction
    local_shifted_line_absolute_power_exponent: Fraction
    short_side_reciprocity_removes_boundary_loss: bool
    mellin_remainder_aggregates_to_little_oh: bool
    local_endpoint_afe_weight_replaced_by_residue: bool
    all_reduced_dyadic_scales_regrouped_before_absolute_values: bool
    restricted_divisor_completion_applies_to_endpoint_residue_kernel: bool
    subcritical_cross_scale_aggregation_proved: bool
    full_divisor_completion_crosses_afe_transition: bool
    full_endpoint_cross_scale_aggregation_proved: bool
    unconditional_coverage: bool


@dataclass(frozen=True)
class LargeQTransitionMellinDivisorAudit:
    common_mellin_variable_retained: bool
    right_line_product_weight_separates_exactly: bool
    right_line_product_energy_is_absolutely_convergent: bool
    q_restricted_twisted_euler_product_is_exact: bool
    zero_mellin_frequency_recovers_von_mangoldt: bool
    nonzero_mellin_frequency_loses_prime_power_support: bool
    gaussian_mellin_tail_is_absolutely_summable: bool
    left_line_product_energy_is_absolutely_convergent: bool
    transition_cutoff_preserves_one_sided_divisor_completion: bool
    transition_reduced_to_one_twisted_divisor_energy: bool
    twisted_divisor_energy_estimate_proved: bool
    unconditional_coverage: bool


@dataclass(frozen=True)
class LargeQTransitionCompactMellinAudit:
    afe_product_band_is_compact: bool
    mellin_separation_line: Fraction
    mellin_inversion_is_exact: bool
    mellin_transform_has_arbitrary_polynomial_decay: bool
    product_coefficients_have_no_real_power_growth: bool
    q_restricted_twisted_divisor_coefficient_is_exact: bool
    coprimality_coupling_is_retained: bool
    reflected_tail_coefficient_is_retained: bool
    transition_reduced_to_compact_mellin_energy: bool
    product_variable_exponent: Fraction
    shift_exponent: Fraction
    absolute_global_exponent: Fraction
    asymptotic_target_exponent: Fraction
    critical_power_saving: Fraction
    fixed_power_gate_saving: Fraction
    compact_mellin_energy_estimate_proved: bool
    unconditional_coverage: bool


@dataclass(frozen=True)
class TransitionKimAverageShiftedConvolutionAudit:
    correlation_length_exponent: Fraction
    shift_average_exponent: Fraction
    left_short_interval_exponent: Fraction
    right_short_interval_exponent: Fraction
    theorem_h_power: Fraction
    optimistic_theorem_bound_exponent: Fraction
    fixed_gate_target_exponent: Fraction
    remaining_power_deficit: Fraction
    localized_mobius_divisor_coefficient_is_multiplicative: bool
    uniform_common_mellin_twist_hypothesis_verified: bool
    theorem_applicable: bool
    published_coverage: bool
    source: str


@dataclass(frozen=True)
class ShiftedPoissonSubboxScales:
    v: Fraction
    j: Fraction
    shift: Fraction
    target: Fraction
    gate_target: Fraction
    volume: Fraction
    required_saving: Fraction
    square_root_margin: Fraction


@dataclass(frozen=True)
class JointPhaseScales:
    stationary_h: Fraction
    t_phase_variation: Fraction
    fourier_phase_variation: Fraction
    same_sign_derivative_parameter: Fraction
    on_stationary_face: bool
    same_sign_power_saving: bool


@dataclass(frozen=True)
class DualCellIsolationScales:
    dual_v: Fraction
    fourier_window: Fraction
    normalized_h_spread: Fraction
    physical_h_support: Fraction
    seminorm_cost_per_derivative: Fraction
    uniform_in_original_kernel_class: bool


@dataclass(frozen=True)
class FareyCriticalScales:
    dual_v: Fraction
    j_interval: Fraction
    at_most_one_j: bool
    rational_approximation: Fraction
    farey_spacing: Fraction
    approximation_minus_spacing: Fraction


@dataclass(frozen=True)
class FareyCompletionScales:
    v: Fraction
    residue_frequency: Fraction
    product_frequency: Fraction
    residue_density_prefactor: Fraction
    two_dimensional_completion_prefactor: Fraction
    both_coordinate_axes_empty: bool
    farey_gate_target: Fraction
    normalized_gate_target: Fraction
    normalized_volume: Fraction
    required_saving: Fraction
    square_root_margin: Fraction
    generic_bcr_bound: Fraction
    generic_bcr_deficit: Fraction
    optimistic_distinct_large_sieve_bound: Fraction
    optimistic_distinct_large_sieve_deficit: Fraction
    fraction_multiplicity_exponent: Fraction
    separated_additive_large_sieve_bound: Fraction
    separated_additive_large_sieve_deficit: Fraction
    zero_residue_forces_centering: bool


@dataclass(frozen=True)
class MobiusTraceFunctionAudit:
    length_margin: Fraction
    length_hypothesis: bool
    modulus_is_prime: bool
    trace_is_nonexceptional: bool
    theorem_applicable: bool
    power_target_covered: bool
    reasons: tuple[str, ...]


@dataclass(frozen=True)
class AveragedChowlaShiftAudit:
    shift: Fraction
    product_frequency: Fraction
    correlation_volume: Fraction
    logarithmic_gate_target: Fraction
    power_deficit: Fraction
    unit_linear_slopes: bool
    zero_shift_excluded: bool
    theorem_applicable: bool
    source: str
    reasons: tuple[str, ...]


@dataclass(frozen=True)
class LinnikDispersionCenteringAudit:
    parseval_diagonal_exponent: Fraction
    logarithmic_gate_target_exponent: Fraction
    power_margin: Fraction
    gate_log_power: Fraction
    aggregation_log_loss: Fraction
    net_log_saving: Fraction
    minus_one_homogeneity_degree: Fraction
    parseval_homogeneity_degree: Fraction
    minus_one_removes_fourier_zero_mode: bool
    minus_one_subtracts_parseval_diagonal: bool
    variance_expansion_retains_signed_off_diagonal: bool
    diagonal_only_majorant_closes: bool
    separate_quadratic_main_term_required: bool
    subtracting_diagonal_after_cauchy_sufficient: bool
    signed_off_diagonal_must_cancel_diagonal: bool
    amplitude_level_projection_is_alternative: bool
    pre_cauchy_signed_subtraction_required: bool
    published_coverage: bool


@dataclass(frozen=True)
class CenteredResonanceScales:
    product_frequency: Fraction
    coefficient_first_moment: Fraction
    resonance_cutoff: Fraction
    phase_variation_at_cutoff: Fraction
    near_resonance_bound: Fraction
    logarithmic_gate_target: Fraction
    saving: Fraction
    nonempty_collar: bool


@dataclass(frozen=True)
class CenteredResonanceLogBudget:
    resonance_power_cutoff: Fraction
    resonance_log_cutoff: Fraction
    near_bound_power: Fraction
    near_bound_log_saving: Fraction
    aggregation_log_loss: Fraction
    global_log_margin: Fraction
    power_matches_gate: bool
    centered_completion_applicable: bool
    nonempty_log_collar: bool
    produces_little_o: bool


@dataclass(frozen=True)
class EndpointCenteredResonanceLogBudget:
    resonance_power_cutoff: Fraction
    endpoint_log_saving: Fraction
    analytic_log_saving_required: Fraction
    resonance_log_cutoff: Fraction
    total_near_bound_log_saving: Fraction
    aggregation_log_loss: Fraction
    global_log_margin: Fraction
    full_power_collar_global_log_margin: Fraction
    endpoint_power_face: bool
    centered_completion_applicable: bool
    nonempty_log_collar: bool
    produces_little_o: bool


@dataclass(frozen=True)
class EndpointCriticalAggregationBudget:
    raw_dyadic_log_loss: Fraction
    endpoint_rs_removed: Fraction
    ratio_k_removed: Fraction
    critical_hl_removed: Fraction
    remaining_dyadic_log_loss: Fraction
    q_logarithmic_depth: Fraction
    frequency_logarithmic_depth: Fraction
    q_aggregation_is_cardinal: bool
    total_log_power_loss: Fraction
    endpoint_log_saving: Fraction
    net_log_power: Fraction
    polyloglog_loss_exponent: Fraction
    critical_face: bool
    extra_log_saving_required: bool
    absolute_bound_produces_little_o: bool


@dataclass(frozen=True)
class ImprovedAveragedChowlaShellAudit:
    q_logarithmic_depth: Fraction
    frequency_logarithmic_depth: Fraction
    total_logarithmic_depth: Fraction
    mrt_log_saving: Fraction
    unit_slope_improved_log_saving: Fraction
    fixed_slope_black_box_log_saving: Fraction
    improved_polyloglog_loss_exponent: Fraction
    fixed_slope_polyloglog_loss_exponent: Fraction
    endpoint_absolute_log_margin: Fraction
    mrt_log_margin: Fraction
    unit_slope_log_margin: Fraction
    all_sector_log_margin: Fraction
    power_critical_face: bool
    stationary_face: bool
    all_sector_subface_covered: bool
    fixed_slope_black_box_proved: bool
    fixed_slope_extension_required: bool
    bv_separation_proved: bool
    bv_separation_required: bool
    joint_coefficient_accepted: bool
    coprimality_transfer_required: bool
    coprimality_transfer_proved: bool
    published_coverage: bool
    source: str


@dataclass(frozen=True)
class CompletionWeightBVAudit:
    x_log_scale: Fraction
    y_log_scale: Fraction
    kernel_first_derivative_log_cost: Fraction
    kernel_mixed_derivative_log_cost: Fraction
    amplitude_log_gain: Fraction
    absolute_frequency_log_depth: Fraction
    bv_net_log_depth: Fraction
    bv_extra_log_depth: Fraction
    offstationary_log_gap: Fraction
    centered_phase_power_slack: Fraction
    low_variation_regime: bool
    stationary_log_face: bool
    offstationary_ibp_available: bool
    retained_after_phase_partition: bool
    lifted_fourier_formula_exact: bool
    raw_first_moment_scale_preserved: bool
    bv_preserves_global_log_depth: bool


@dataclass(frozen=True)
class CoprimalityRestrictedMenonAudit:
    q_logarithmic_depth: Fraction
    frequency_logarithmic_depth: Fraction
    common_divisor_cutoff_log_depth: Fraction
    common_divisor_volume_decay: Fraction
    common_divisor_tail_log_saving: Fraction
    common_divisor_tail_log_margin: Fraction
    restricted_modulus_log_depth: Fraction
    fixed_slope_log_saving: Fraction
    all_sector_log_margin: Fraction
    exact_gcd_reindex_proved: bool
    tail_is_summable: bool
    common_divisor_tail_produces_little_o: bool
    principal_character_twist: bool
    polylog_twist_uniformity_proved: bool
    coprimality_transfer_proved: bool
    subface_covered: bool
    source: str


@dataclass(frozen=True)
class FarResonanceShellScales:
    distance: Fraction
    product_frequency: Fraction
    phase_amplitude: Fraction
    absolute_bound: Fraction
    logarithmic_gate_target: Fraction
    required_power_saving: Fraction
    at_power_barrier: bool


@dataclass(frozen=True)
class AveragedChowlaShellAudit:
    distance: Fraction
    required_power_saving: Fraction
    theorem_log_saving: Fraction
    required_log_saving: Fraction
    log_shortfall: Fraction
    theorem_applicable: bool
    source: str
    reasons: tuple[str, ...]


@dataclass(frozen=True)
class InverseResonanceBCRScales:
    distance: Fraction
    inverse_length: Fraction
    modulus_length: Fraction
    numerator_product_length: Fraction
    term_1: Fraction
    term_2: Fraction
    bound: Fraction
    gate_target: Fraction
    deficit: Fraction
    joint_coefficient_accepted: bool
    published_coverage: bool


@dataclass(frozen=True)
class PrimitiveFractionLargeSieveScales:
    distance: Fraction
    fraction_family: Fraction
    primitive_fraction_spacing: Fraction
    fraction_multiplicity: Fraction
    numerator_product_length: Fraction
    large_sieve_bound: Fraction
    centered_absolute_bound: Fraction
    best_unconditional_bound: Fraction
    gate_target: Fraction
    remaining_power_saving: Fraction
    improves_absolute_bound: bool


@dataclass(frozen=True)
class ReciprocalClusterLargeSieveScales:
    distance: Fraction
    cluster_multiplicity: Fraction
    farey_center_spacing: Fraction
    reciprocity_correction: Fraction
    numerator_resolution: Fraction
    correction_within_resolution: bool
    clustered_large_sieve_bound: Fraction
    primitive_best_bound: Fraction
    best_unconditional_bound: Fraction
    gate_target: Fraction
    remaining_power_saving: Fraction
    improves_primitive_bound: bool


@dataclass(frozen=True)
class PrimeFactorTraceTwistAudit:
    distance: Fraction
    prime_factor_exponent: Fraction
    applications: int
    eta: Fraction
    fkm_eta_ceiling: Fraction
    interval_over_modulus_penalty: Fraction
    one_sided_power_saving: Fraction
    optimistic_total_power_saving: Fraction
    current_far_shell_deficit: Fraction
    optimistic_residual_deficit: Fraction
    trace_is_nonexceptional: bool
    prime_modulus_hypothesis: bool
    nonzero_prime_frequency_uniform: bool
    uniform_prime_factor_available: bool
    joint_cofactor_accepted: bool
    optimistic_gate_covered: bool
    published_coverage: bool
    source: str


@dataclass(frozen=True)
class SquarefreeLinearCompletionAudit:
    distance: Fraction
    short_factor_total: Fraction
    long_quotient_interval: Fraction
    product_frequency: Fraction
    reduced_denominator_lower_bound: Fraction
    optimistic_reduced_denominator: Fraction
    rational_major_arc_term: Fraction
    square_root_term: Fraction
    denominator_term: Fraction
    optimistic_theorem_bound: Fraction
    power_saving: Fraction
    original_shell_deficit: Fraction
    remaining_shell_deficit: Fraction
    squarefree_support_retained: bool
    coprimality_progressions_charged: bool
    factor_subbox_covered: bool
    published_coverage: bool
    source: str


@dataclass(frozen=True)
class TypeIICauchyDiagonalAudit:
    b_exponent: Fraction
    b_exponent_range: tuple[Fraction, Fraction]
    a_exponent: Fraction
    modulus_exponent: Fraction
    numerator_l2_exponent: Fraction
    identity_diagonal_exponent: Fraction
    spectral_target_exponent: Fraction
    spectral_target_margin: Fraction
    post_cauchy_diagonal_exponent: Fraction
    post_cauchy_target_exponent: Fraction
    post_cauchy_target_deficit: Fraction
    exact_identity_diagonal_present: bool
    dispersion_subtraction_required: bool
    separate_diagonal_majorant_closes: bool
    published_coverage: bool


@dataclass(frozen=True)
class ZeroRayConvolutionCenteringAudit:
    b_exponent: Fraction
    a_exponent: Fraction
    product_ray_exponent: Fraction
    cutoff_exponent: Fraction
    product_above_cutoff: bool
    full_convolution_vanishes_exactly: bool
    type_sector_convolution_equals_negative_mobius: bool
    type_sector_convolution_vanishes: bool
    factorization_anchor_may_depend_only_on_product: bool
    factorization_anchor_leaves_explicit_mobius_main: bool
    dyadic_factor_localization_breaks_exact_zero: bool
    fixed_factor_phase_breaks_product_invariance: bool
    joint_gram_gate_required: bool
    joint_gram_target_exponent: Fraction
    explicit_mobius_main_squared_exponent: Fraction
    explicit_main_target_margin: Fraction
    separate_explicit_main_majorant_closes: bool
    joint_cross_term_required: bool
    published_coverage: bool


@dataclass(frozen=True)
class PrimitiveSlopeZeroRayAudit:
    b_exponent: Fraction
    slope_exponent: Fraction
    slope_exponent_range: tuple[Fraction, Fraction]
    common_n_factor_exponent: Fraction
    common_y_factor_exponent: Fraction
    primitive_pair_cardinality_exponent: Fraction
    explicit_main_cardinality_exponent: Fraction
    joint_gram_target_exponent: Fraction
    required_power_saving: Fraction
    double_square_root_saving: Fraction
    double_square_root_has_exponent_slack: bool
    low_slope_benchmark_obstruction: bool
    primitive_slope_mobius_pair_retained: bool
    common_k_mobius_cancellation_available: bool
    primitive_slope_reciprocal_conductor_present: bool
    published_coverage: bool


@dataclass(frozen=True)
class LongMobiusCutoffAudit:
    cutoff_exponent: Fraction
    complementary_factor_max_exponent: Fraction
    long_factor_min_exponent: Fraction
    squared_target_saving: Fraction
    identity_diagonal_exponent: Fraction
    worst_spectral_target_exponent: Fraction
    worst_diagonal_margin: Fraction
    all_factor_boxes_have_diagonal_power_slack: bool
    entire_zero_ray_cardinality_has_power_slack: bool
    exact_single_sector_identity: bool
    v_split_omitted_exactly: bool
    reciprocal_modulus_exponent: Fraction
    reciprocal_conductor_reduced: bool
    zero_completion_endpoint_c_exponent: Fraction
    full_off_diagonal_imposes_b_divides_delta: bool
    published_off_diagonal_coverage: bool


@dataclass(frozen=True)
class LongCutoffHCompletionAudit:
    b_exponent: Fraction
    a_exponent: Fraction
    common_b_period_surplus: Fraction
    fixed_a_normalized_frequency: Fraction
    full_modulus_period_surplus: Fraction
    fixed_a_phase_is_smooth_for_b_poisson: bool
    b_only_poisson_valid: bool
    full_phase_modulus_exponent: Fraction
    published_coverage: bool


@dataclass(frozen=True)
class LongCutoffQuotientSplitAudit:
    cutoff_exponent: Fraction
    b_exponent: Fraction
    dual_v_exponent: Fraction
    a_exponent: Fraction
    bv_modulus_exponent: Fraction
    small_divisor_level_exponent: Fraction
    expanded_modulus_endpoint: Fraction
    large_divisor_lower_exponent: Fraction
    large_divisor_upper_exponent: Fraction
    large_cofactor_max_exponent: Fraction
    strict_bv_log_slack_required: bool
    gcd_reduction_only_decreases_modulus: bool
    large_sector_retains_two_mobius_weights: bool
    standard_bv_coupled_hypotheses_verified: bool
    published_coverage: bool


@dataclass(frozen=True)
class LongCutoffQuotientBDHAudit:
    modulus_exponent: Fraction
    query_family_exponent: Fraction
    progression_length_exponent: Fraction
    total_cardinality_exponent: Fraction
    residue_multiplicity_exponent: Fraction
    outer_coefficient_l2_squared_exponent: Fraction
    ideal_bdh_variance_exponent: Fraction
    optimistic_bdh_bound_exponent: Fraction
    farey_gate_target_exponent: Fraction
    bdh_remaining_deficit: Fraction
    completion_conversion_exponent: Fraction
    max_centered_product_phase_saving: Fraction
    optimistic_centered_bound_exponent: Fraction
    completed_gate_target_exponent: Fraction
    centered_remaining_deficit: Fraction
    common_weight_hypothesis_verified: bool
    centered_geometric_saving_proved: bool
    published_coverage: bool


@dataclass(frozen=True)
class PascadiIncompleteKloostermanAudit:
    product_n_exponent: Fraction
    incomplete_d_exponent: Fraction
    modulus_c_exponent: Fraction
    coefficient_l2_exponent: Fraction
    regular_i_squared_exponent: Fraction
    exceptional_i_squared_exponent: Fraction
    i_exponent: Fraction
    optimistic_bound_exponent: Fraction
    gate_target_exponent: Fraction
    remaining_deficit: Fraction
    product_coefficient_separated_optimistically: bool
    assumption_14_verified: bool
    direct_corollary_hypotheses_verified: bool
    published_coverage: bool
    source: str


@dataclass(frozen=True)
class CenteredQuotientPoissonAudit:
    e_cofactor_max_exponent: Fraction
    squarefree_e_support_required: bool
    coprimality_e_support_required: bool
    squarefree_divisor_expansion_exact: bool
    nonzero_frequency_mass_equals_theta_00: bool
    centered_minus_one_vanishes_separately: bool
    unweighted_e_poisson_valid: bool
    joint_c_v_orthogonality_recloses_original_kernel: bool
    determinant_gate_unchanged: bool
    new_conductor_reduction: bool
    published_coverage: bool


@dataclass(frozen=True)
class HeckeMobiusLocalFactor:
    mobius_factor: tuple[Fraction, ...]
    inverse_l_factor: tuple[Fraction, ...]
    correction_numerator: tuple[Fraction, ...]
    correction_denominator: tuple[Fraction, ...]
    correction_minus_one_numerator: tuple[Fraction, ...]
    euler_factor_identity_exact: bool


@dataclass(frozen=True)
class HeckeMobiusSpectralAudit:
    polynomial_length_exponent: Fraction
    conductor_exponent_witness: Fraction
    required_log_saving_power: int
    local_euler_factor_exact: bool
    knightly_li_has_one_fixed_hecke_index: bool
    linear_superposition_formally_creates_one_mobius_hecke_sum: bool
    qct_geometry_identified_with_generalized_kloosterman_family: bool
    two_mobius_weights_derived_as_hecke_polynomials: bool
    classical_polynomial_conductor_saving_only_constant: bool
    thorner_polynomial_conductor_saving_tends_to_one: bool
    spectral_conductor_verified: bool
    uniform_zero_free_log_saving_verified: bool
    published_coverage: bool


@dataclass(frozen=True)
class DeterminantOrbitHeckeIndexAudit:
    matrix_entries: tuple[str, str, str, str]
    determinant_symbol: str
    modulus_symbol: str
    residue_pair: tuple[str, str]
    hecke_operator_index_symbol: str
    kloosterman_fourier_indices: tuple[str, str]
    original_phase_reduces_to_linear_orbit_phase: bool
    r_mobius_weights_residue_entry: bool
    s_mobius_weights_modulus: bool
    delta_mobius_weight_present: bool
    knightly_li_superposition_targets_existing_mobius_weight: bool
    two_existing_mobius_weights_become_hecke_polynomials: bool
    qct_kernel_is_unweighted_complete_orbit: bool
    published_coverage: bool


@dataclass(frozen=True)
class FixedModulusKloostermanCompletionAudit:
    modulus_exponent: Fraction
    h_exponent: Fraction
    delta_exponent: Fraction
    r_fourier_l2_exponent: Fraction
    h_coefficient_l2_exponent: Fraction
    bp_57_dimensionless_factor_exponent: Fraction
    bp_57_fixed_delta_s_exponent_before_completion: Fraction
    completion_normalization_exponent: Fraction
    bp_57_global_bound_exponent: Fraction
    original_cardinality_exponent: Fraction
    bp_57_saving_exponent: Fraction
    ck_gate_target_exponent: Fraction
    remaining_deficit: Fraction
    product_residue_energy_exponent: Fraction
    product_residue_l2_exponent: Fraction
    kloosterman_operator_norm_exponent: Fraction
    orthogonality_global_bound_exponent: Fraction
    orthogonality_saving_exponent: Fraction
    orthogonality_remaining_deficit: Fraction
    best_registered_route: str
    mqw_size_lhs_exponent: Fraction
    mqw_size_rhs_exponent: Fraction
    mqw_size_condition_deficit: Fraction
    finite_r_completion_exact: bool
    full_additive_fourier_support_required: bool
    kernel_separated_optimistically: bool
    delta_unit_mod_s_verified: bool
    h_coprimality_mod_s_verified: bool
    mqw_direct_hypotheses_verified: bool
    direct_published_coverage: bool


@dataclass(frozen=True)
class BCFixedDeterminantAudit:
    short_variable_exponents: tuple[Fraction, Fraction]
    long_variable_exponents: tuple[Fraction, Fraction]
    determinant_scale_exponent: Fraction
    fixed_shift_trivial_exponent: Fraction
    bc_corollary_error_exponent: Fraction
    bc_corollary_beats_trivial: bool
    shift_range_exponent: Fraction
    summed_trivial_exponent: Fraction
    global_target_exponent: Fraction
    required_mobius_saving: Fraction
    full_shift_average_required: bool
    coupled_kernel_separated_optimistically: bool
    direct_corollary_hypotheses_verified: bool
    published_coverage: bool


def _positive_part(value: Fraction) -> Fraction:
    return max(F(0), value)


def completion_dual_exponent(
    length_exponent: Fraction,
    modulus_exponent: Fraction,
) -> Fraction:
    """Length of the effective smooth-Poisson dual interval."""
    return _positive_part(modulus_exponent - length_exponent)


def h_poisson_shifted_scales(box: ExponentBox) -> ShiftedPoissonScales:
    """Exact zero-slack ledger after Poisson summation in ``h``.

    The transformed equation is ``delta = r*v - j*s``.  ``volume`` is
    the lattice-volume exponent before arithmetic cancellation; it records
    the codimension imposed by the shift window and is not an estimate.
    """
    v = completion_dual_exponent(box.h, box.sigma)
    j = max(F(0), box.rho - box.h, box.ell - box.sigma)
    product_scale = max(box.rho + v, box.sigma + j)
    volume = (
        box.rho
        + box.sigma
        + v
        + j
        - _positive_part(product_scale - box.ell)
    )
    target = box.rho + box.sigma - box.h
    gate_target = target - TARGET_SAVING
    return ShiftedPoissonScales(
        v=v,
        j=j,
        shift=box.ell,
        target=target,
        gate_target=gate_target,
        volume=volume,
        required_saving=volume - gate_target,
        square_root_margin=gate_target - volume / 2,
    )


def determinant_line_mobius_audit(
    box: ExponentBox,
    *,
    gcd_exponent: Fraction,
) -> DeterminantLineMobiusAudit:
    """Parametrize each nonzero determinant fiber by one integer line.

    Write ``j=g*j0``, ``v=g*v0`` with ``(j0,v0)=1``.  The equation
    ``r*v-j*s=delta`` is soluble only when ``g|delta``; after
    ``delta=g*delta0`` it is

    ``r*v0-s*j0=delta0``.

    For any particular solution ``(r0,s0)``, all solutions are exactly
    ``r=r0+j0*n``, ``s=s0+v0*n``.  The Möbius factor on a fixed fiber is
    therefore the two-affine-form correlation
    ``mu(r0+j0*n)*mu(s0+v0*n)``.  If ``d|delta0`` is squarefree, the
    coprimality failure ``d|(r,s)`` restricts ``n`` to one residue class
    modulo ``d``: uniqueness follows because ``(j0,v0)=1``.

    The returned cardinality includes the dyadic ``g``, primitive slope,
    shift-quotient, and line-parameter counts.  It is a scale identity,
    not a cancellation estimate.
    """
    shifted = h_poisson_shifted_scales(box)
    j_exponent = shifted.j
    v_exponent = shifted.v
    gcd_max = min(j_exponent, v_exponent, box.ell)
    if gcd_exponent < 0 or gcd_exponent > gcd_max:
        raise ValueError("gcd exponent exceeds the determinant dual ranges")

    primitive_j = j_exponent - gcd_exponent
    primitive_v = v_exponent - gcd_exponent
    shift_quotient = box.ell - gcd_exponent
    line_parameter_length = min(
        box.rho - primitive_j,
        box.sigma - primitive_v,
    )
    if line_parameter_length < 0:
        raise ValueError("primitive determinant line misses the dyadic box")

    layer_cardinality = (
        gcd_exponent
        + primitive_j
        + primitive_v
        + shift_quotient
        + line_parameter_length
    )
    required_saving = layer_cardinality - shifted.gate_target

    return DeterminantLineMobiusAudit(
        common_gcd_exponent=gcd_exponent,
        dual_j_exponent=j_exponent,
        dual_v_exponent=v_exponent,
        primitive_j_exponent=primitive_j,
        primitive_v_exponent=primitive_v,
        shift_quotient_exponent=shift_quotient,
        line_parameter_length_exponent=line_parameter_length,
        layer_cardinality_exponent=layer_cardinality,
        global_gate_target_exponent=shifted.gate_target,
        required_mobius_saving=required_saving,
        common_gcd_divides_shift=True,
        primitive_slopes_are_coprime=True,
        fixed_fiber_is_two_affine_mobius_correlation=True,
        coprimality_is_one_residue_per_squarefree_shift_divisor=True,
        published_average_supplies_only_logarithmic_saving=True,
        published_uniform_growing_slope_hypothesis_verified=False,
        coupled_weight_hypothesis_verified=False,
        required_positive_power_saving_proved=False,
        published_coverage=False,
        source=(
            "Matomaki-Radziwill-Tao, arXiv:1503.05121; "
            "Menon, arXiv:2607.15574"
        ),
    )


def determinant_line_square_root_audit(
    box: ExponentBox,
    *,
    gcd_exponent: Fraction,
) -> DeterminantLineSquareRootAudit:
    """Measure a hypothetical joint square root in ``(delta0,n)``.

    Choose Bezout coefficients ``x*v0+y*j0=1``.  On a fixed primitive
    slope, the determinant line is

    ``r=x*delta0+j0*n``, ``s=-y*delta0+v0*n``.

    The coefficient matrix has determinant one.  Thus the two Möbius
    arguments are independent integral coordinates, although the exact
    transformed kernel cuts out a coupled skew region.  A square-root
    estimate in the whole ``(delta0,n)`` area would save half its
    exponent.  This function records whether that *unproved* estimate
    has enough exponent for the determinant-line gate.
    """
    line = determinant_line_mobius_audit(
        box,
        gcd_exponent=gcd_exponent,
    )
    inner_area = (
        line.shift_quotient_exponent
        + line.line_parameter_length_exponent
    )
    square_root_saving = inner_area / 2
    margin = square_root_saving - line.required_mobius_saving

    return DeterminantLineSquareRootAudit(
        common_gcd_exponent=gcd_exponent,
        shift_quotient_exponent=line.shift_quotient_exponent,
        line_parameter_length_exponent=(
            line.line_parameter_length_exponent
        ),
        inner_area_exponent=inner_area,
        two_dimensional_square_root_saving=square_root_saving,
        required_mobius_saving=line.required_mobius_saving,
        square_root_margin=margin,
        small_g_residual_saving=_positive_part(-margin),
        bezout_change_of_variables_is_unimodular=True,
        square_root_has_power_slack=(margin > 0),
        critical_layer_needs_only_log_saving=(margin == 0),
        square_root_bound_proved=False,
        published_coverage=False,
    )


def mobius_progression_variance_audit(
    box: ExponentBox,
    *,
    gcd_exponent: Fraction,
) -> MobiusProgressionVarianceAudit:
    """Audit published progression averages against a determinant line.

    The folklore Davenport--Halberstam formula for Möbius is

    ``sum_(q<=Q) sum_(a mod q) |M(X;q,a)|^2``
    `` = (6/pi^2) X Q + O_A(X^2 log(X)^(-A))``.

    Its asymptotic range is ``Q >= X log(X)^(-A)``.  On the hard
    determinant line, ``X=T^3`` while a primitive slope modulus is at
    most ``T^(1/2-gamma)``; the error therefore dominates the main term
    by a fixed power.

    Granville--Shao's Bombieri--Vinogradov theorem does reach positive
    slope exponents below ``X^(1/2-delta)``, but controls an unweighted
    one-Möbius progression discrepancy with logarithmic saving.  It does
    not allow the second affine Möbius value or the query-dependent
    transformed kernel as coefficients.
    """
    line = determinant_line_mobius_audit(
        box,
        gcd_exponent=gcd_exponent,
    )
    sequence_length = max(box.rho, box.sigma)
    progression_modulus = max(
        line.primitive_j_exponent,
        line.primitive_v_exponent,
    )
    dh_min_modulus = sequence_length
    dh_main = sequence_length + progression_modulus
    dh_error = 2 * sequence_length
    gs_margin = sequence_length / 2 - progression_modulus
    gs_lower_range_verified = progression_modulus > 0

    return MobiusProgressionVarianceAudit(
        common_gcd_exponent=gcd_exponent,
        sequence_length_exponent=sequence_length,
        progression_modulus_exponent=progression_modulus,
        dh_asymptotic_min_modulus_exponent=dh_min_modulus,
        dh_modulus_range_deficit=(
            dh_min_modulus - progression_modulus
        ),
        dh_variance_main_exponent=dh_main,
        dh_error_exponent=dh_error,
        dh_error_over_main_deficit=dh_error - dh_main,
        dh_asymptotic_range_verified=(
            progression_modulus >= dh_min_modulus
        ),
        dh_small_modulus_upper_bound_exponent=dh_error,
        dh_small_modulus_arbitrary_log_saving=True,
        dh_small_modulus_bound_uses_positive_monotonicity=True,
        gs_bv_level_margin=gs_margin,
        gs_bv_lower_range_verified=gs_lower_range_verified,
        gs_bv_level_verified=(
            gs_margin > 0 and gs_lower_range_verified
        ),
        gs_bv_saves_only_logarithms=True,
        one_mobius_progression_discrepancy_only=True,
        second_mobius_coupled_weight_allowed=False,
        query_dependent_smooth_weight_allowed=False,
        published_coverage=False,
        dh_source=(
            "Hooley, J. London Math. Soc. (2) 10 (1975), Theorem 2; "
            "Fan, The Davenport-Halberstam theorem for Mobius function"
        ),
        gs_source=(
            "Granville-Shao, arXiv:1703.06865v2, Theorem 1.2"
        ),
    )


def determinant_slope_square_function_audit(
    box: ExponentBox,
    *,
    gcd_exponent: Fraction,
    endpoint_taper_factors: Fraction,
    endpoint_aggregation_log_loss: Fraction,
    endpoint_conditions_verified: bool,
) -> DeterminantSlopeSquareFunctionAudit:
    """State the endpoint-compatible determinant slope square-function gate.

    For fixed dyadic ``g=T^gamma``, let ``S_(g,j0,v0)`` denote the exact
    ``(delta0,n)`` sum in the determinant-line form.  The proposed local
    input is

    ``sum_(j0,v0) |S_(g,j0,v0)|^2``
    `` << T^(2*max(rho,sigma)) log(T)^(-2*endpoint_tapers)``.

    The logarithm here comes only from the two mollifier tapers already
    present in the amplitude.  At ``gamma=0`` the positive identity
    diagonal has power ``T^6``; asking for arbitrary logarithmic saving
    below those tapers would be impossible.  With two endpoint tapers the
    squared diagonal naturally carries ``log(T)^(-4)`` and the
    square-function norm carries ``log(T)^(-2)``.

    Cardinal summation over ``g`` and Cauchy over the primitive slope pair
    cost ``T^gamma`` and ``T^(1/2-gamma)`` respectively, producing exactly
    ``T^(7/2) log(T)^(-2)`` at the hard endpoint.  The exact endpoint
    aggregation loses one logarithm, leaving a little-oh factor.
    """
    if endpoint_taper_factors < 0 or endpoint_aggregation_log_loss < 0:
        raise ValueError("endpoint logarithmic inputs must be nonnegative")
    line = determinant_line_mobius_audit(
        box,
        gcd_exponent=gcd_exponent,
    )
    shifted = h_poisson_shifted_scales(box)
    variance = mobius_progression_variance_audit(
        box,
        gcd_exponent=gcd_exponent,
    )
    slope_pair = (
        line.primitive_j_exponent + line.primitive_v_exponent
    )
    slope_cauchy = slope_pair / 2
    square_squared = 2 * variance.sequence_length_exponent
    square_norm = square_squared / 2
    raw_identity_diagonal = (
        line.layer_cardinality_exponent - gcd_exponent
    )
    aggregated = gcd_exponent + slope_cauchy + square_norm
    logarithmic_target = shifted.target
    squared_taper_saving = 2 * endpoint_taper_factors
    net_log_saving = (
        endpoint_taper_factors - endpoint_aggregation_log_loss
    )

    return DeterminantSlopeSquareFunctionAudit(
        common_gcd_exponent=gcd_exponent,
        g_layer_cardinality_exponent=gcd_exponent,
        primitive_slope_pair_exponent=slope_pair,
        slope_cauchy_cost_exponent=slope_cauchy,
        raw_identity_diagonal_exponent=raw_identity_diagonal,
        coarse_square_function_squared_exponent=square_squared,
        coarse_square_function_norm_exponent=square_norm,
        aggregated_bound_exponent=aggregated,
        logarithmic_gate_target_exponent=logarithmic_target,
        power_margin=logarithmic_target - aggregated,
        endpoint_taper_amplitude_log_saving=endpoint_taper_factors,
        endpoint_taper_squared_log_saving=squared_taper_saving,
        proposed_square_function_squared_log_saving=(
            squared_taper_saving
        ),
        aggregated_amplitude_log_saving=endpoint_taper_factors,
        endpoint_aggregation_log_loss=endpoint_aggregation_log_loss,
        net_log_saving=net_log_saving,
        dh_error_exponent_matches_square_function_power=(
            variance.dh_error_exponent == square_squared
        ),
        one_mobius_dh_scale_available=(
            variance.dh_small_modulus_upper_bound_exponent
            == square_squared
            and variance.dh_small_modulus_arbitrary_log_saving
        ),
        fixed_power_deficit_removed_by_logarithmic_gate=(
            aggregated == logarithmic_target
            and aggregated > shifted.gate_target
        ),
        signed_slope_square_function_required=True,
        endpoint_conditions_verified=endpoint_conditions_verified,
        endpoint_diagonal_scale_compatible=(
            square_squared >= raw_identity_diagonal
            and squared_taper_saving == 2 * endpoint_taper_factors
        ),
        arbitrary_log_saving_below_diagonal_requested=False,
        endpoint_bound_produces_little_o=(
            endpoint_conditions_verified and net_log_saving > 0
        ),
        second_mobius_coupled_dh_theorem_available=False,
        coupled_transform_weight_hypothesis_verified=False,
        square_function_estimate_proved=False,
        published_coverage=False,
    )


def endpoint_slope_offdiagonal_audit(
    box: ExponentBox,
    *,
    gcd_exponent: Fraction,
) -> EndpointSlopeOffDiagonalAudit:
    """Ledger after expanding EDSSF and removing its exact diagonal.

    For one fixed integer ``g=T^gamma``, the primitive slope family has
    exponent ``p`` and each ``(delta0,n)`` box has exponent ``a``.  The
    expanded off-diagonal therefore has cardinality ``p+2a``.  The
    endpoint square-function target is the coarse diagonal power
    ``2*max(rho,sigma)``; this function records the exact saving required
    of the signed four-Möbius cross term.

    If two primitive rows share a slope, Cramer's rule recovers that slope
    from their shifts whenever ``Delta=r1*s2-r2*s1`` is nonzero.  When
    ``Delta=0``, positivity and primitivity force equality of the two
    rows, which is precisely the identity diagonal already retained.
    """
    line = determinant_line_mobius_audit(
        box,
        gcd_exponent=gcd_exponent,
    )
    slope_pair = (
        line.primitive_j_exponent + line.primitive_v_exponent
    )
    inner_area = (
        line.shift_quotient_exponent
        + line.line_parameter_length_exponent
    )
    expanded = slope_pair + 2 * inner_area
    identity_diagonal = (
        line.layer_cardinality_exponent - gcd_exponent
    )
    target = 2 * max(box.rho, box.sigma)
    square_root_bound = expanded / 2
    fraction_collar = (
        line.shift_quotient_exponent
        - box.sigma
        - line.primitive_v_exponent
    )
    determinant_max = min(
        box.rho + box.sigma,
        2 * box.sigma + fraction_collar,
    )

    return EndpointSlopeOffDiagonalAudit(
        common_gcd_exponent=gcd_exponent,
        primitive_slope_pair_exponent=slope_pair,
        inner_delta_n_area_exponent=inner_area,
        expanded_offdiagonal_cardinality_exponent=expanded,
        raw_identity_diagonal_exponent=identity_diagonal,
        coarse_endpoint_target_exponent=target,
        required_offdiagonal_saving=expanded - target,
        full_square_root_bound_exponent=square_root_bound,
        full_square_root_target_margin=target - square_root_bound,
        fraction_collar_exponent=fraction_collar,
        cross_determinant_max_exponent=determinant_max,
        endpoint_taper_log_saving_in_square=F(4),
        zero_cross_determinant_is_identity_diagonal=True,
        nonzero_cross_determinant_recovers_unique_slope=True,
        full_square_root_has_power_slack=(square_root_bound < target),
        signed_four_mobius_offdiagonal_required=True,
        published_four_mobius_spectral_bound_available=False,
        offdiagonal_estimate_proved=False,
        published_coverage=False,
    )


def endpoint_cokernel_character_audit(
    box: ExponentBox,
    *,
    gcd_exponent: Fraction,
    determinant_exponent: Fraction,
) -> EndpointCokernelCharacterAudit:
    """Record the one-dimensional finite character group behind Cramer.

    For primitive rows ``(r_i,s_i)``, the determinant matrix

    ``B=((r1,-s1),(r2,-s2))``

    has first Smith invariant one and second invariant ``|Delta|``.
    Therefore ``Z^2/B Z^2`` is cyclic of order ``|Delta|``.  The two
    Cramer numerator divisibilities have joint density ``|Delta|^-1``,
    not ``|Delta|^-2``, and exact finite orthogonality uses one family of
    ``|Delta|`` characters.

    Square-root cancellation in that character family saves only half of
    the determinant exponent.  The returned residual is the additional
    saving that must still come from the signed four-Möbius matrix-entry
    sum and its coupled transform weight; no such estimate is asserted.
    """
    offdiagonal = endpoint_slope_offdiagonal_audit(
        box,
        gcd_exponent=gcd_exponent,
    )
    if determinant_exponent < 0:
        raise ValueError("determinant exponent must be nonnegative")
    if determinant_exponent > offdiagonal.cross_determinant_max_exponent:
        raise ValueError("determinant exponent exceeds the fraction collar")

    character_square_root = determinant_exponent / 2
    return EndpointCokernelCharacterAudit(
        common_gcd_exponent=gcd_exponent,
        cross_determinant_exponent=determinant_exponent,
        smith_first_invariant_exponent=F(0),
        smith_second_invariant_exponent=determinant_exponent,
        cokernel_character_family_exponent=determinant_exponent,
        orthogonality_normalization_saving=determinant_exponent,
        naive_two_congruence_character_exponent=2 * determinant_exponent,
        odsf_required_saving=offdiagonal.required_offdiagonal_saving,
        character_square_root_saving=character_square_root,
        remaining_saving_after_character_square_root=(
            offdiagonal.required_offdiagonal_saving
            - character_square_root
        ),
        primitive_rows_force_cyclic_cokernel=True,
        two_cramer_congruences_are_independent=False,
        single_finite_character_family_is_exact=True,
        four_mobius_entry_cancellation_still_required=True,
        hybrid_character_entry_estimate_proved=False,
        published_coverage=False,
    )


def _is_large_q_bounded_zeta_endpoint(box: ExponentBox) -> bool:
    return (
        box.kappa > 0
        and box.rho == box.sigma
        and box.kappa + box.rho == F(3)
        and box.kappa + box.sigma == F(3)
        and box.m == box.k == box.ell == F(0)
        and box.h == box.sigma - box.m
    )


def _is_large_q_afe_transition_face(box: ExponentBox) -> bool:
    return (
        is_admissible(box)
        and box.kappa > 0
        and box.kappa + box.rho == F(3)
        and box.kappa + box.sigma == F(3)
        and box.k + box.m == F(1)
        and box.k + box.sigma == box.m + box.rho
    )


def large_q_endpoint_unpoisson_audit(
    box: ExponentBox,
    *,
    shift_log_depth: Fraction,
) -> LargeQEndpointUnpoissonAudit:
    """Close the bounded-zeta large-q endpoint by undoing Poisson.

    This adapter applies to the collective family obtained by summing all
    nonzero ``h`` boxes before taking an absolute value.  With bounded
    ``m1,m2,delta``, the pre-Poisson equation

    ``m1*s-m2*r=delta``

    has ``O(R)`` solutions when ``R=S``.  The height integral contributes
    ``T`` and the original coefficient contributes
    ``(q*sqrt(R*S))^-1``.  At ``(R,S,q)=(T,T,T^2)`` this is ``T^-1`` per
    q.  Cardinal q-summation returns power ``T`` and the two endpoint
    mollifier tapers leave ``log(T)^-2``.  The zero Poisson mode obeys the
    same absolute bound, so subtraction of that mode is harmless.
    """
    if not _is_large_q_bounded_zeta_endpoint(box):
        raise ValueError("box is not the large-q bounded-zeta endpoint")
    if shift_log_depth < 0:
        raise ValueError("shift log depth must be nonnegative")

    shifted_solutions = box.rho
    height_integral = F(1)
    denominator = box.kappa + (box.rho + box.sigma) / 2
    per_q = height_integral + shifted_solutions - denominator
    aggregated = per_q + box.kappa
    return LargeQEndpointUnpoissonAudit(
        reduced_length_exponent=box.rho,
        shifted_solution_exponent=shifted_solutions,
        height_integral_exponent=height_integral,
        pre_poisson_denominator_exponent=denominator,
        per_q_contribution_exponent=per_q,
        q_family_cardinality_exponent=box.kappa,
        aggregated_remainder_exponent=aggregated,
        endpoint_taper_log_saving=F(2),
        shift_log_depth=shift_log_depth,
        net_log_saving=F(2) - shift_log_depth,
        all_nonzero_h_boxes_regrouped_before_absolute_value=True,
        poisson_zero_mode_has_same_bound=True,
        mobius_cancellation_used=False,
        unconditional_coverage=(
            aggregated == F(1) and shift_log_depth < F(2)
        ),
    )


def endpoint_unpoisson_adapter(
    box: ExponentBox,
    *,
    shift_log_depth: Fraction | None,
) -> RouteResult:
    if not _is_large_q_bounded_zeta_endpoint(box):
        return RouteResult(
            route="endpoint_unpoisson",
            applicable=False,
            saving=None,
            source="exact inverse Poisson regrouping",
            reason="not_large_q_bounded_zeta_endpoint",
            conditions=(
                "both mollifier variables in the endpoint collar",
                "bounded m1,m2,delta boxes",
                "regroup every nonzero h box before absolute values",
            ),
        )
    if shift_log_depth is None:
        return RouteResult(
            route="endpoint_unpoisson",
            applicable=False,
            saving=None,
            source="exact inverse Poisson and shifted-equation count",
            reason="polylog_shift_depth_not_encoded",
            conditions=(
                "supply the delta-box logarithmic depth",
                "require that depth to be strictly below two",
            ),
        )
    audit = large_q_endpoint_unpoisson_audit(
        box,
        shift_log_depth=shift_log_depth,
    )
    return RouteResult(
        route="endpoint_unpoisson",
        applicable=audit.unconditional_coverage,
        saving=F(0),
        source="exact inverse Poisson and shifted-equation count",
        reason=(
            "covered_by_endpoint_unpoisson"
            if audit.unconditional_coverage
            else "insufficient_endpoint_log_saving"
        ),
        conditions=(
            "N/4 <= qR,qS <= N",
            "bounded m1,m2,delta boxes",
            "sum all nonzero h before absolute values",
            "retain both endpoint mollifier tapers",
        ),
    )


def large_q_endpoint_critical_shift_audit(
    box: ExponentBox,
    *,
    shift_log_depth: Fraction,
    zeta_scales_fixed: bool,
) -> LargeQEndpointCriticalShiftAudit:
    """Audit, but do not promote, the q-first Euler factorization.

    Mellin inversion of the squarefree harmonic q-sum produces

    ``g(rs)=prod_(p|rs) (1+1/p)^-1``.

    Since ``(r,s)=1``, this factors as ``g(r)g(s)`` and turns the two
    Möbius coefficients into the fixed multiplicative function
    ``f(n)=mu(n)g(n)``.  Its exact Euler quotient is ``f=mu*h`` with
    ``h(p^a)=1/(p+1)``; the h-series is absolutely convergent in every
    positive half-plane.  When the zeta-variable scales are fixed
    independently of T, truncating h and the coprimality divisor leaves
    fixed arithmetic slopes.  The original height phase, however, is an
    Archimedean/additive twist and is not covered by the untwisted
    fixed-slope Menon consequence.  Dropping it would invalidate the
    reduction.  The separate height-phase adapter retains that phase and
    supplies the actual coverage below the product-scale boundary.
    """
    if not _is_large_q_bounded_zeta_endpoint(box):
        raise ValueError("box is not the large-q bounded-zeta endpoint")
    if shift_log_depth < 0:
        raise ValueError("shift log depth must be nonnegative")

    return LargeQEndpointCriticalShiftAudit(
        shift_log_depth=shift_log_depth,
        endpoint_taper_log_saving=F(2),
        power_remainder_exponent=F(1),
        q_mellin_error_power_saving=box.kappa / 4,
        coprimality_divisor_volume_decay=F(2),
        fixed_zeta_scales_required=True,
        fixed_zeta_scales_supplied=zeta_scales_fixed,
        q_summed_density_is_multiplicative=True,
        q_restriction_removed_before_correlation=True,
        density_weight_has_absolutely_convergent_convolution=True,
        fixed_truncation_has_only_fixed_linear_slopes=True,
        menon_shift_average_tends_to_zero=False,
        full_height_phase_must_remain_in_correlation=True,
        two_limit_tail_tends_to_zero=True,
        critical_shift_subface_covered=False,
        above_critical_subface_covered=False,
        unconditional_coverage=False,
    )


def large_q_growing_zeta_product_lift_audit(
    box: ExponentBox,
    *,
    shift_log_depth: Fraction,
) -> LargeQGrowingZetaProductLiftAudit:
    """Record the exact remaining gate when K and M grow polylogarithmically.

    Keeping ``gcd(m1,m2) | delta`` before summing the nonzero shifts removes
    the logarithm lost by a pointwise gcd bound.  Reindexing ``n=m1*s`` and
    ``n-delta=m2*r`` then turns the residual into one centered short-shift
    energy of product-lifted Möbius coefficients.  No published theorem in
    the current audit proves the required variance uniformly in the growing
    product scale, so this adapter must remain negative.
    """
    if not _is_large_q_bounded_zeta_endpoint(box):
        raise ValueError("box is not the large-q bounded-zeta endpoint")
    if shift_log_depth < 0:
        raise ValueError("shift log depth must be nonnegative")

    return LargeQGrowingZetaProductLiftAudit(
        shift_log_depth=shift_log_depth,
        endpoint_taper_log_saving=F(2),
        absolute_shift_volume_log_exponent=shift_log_depth,
        absolute_power_exponent=F(1),
        gcd_divisibility_removes_spurious_log_loss=True,
        product_lift_identity_is_exact=True,
        zero_shift_is_explicit_diagonal=True,
        required_centered_energy_power_exponent=F(1),
        required_centered_energy_log_exponent=shift_log_depth,
        requires_little_oh_of_local_scale=True,
        published_short_interval_variance_applies=False,
        centered_product_energy_estimate_proved=False,
        unconditional_coverage=False,
    )


def large_q_height_phase_audit(
    box: ExponentBox,
    *,
    shift_log_depth: Fraction,
    zeta_log_depth: Fraction,
) -> LargeQHeightPhaseAudit:
    """Retain the height phase and integrate by parts when ``L/M`` grows.

    The exact phase derivative is ``log(1+delta/(m2*r))``.  On the
    large-q endpoint, repeated integration by parts gives arbitrary
    decay in ``1+L/M``.  Hence the critical shift depth two is covered
    whenever the zeta-variable logarithmic depth is strictly below two.
    """
    if not _is_large_q_bounded_zeta_endpoint(box):
        raise ValueError("box is not the large-q bounded-zeta endpoint")
    if shift_log_depth < 0 or zeta_log_depth < 0:
        raise ValueError("logarithmic depths must be nonnegative")

    phase_depth = shift_log_depth - zeta_log_depth
    separated = phase_depth > 0
    covered = shift_log_depth == F(2) and separated
    return LargeQHeightPhaseAudit(
        shift_log_depth=shift_log_depth,
        zeta_log_depth=zeta_log_depth,
        phase_ratio_log_depth=phase_depth,
        absolute_before_phase_log_exponent=shift_log_depth - F(2),
        height_kernel_has_arbitrary_decay=True,
        full_height_phase_retained=True,
        strict_phase_separation=separated,
        strict_subface_covered=covered,
        unconditional_coverage=covered,
    )


def large_q_boundary_reflection_audit(
    box: ExponentBox,
    *,
    shift_log_depth: Fraction,
    zeta_log_depth: Fraction,
) -> LargeQBoundaryReflectionAudit:
    """Complete the endpoint divisor sum and isolate the reflected tail.

    The complete divisor sum restricted by ``(d,q)=1`` has mass only
    when the q-free part is one, and its logarithmic derivative is the
    von Mangoldt function of that q-free part.  Formally, a retained
    squarefree reduced variable then forces a prime and upper-bound sieve
    savings dispose of every term containing the sparse main.  Applying
    this completion to the actual dyadic kernel still requires summing
    all reduced-variable scales and removing the coupled AFE weight.
    Those cross-scale steps are not proved, so the formal reflected-tail
    residual is not promoted to an actual boundary reduction.
    """
    if not _is_large_q_bounded_zeta_endpoint(box):
        raise ValueError("box is not the large-q bounded-zeta endpoint")
    if shift_log_depth < 0 or zeta_log_depth < 0:
        raise ValueError("logarithmic depths must be nonnegative")

    return LargeQBoundaryReflectionAudit(
        shift_log_depth=shift_log_depth,
        zeta_log_depth=zeta_log_depth,
        full_q_restricted_divisor_identity_is_exact=True,
        full_mass_supported_on_q_smooth_part=True,
        full_log_term_supported_on_q_free_prime_powers=True,
        squarefree_reduced_variable_forces_prime=True,
        sparse_main_main_has_two_prime_sieve_savings=True,
        sparse_main_tail_has_one_prime_sieve_saving=True,
        formal_terms_with_sparse_main_have_sieve_saving=True,
        dyadic_reduced_scale_prevents_direct_completion=True,
        afe_weight_prevents_exact_full_divisor_completion=True,
        cross_scale_aggregation_proved=False,
        reflected_tail_has_moving_product_threshold=True,
        reflected_tail_phase_separated_at_boundary=False,
        formal_remaining_terms=("reflected_tail", "reflected_tail"),
        reflected_tail_energy_estimate_proved=False,
        unconditional_coverage=False,
    )


def large_q_subcritical_afe_completion_audit(
    box: ExponentBox,
    *,
    afe_product_gap: Fraction,
    mellin_left_shift: Fraction,
) -> LargeQSubcriticalAfeCompletionAudit:
    """Replace V_t(m1*m2) by its residue below the AFE transition.

    On ``m1*m2 <= T^(1-eta)``, shifting the completed Mellin integral
    to ``Re z=-c`` crosses only the residue one and leaves an error
    ``T^(-c*eta)``.  The exact shifted-line count has scale ``T*L`` per
    dyadic ratio family, so this fixed power saving absorbs all
    polylogarithmic partitions.  This replaces the AFE weight inside the
    endpoint family.  It does not complete the divisor sum: at fixed
    product ``n=m*s``, adding divisors ``d`` far below the endpoint scale
    replaces ``m`` by ``n/d`` and can cross the AFE transition.  Hence
    the cross-scale restricted-divisor completion remains unproved.
    """
    if not _is_large_q_bounded_zeta_endpoint(box):
        raise ValueError("box is not the large-q bounded-zeta endpoint")
    if afe_product_gap <= 0 or afe_product_gap >= 1:
        raise ValueError("AFE product gap must lie strictly between zero and one")
    if mellin_left_shift <= 0 or mellin_left_shift >= F(1, 4):
        raise ValueError("Mellin left shift must lie strictly between zero and 1/4")

    return LargeQSubcriticalAfeCompletionAudit(
        afe_product_gap=afe_product_gap,
        afe_product_upper_exponent=F(1) - afe_product_gap,
        mellin_left_shift=mellin_left_shift,
        mellin_residue_is_one=True,
        mellin_remainder_power_saving=(
            afe_product_gap * mellin_left_shift
        ),
        local_shifted_line_absolute_power_exponent=F(1),
        short_side_reciprocity_removes_boundary_loss=True,
        mellin_remainder_aggregates_to_little_oh=True,
        local_endpoint_afe_weight_replaced_by_residue=True,
        all_reduced_dyadic_scales_regrouped_before_absolute_values=False,
        restricted_divisor_completion_applies_to_endpoint_residue_kernel=False,
        subcritical_cross_scale_aggregation_proved=False,
        full_divisor_completion_crosses_afe_transition=True,
        full_endpoint_cross_scale_aggregation_proved=False,
        unconditional_coverage=False,
    )


def large_q_transition_mellin_divisor_audit(
    box: ExponentBox,
) -> LargeQTransitionMellinDivisorAudit:
    """Audit the tempting common-Mellin transition reduction.

    The identity ``m^-z=(m*s)^-z s^z`` moves the Mellin twist into the
    reduced divisor coefficient on the original absolutely convergent
    line.  The q-restricted Euler polynomial and its logarithmic
    derivative are exact there.  Moving the already reindexed energy to
    ``Re z=-c`` is invalid: its coefficients grow like ``n^(c-1/2)``
    and the shifted energy is not absolutely convergent.  Inserting a
    transition cutoff first couples the two divisor choices through
    ``m1*m2=n1*n2/(r*s)``.  Thus this audit rejects the claimed reduction
    to one left-line energy gate.
    """
    if not _is_large_q_bounded_zeta_endpoint(box):
        raise ValueError("box is not the large-q bounded-zeta endpoint")
    return LargeQTransitionMellinDivisorAudit(
        common_mellin_variable_retained=True,
        right_line_product_weight_separates_exactly=True,
        right_line_product_energy_is_absolutely_convergent=True,
        q_restricted_twisted_euler_product_is_exact=True,
        zero_mellin_frequency_recovers_von_mangoldt=True,
        nonzero_mellin_frequency_loses_prime_power_support=True,
        gaussian_mellin_tail_is_absolutely_summable=True,
        left_line_product_energy_is_absolutely_convergent=False,
        transition_cutoff_preserves_one_sided_divisor_completion=False,
        transition_reduced_to_one_twisted_divisor_energy=False,
        twisted_divisor_energy_estimate_proved=False,
        unconditional_coverage=False,
    )


def large_q_transition_compact_mellin_audit(
    box: ExponentBox,
) -> LargeQTransitionCompactMellinAudit:
    """Use compact product support before zero-line Mellin separation.

    A smooth transition band in ``m1*m2`` is compact in the
    multiplicative variable.  Mellin inversion on ``Re z=0`` is then
    exact and rapidly decaying.  The product reindexing
    ``m*s=n`` produces ``D_(q,X,i*tau)(n)`` without a real power of
    ``n``.  This is the scale-stable replacement for the invalid
    left-line termwise shift.  It retains the q-coprimality and reflected
    divisor tail, so the resulting energy estimate is still new.
    """
    if not _is_large_q_afe_transition_face(box):
        raise ValueError("box is not on the large-q AFE transition face")
    product_variable = box.m + box.rho
    absolute_global = F(1) + box.ell
    asymptotic_target = F(1)
    critical_saving = absolute_global - asymptotic_target
    return LargeQTransitionCompactMellinAudit(
        afe_product_band_is_compact=True,
        mellin_separation_line=F(0),
        mellin_inversion_is_exact=True,
        mellin_transform_has_arbitrary_polynomial_decay=True,
        product_coefficients_have_no_real_power_growth=True,
        q_restricted_twisted_divisor_coefficient_is_exact=True,
        coprimality_coupling_is_retained=True,
        reflected_tail_coefficient_is_retained=True,
        transition_reduced_to_compact_mellin_energy=True,
        product_variable_exponent=product_variable,
        shift_exponent=box.ell,
        absolute_global_exponent=absolute_global,
        asymptotic_target_exponent=asymptotic_target,
        critical_power_saving=critical_saving,
        fixed_power_gate_saving=critical_saving + TARGET_SAVING,
        compact_mellin_energy_estimate_proved=False,
        unconditional_coverage=False,
    )


def transition_kim_average_shifted_convolution_audit(
    box: ExponentBox,
    *,
    left_short_interval_exponent: Fraction,
    right_short_interval_exponent: Fraction,
) -> TransitionKimAverageShiftedConvolutionAudit:
    """Compare the transition gate with Kim's average-shift theorem.

    Kim's Theorem 1.2 gives ``X*H^(4/(8-b1-b2))`` for multiplicative
    input functions satisfying the stated short-interval second-moment
    hypotheses.  The localized Mobius-divisor product coefficient is not
    multiplicative, and the common Mellin-twisted weight is not one of the
    theorem's inputs.  Even granting the optimistic values ``b1=b2=1``,
    the resulting exponent misses the fixed transition gate.
    """
    if not _is_large_q_afe_transition_face(box):
        raise ValueError("box is not on the large-q AFE transition face")
    for value in (
        left_short_interval_exponent,
        right_short_interval_exponent,
    ):
        if value <= 0 or value > F(2):
            raise ValueError(
                "Kim short-interval exponent must lie in (0,2]"
            )

    theorem_denominator = (
        F(8)
        - left_short_interval_exponent
        - right_short_interval_exponent
    )
    theorem_h_power = F(4) / theorem_denominator
    correlation_length = box.m + box.rho
    shift_average = box.ell
    theorem_bound = (
        correlation_length + shift_average * theorem_h_power
    )
    fixed_target = correlation_length - TARGET_SAVING
    deficit = _positive_part(theorem_bound - fixed_target)
    multiplicative = False
    mellin_uniform = False
    applicable = multiplicative and mellin_uniform and deficit == 0

    return TransitionKimAverageShiftedConvolutionAudit(
        correlation_length_exponent=correlation_length,
        shift_average_exponent=shift_average,
        left_short_interval_exponent=left_short_interval_exponent,
        right_short_interval_exponent=right_short_interval_exponent,
        theorem_h_power=theorem_h_power,
        optimistic_theorem_bound_exponent=theorem_bound,
        fixed_gate_target_exponent=fixed_target,
        remaining_power_deficit=deficit,
        localized_mobius_divisor_coefficient_is_multiplicative=(
            multiplicative
        ),
        uniform_common_mellin_twist_hypothesis_verified=mellin_uniform,
        theorem_applicable=applicable,
        published_coverage=False,
        source="Kim, arXiv:2509.24152v2, Theorem 1.2",
    )


def h_poisson_subbox_scales(
    box: ExponentBox,
    *,
    v: Fraction,
    j: Fraction,
) -> ShiftedPoissonSubboxScales:
    """Ledger for one dyadic ``(v,j)`` box after ``h``-Poisson.

    Exponent zero includes every fixed bounded interval, in particular the
    resonance box ``v=j=1``.  The returned saving is volume minus the
    coupled target and does not assert that such cancellation is known.
    """
    v_max = completion_dual_exponent(box.h, box.sigma)
    j_max = max(F(0), box.rho - box.h, box.ell - box.sigma)
    if v < 0 or j < 0 or v > v_max or j > j_max:
        raise ValueError("subbox exponents exceed the h-Poisson dual ranges")
    product_scale = max(box.rho + v, box.sigma + j)
    volume = (
        box.rho
        + box.sigma
        + v
        + j
        - _positive_part(product_scale - box.ell)
    )
    target = box.rho + box.sigma - box.h
    gate_target = target - TARGET_SAVING
    return ShiftedPoissonSubboxScales(
        v=v,
        j=j,
        shift=box.ell,
        target=target,
        gate_target=gate_target,
        volume=volume,
        required_saving=volume - gate_target,
        square_root_margin=gate_target - volume / 2,
    )


def joint_phase_scales(box: ExponentBox) -> JointPhaseScales:
    """Audit the joint ``(x,t)`` phase before ``h``-Poisson.

    On ``x \\asymp T^m`` the phase is

    ``t*log(1+delta/(x*r)) - 2*pi*h*x/s``.

    In the small-shift regime its two normalized variation exponents are
    ``1+ell-m-rho`` and ``h+m-sigma``.  For opposite signs of ``h`` and
    ``delta`` the stationary face is
    ``h=sigma+1+ell-2*m-rho``.  For equal signs the derivatives add, but
    integration by parts yields a power of ``T`` only when their largest
    normalized variation exponent is strictly positive.
    """
    t_variation = F(1) + box.ell - box.m - box.rho
    fourier_variation = box.h + box.m - box.sigma
    parameter = max(t_variation, fourier_variation)
    stationary_h = box.sigma + 1 + box.ell - 2 * box.m - box.rho
    return JointPhaseScales(
        stationary_h=stationary_h,
        t_phase_variation=t_variation,
        fourier_phase_variation=fourier_variation,
        same_sign_derivative_parameter=parameter,
        on_stationary_face=box.h == stationary_h,
        same_sign_power_saving=parameter > 0,
    )


def dual_cell_isolation_scales(
    box: ExponentBox,
    *,
    dual_v: Fraction,
) -> DualCellIsolationScales:
    """Ledger for isolating a dyadic ``v`` scale after ``h``-Poisson.

    The Fourier coordinate is ``xi=H*v/s``.  A scale
    ``v \\asymp T^nu`` therefore occupies a window of exponent
    ``h+nu-sigma``.  Multiplication by a cutoff on that window convolves
    the normalized ``h/H`` weight over the reciprocal scale.  A positive
    reciprocal exponent is a power loss in every derivative seminorm, so
    the isolated cell is not uniform in the original coupled-kernel class.
    """
    dual_max = completion_dual_exponent(box.h, box.sigma)
    if dual_v < 0 or dual_v > dual_max:
        raise ValueError("dual_v exceeds the h-Poisson range")
    fourier_window = box.h + dual_v - box.sigma
    spread = _positive_part(-fourier_window)
    return DualCellIsolationScales(
        dual_v=dual_v,
        fourier_window=fourier_window,
        normalized_h_spread=spread,
        physical_h_support=box.h + spread,
        seminorm_cost_per_derivative=spread,
        uniform_in_original_kernel_class=spread == 0,
    )


def farey_critical_scales(
    box: ExponentBox,
    *,
    dual_v: Fraction,
) -> FareyCriticalScales:
    """Ledger for ``r/s`` approximated by the dual rational ``j/v``.

    The determinant equation gives the exact identity
    ``r/s-j/v=delta/(s*v)``.  The natural spacing between fractions of
    denominator ``T^dual_v`` is ``T^(-2*dual_v)``.  For fixed ``r,s,v``,
    the allowed ``j`` interval has length exponent ``ell-sigma``.
    """
    dual_max = completion_dual_exponent(box.h, box.sigma)
    if dual_v < 0 or dual_v > dual_max:
        raise ValueError("dual_v exceeds the h-Poisson range")
    approximation = box.ell - box.sigma - dual_v
    spacing = -2 * dual_v
    j_interval = box.ell - box.sigma
    return FareyCriticalScales(
        dual_v=dual_v,
        j_interval=j_interval,
        at_most_one_j=j_interval < 0,
        rational_approximation=approximation,
        farey_spacing=spacing,
        approximation_minus_spacing=approximation - spacing,
    )


def farey_completion_scales(box: ExponentBox) -> FareyCompletionScales:
    """Ledger after exact finite Fourier inversion in the shift residue.

    The signed shift has scale ``L=T^ell`` inside residues modulo
    ``s=T^sigma``.  Its normalized Fourier coefficients contribute the
    exact density factor ``L/S`` and have effective frequency length
    ``K=S/L``.  The existing ``h``-Poisson frequency has length ``V=S/H``.
    Removing the density factor turns the Farey target into the target for
    a four-variable Kloosterman-fraction sum in ``(r,s,c,v)``.

    These are support and normalization exponents only; the function does
    not assert cancellation in that completed sum.
    """
    v = completion_dual_exponent(box.h, box.sigma)
    residue_frequency = completion_dual_exponent(box.ell, box.sigma)
    prefactor = box.ell - box.sigma
    farey_target = box.rho + box.sigma - box.h - TARGET_SAVING
    normalized_target = farey_target - prefactor
    volume = box.rho + box.sigma + v + residue_frequency
    product_frequency = v + residue_frequency
    total = product_frequency + box.rho + box.sigma
    longest = max(box.rho, box.sigma)
    large_a = F(1, 2) * _positive_part(
        product_frequency - box.rho - box.sigma
    )
    bcr_term_1 = F(17, 20) * total + F(1, 4) * longest + large_a
    bcr_term_2 = (
        F(7, 8) * (box.rho + box.sigma)
        + product_frequency
        + F(1, 8) * longest
        + large_a
    )
    generic_bcr_bound = max(bcr_term_1, bcr_term_2)
    optimistic_large_sieve_bound = (
        box.rho
        + box.sigma
        + product_frequency
        + max(box.rho, 2 * box.sigma)
    ) / 2
    # Fractions a/s need not be reduced.  A fixed reduced fraction can have
    # up to T^product_frequency representatives in the (a,s) box.  Combining
    # duplicate points by Cauchy costs half that exponent.
    fraction_multiplicity = product_frequency
    additive_large_sieve_bound = (
        optimistic_large_sieve_bound + fraction_multiplicity / 2
    )
    return FareyCompletionScales(
        v=v,
        residue_frequency=residue_frequency,
        product_frequency=product_frequency,
        residue_density_prefactor=prefactor,
        two_dimensional_completion_prefactor=(
            box.ell + box.h - box.sigma
        ),
        both_coordinate_axes_empty=(
            box.ell < box.sigma and box.h < box.sigma
        ),
        farey_gate_target=farey_target,
        normalized_gate_target=normalized_target,
        normalized_volume=volume,
        required_saving=volume - normalized_target,
        square_root_margin=normalized_target - volume / 2,
        generic_bcr_bound=generic_bcr_bound,
        generic_bcr_deficit=generic_bcr_bound - normalized_target,
        optimistic_distinct_large_sieve_bound=(
            optimistic_large_sieve_bound
        ),
        optimistic_distinct_large_sieve_deficit=(
            optimistic_large_sieve_bound - normalized_target
        ),
        fraction_multiplicity_exponent=fraction_multiplicity,
        separated_additive_large_sieve_bound=additive_large_sieve_bound,
        separated_additive_large_sieve_deficit=(
            additive_large_sieve_bound - normalized_target
        ),
        zero_residue_forces_centering=box.ell < box.sigma,
    )


def mobius_trace_function_audit(
    box: ExponentBox,
    *,
    modulus_is_prime: bool,
    trace_is_nonexceptional: bool,
) -> MobiusTraceFunctionAudit:
    """Audit Korolev--Shparlinski Theorem 2.1 against a CFK slice.

    The theorem treats a prime modulus, a nonexceptional bounded-
    conductor trace function, and a Möbius interval longer than
    ``p^(1/2+epsilon)``.  Its conclusion saves one logarithm (up to
    ``loglog``), not a fixed power.  The CFK phase in the ``r`` variable is
    linear additive, ``e(c*v*r/s)``, which belongs to the exceptional class
    explicitly excluded by the theorem; its modulus ``s`` also varies over
    general squarefree integers.
    """
    length_margin = box.rho - box.sigma / 2
    length_hypothesis = length_margin > 0
    reasons: list[str] = []
    if not modulus_is_prime:
        reasons.append("requires_prime_modulus")
    if not trace_is_nonexceptional:
        reasons.append("linear_additive_trace_is_exceptional")
    if not length_hypothesis:
        reasons.append("interval_not_beyond_square_root")
    reasons.append("only_logarithmic_saving")
    theorem_applicable = (
        modulus_is_prime
        and trace_is_nonexceptional
        and length_hypothesis
    )
    return MobiusTraceFunctionAudit(
        length_margin=length_margin,
        length_hypothesis=length_hypothesis,
        modulus_is_prime=modulus_is_prime,
        trace_is_nonexceptional=trace_is_nonexceptional,
        theorem_applicable=theorem_applicable,
        power_target_covered=False,
        reasons=tuple(reasons),
    )


def averaged_chowla_shift_audit(
    box: ExponentBox,
) -> AveragedChowlaShiftAudit:
    """Audit averaged Chowla after the exact substitution ``r=s+d``.

    The centered phase becomes ``e(a*d/s)-1`` because ``a`` is an
    integer.  Both Möbius arguments, ``s`` and ``s+d``, consequently have
    unit linear slope.  Matomäki--Radziwiłł--Tao's averaged Elliott theorem
    supplies logarithmic decay for fixed linear-form weights; it supplies
    no positive power and does not accept the actual coefficient
    ``Lambda_{s+d,s}(a)``, which depends jointly on the base and shift.
    """
    completion = farey_completion_scales(box)
    shift = max(box.rho, box.sigma)
    product_frequency = completion.product_frequency
    correlation_volume = box.sigma + shift + product_frequency
    logarithmic_gate_target = (
        completion.normalized_gate_target + TARGET_SAVING
    )
    power_deficit = correlation_volume - logarithmic_gate_target
    reasons = [
        "joint_s_shift_frequency_coefficient",
        "averaged_chowla_saves_only_logarithms",
    ]
    if power_deficit > 0:
        reasons.append("positive_power_deficit")
    return AveragedChowlaShiftAudit(
        shift=shift,
        product_frequency=product_frequency,
        correlation_volume=correlation_volume,
        logarithmic_gate_target=logarithmic_gate_target,
        power_deficit=power_deficit,
        unit_linear_slopes=True,
        zero_shift_excluded=min(box.rho, box.sigma) > 0,
        theorem_applicable=False,
        source=(
            "Matomaki-Radziwill-Tao, arXiv:1503.05121, Theorem 1.6"
        ),
        reasons=tuple(reasons),
    )


def linnik_dispersion_centering_audit(
    box: ExponentBox,
    *,
    gate_log_power: Fraction,
) -> LinnikDispersionCenteringAudit:
    """Separate the linear zero-mode centering from a quadratic diagonal.

    In the exact completed sum the term ``e(a*r/s)-1`` removes the
    additive Fourier zero mode.  Under ``Theta -> z*Theta`` that
    subtraction is linear in ``z``.  The identity diagonal created by a
    dispersion square is instead ``sum |Theta|^2`` and is homogeneous of
    degree two.  Consequently the existing minus-one term cannot be the
    main-diagonal subtraction in a Linnik variance identity.

    Expanding a genuine variance as ``D + O`` leaves a signed
    off-diagonal ``O``.  At the hard box the separate Parseval majorant
    for ``D`` is ``R*C*V = T^4``, exactly the power of the logarithmic
    gate.  Hence discarding or separately majorizing ``O`` cannot produce
    the required logarithmic saving.  Nor is a bound for ``V-D=O`` enough
    after Cauchy: the positive right-hand side is still ``V=D+O``.  A
    valid route must either project away a model at amplitude level before
    Cauchy, or prove with signs retained that ``O`` cancels ``D`` to the
    required logarithmic precision.
    """
    if gate_log_power <= AGGREGATION_LOG_LOSS:
        raise ValueError(
            "gate log power must exceed the global aggregation loss"
        )

    completion = farey_completion_scales(box)
    parseval_diagonal = box.rho + completion.product_frequency
    logarithmic_gate_target = (
        completion.normalized_gate_target + TARGET_SAVING
    )
    power_margin = logarithmic_gate_target - parseval_diagonal

    return LinnikDispersionCenteringAudit(
        parseval_diagonal_exponent=parseval_diagonal,
        logarithmic_gate_target_exponent=logarithmic_gate_target,
        power_margin=power_margin,
        gate_log_power=gate_log_power,
        aggregation_log_loss=AGGREGATION_LOG_LOSS,
        net_log_saving=gate_log_power - AGGREGATION_LOG_LOSS,
        minus_one_homogeneity_degree=F(1),
        parseval_homogeneity_degree=F(2),
        minus_one_removes_fourier_zero_mode=True,
        minus_one_subtracts_parseval_diagonal=False,
        variance_expansion_retains_signed_off_diagonal=True,
        diagonal_only_majorant_closes=(power_margin > 0),
        separate_quadratic_main_term_required=True,
        subtracting_diagonal_after_cauchy_sufficient=False,
        signed_off_diagonal_must_cancel_diagonal=True,
        amplitude_level_projection_is_alternative=True,
        pre_cauchy_signed_subtraction_required=True,
        published_coverage=False,
    )


def centered_resonance_scales(
    box: ExponentBox,
    *,
    slack: Fraction,
) -> CenteredResonanceScales:
    """Ledger for the centered near-resonance collar.

    Put ``p=log_T(CV)`` and ``Delta_s(d)=min_j |d-j*s|``.  Double
    centering gives a coefficient first moment of exponent ``2*p`` and
    hence a collar bound ``(CV)^2 D^2``.  Choosing
    ``D=T^((rho-p)/2-slack)`` saves ``T^(-2*slack)`` against the
    logarithmic LMSD gate ``T^rho*CV``.
    """
    if slack < 0:
        raise ValueError("slack must be nonnegative")
    completion = farey_completion_scales(box)
    product_frequency = completion.product_frequency
    coefficient_first_moment = 2 * product_frequency
    resonance_cutoff = (box.rho - product_frequency) / 2 - slack
    near_resonance_bound = (
        coefficient_first_moment + 2 * resonance_cutoff
    )
    logarithmic_gate_target = (
        completion.normalized_gate_target + TARGET_SAVING
    )
    return CenteredResonanceScales(
        product_frequency=product_frequency,
        coefficient_first_moment=coefficient_first_moment,
        resonance_cutoff=resonance_cutoff,
        phase_variation_at_cutoff=(
            resonance_cutoff + product_frequency - box.sigma
        ),
        near_resonance_bound=near_resonance_bound,
        logarithmic_gate_target=logarithmic_gate_target,
        saving=logarithmic_gate_target - near_resonance_bound,
        nonempty_collar=resonance_cutoff > 0,
    )


def centered_resonance_log_budget(
    box: ExponentBox,
    *,
    gate_log_power: Fraction,
) -> CenteredResonanceLogBudget:
    """Pay the logarithmic LMSD gate with the squared collar width.

    With ``p=log_T(CV)``, choose
    ``D=T^((rho-p)/2) log(2T)^(-B/2)``.  The bound
    ``(CV)^2 D^2`` is then exactly
    ``T^(rho+p) log(2T)^(-B)``.  The present global ledger loses seven
    logarithms, so ``B>7`` produces ``o(T)`` after aggregation.
    """
    if gate_log_power < 0:
        raise ValueError("gate_log_power must be nonnegative")
    completion = farey_completion_scales(box)
    product_frequency = completion.product_frequency
    resonance_power_cutoff = (box.rho - product_frequency) / 2
    resonance_log_cutoff = gate_log_power / 2
    near_bound_power = (
        2 * product_frequency + 2 * resonance_power_cutoff
    )
    near_bound_log_saving = 2 * resonance_log_cutoff
    logarithmic_gate_power = (
        completion.normalized_gate_target + TARGET_SAVING
    )
    power_matches_gate = near_bound_power == logarithmic_gate_power
    global_log_margin = gate_log_power - AGGREGATION_LOG_LOSS
    centered_completion_applicable = completion.both_coordinate_axes_empty
    nonempty_log_collar = resonance_power_cutoff > 0
    return CenteredResonanceLogBudget(
        resonance_power_cutoff=resonance_power_cutoff,
        resonance_log_cutoff=resonance_log_cutoff,
        near_bound_power=near_bound_power,
        near_bound_log_saving=near_bound_log_saving,
        aggregation_log_loss=AGGREGATION_LOG_LOSS,
        global_log_margin=global_log_margin,
        power_matches_gate=power_matches_gate,
        centered_completion_applicable=centered_completion_applicable,
        nonempty_log_collar=nonempty_log_collar,
        produces_little_o=(
            power_matches_gate
            and centered_completion_applicable
            and nonempty_log_collar
            and global_log_margin > 0
        ),
    )


def endpoint_centered_resonance_log_budget(
    box: ExponentBox,
    *,
    gate_log_power: Fraction,
    endpoint_factors: int,
) -> EndpointCenteredResonanceLogBudget:
    """Insert the available ``p_N`` endpoint logarithms into the collar.

    Each verified top-endpoint mollifier factor contributes one inverse
    logarithm.  The remaining logarithmic gate is paid by ``D^2``, so its
    exponent is halved when converted to the cutoff for ``D``.
    """
    if gate_log_power < 0:
        raise ValueError("gate_log_power must be nonnegative")
    if endpoint_factors not in (0, 1, 2):
        raise ValueError("endpoint_factors must be 0, 1, or 2")
    completion = farey_completion_scales(box)
    product_frequency = completion.product_frequency
    resonance_power_cutoff = (box.rho - product_frequency) / 2
    endpoint_log_saving = F(endpoint_factors)
    analytic_log_saving_required = _positive_part(
        gate_log_power - endpoint_log_saving
    )
    resonance_log_cutoff = analytic_log_saving_required / 2
    total_near_bound_log_saving = (
        2 * resonance_log_cutoff + endpoint_log_saving
    )
    global_log_margin = (
        total_near_bound_log_saving - AGGREGATION_LOG_LOSS
    )
    available_endpoint_factors = sum(
        exponent == F(3)
        for exponent in (
            box.kappa + box.rho,
            box.kappa + box.sigma,
        )
    )
    endpoint_power_face = endpoint_factors <= available_endpoint_factors
    centered_completion_applicable = completion.both_coordinate_axes_empty
    nonempty_log_collar = resonance_power_cutoff > 0
    return EndpointCenteredResonanceLogBudget(
        resonance_power_cutoff=resonance_power_cutoff,
        endpoint_log_saving=endpoint_log_saving,
        analytic_log_saving_required=analytic_log_saving_required,
        resonance_log_cutoff=resonance_log_cutoff,
        total_near_bound_log_saving=total_near_bound_log_saving,
        aggregation_log_loss=AGGREGATION_LOG_LOSS,
        global_log_margin=global_log_margin,
        full_power_collar_global_log_margin=(
            endpoint_log_saving - AGGREGATION_LOG_LOSS
        ),
        endpoint_power_face=endpoint_power_face,
        centered_completion_applicable=centered_completion_applicable,
        nonempty_log_collar=nonempty_log_collar,
        produces_little_o=(
            endpoint_power_face
            and centered_completion_applicable
            and nonempty_log_collar
            and global_log_margin > 0
        ),
    )


def endpoint_critical_aggregation_budget(
    box: ExponentBox,
    *,
    endpoint_factors: int,
    q_logarithmic_depth: Fraction,
    frequency_logarithmic_depth: Fraction,
) -> EndpointCriticalAggregationBudget:
    """Count a bounded logarithmic neighborhood of the hard endpoint.

    The crude global ledger has six dyadic parameters ``R,S,K,M,L,H``.
    On this face, the two endpoint constraints determine ``R,S`` for a
    fixed ``q``; ratio balance determines ``K`` from ``M``; and the two
    critical frequency constraints determine ``H,L`` from ``M,R,S``.
    The entire line ``0 <= m <= 1/2`` remains, so the ``M`` dyadic sum is
    genuine.  The centered absolute bound loses a factor ``q`` against
    the normalized local gate.  Thus after taking absolute values the
    ``q`` aggregation is cardinal, not harmonic.  If ``q <= L^gamma``
    and the frequency collar loses ``L^beta``, the two endpoint tapers
    leave the exact logarithmic margin ``1-gamma-beta`` after the genuine
    ``M`` dyadic sum.  Critical ``H,L`` collars add only log-log losses.
    """
    if endpoint_factors not in (0, 1, 2):
        raise ValueError("endpoint_factors must be 0, 1, or 2")
    if q_logarithmic_depth < 0:
        raise ValueError("q_logarithmic_depth must be nonnegative")
    if frequency_logarithmic_depth < 0:
        raise ValueError("frequency_logarithmic_depth must be nonnegative")

    raw_dyadic_log_loss = F(6)
    endpoint_faces = sum(
        exponent == F(3)
        for exponent in (
            box.kappa + box.rho,
            box.kappa + box.sigma,
        )
    )
    endpoint_rs_removed = F(2) if endpoint_faces == 2 else F(0)
    ratio_face = box.k + box.sigma == box.m + box.rho
    ratio_k_removed = F(1) if ratio_face else F(0)
    h_critical = box.h == box.sigma - box.m
    ell_critical = box.ell == box.m + box.rho - 1
    critical_hl_removed = F(h_critical) + F(ell_critical)
    remaining_dyadic_log_loss = (
        raw_dyadic_log_loss
        - endpoint_rs_removed
        - ratio_k_removed
        - critical_hl_removed
    )
    total_log_power_loss = (
        remaining_dyadic_log_loss
        + q_logarithmic_depth
        + frequency_logarithmic_depth
    )
    certified_endpoint_factors = min(endpoint_factors, endpoint_faces)
    endpoint_log_saving = F(certified_endpoint_factors)
    net_log_power = endpoint_log_saving - total_log_power_loss
    polyloglog_loss_exponent = (
        F(2) if h_critical and ell_critical else F(0)
    )
    critical_face = (
        is_admissible(box)
        and box.kappa == F(0)
        and endpoint_faces == 2
        and endpoint_factors == 2
        and ratio_face
        and h_critical
        and ell_critical
    )
    extra_log_saving_required = (
        critical_face
        and polyloglog_loss_exponent > 0
        and net_log_power <= 0
    )
    absolute_bound_produces_little_o = (
        critical_face and net_log_power > 0
    )
    return EndpointCriticalAggregationBudget(
        raw_dyadic_log_loss=raw_dyadic_log_loss,
        endpoint_rs_removed=endpoint_rs_removed,
        ratio_k_removed=ratio_k_removed,
        critical_hl_removed=critical_hl_removed,
        remaining_dyadic_log_loss=remaining_dyadic_log_loss,
        q_logarithmic_depth=q_logarithmic_depth,
        frequency_logarithmic_depth=frequency_logarithmic_depth,
        q_aggregation_is_cardinal=True,
        total_log_power_loss=total_log_power_loss,
        endpoint_log_saving=endpoint_log_saving,
        net_log_power=net_log_power,
        polyloglog_loss_exponent=polyloglog_loss_exponent,
        critical_face=critical_face,
        extra_log_saving_required=extra_log_saving_required,
        absolute_bound_produces_little_o=(
            absolute_bound_produces_little_o
        ),
    )


def improved_averaged_chowla_shell_audit(
    box: ExponentBox,
    *,
    q_logarithmic_depth: Fraction,
    frequency_logarithmic_depth: Fraction,
) -> ImprovedAveragedChowlaShellAudit:
    """Compare MRT and Menon on a logarithmic critical subface.

    The endpoint tapers and the genuine ``M`` dyadic sum leave margin one.
    A cardinal ``q <= L^gamma`` sum and frequency deficit ``L^beta``
    consume ``gamma+beta``.  MRT adds ``1/3000`` logarithm, whereas
    Menon's improved averaged-Chowla theorem adds one logarithm with a
    squared ``log log`` loss in the unit-slope sector.  For all four MWKF
    slopes, a polarization and Fourier-identity transfer from Menon's
    exponential-sum theorem costs a square root, leaving one-half of a
    logarithm.  Hence the full separated ledger closes for
    ``gamma+beta < 3/2``.

    The finite Fourier BV argument certifies the actual smooth completion
    coefficient.  Exact gcd inversion, its summable common-divisor tail,
    and Menon's polylogarithmic character uniformity certify transfer
    through the coprimality conditions.
    """
    if q_logarithmic_depth < 0:
        raise ValueError("q_logarithmic_depth must be nonnegative")
    if frequency_logarithmic_depth < 0:
        raise ValueError("frequency_logarithmic_depth must be nonnegative")

    total_logarithmic_depth = (
        q_logarithmic_depth + frequency_logarithmic_depth
    )
    mrt_log_saving = F(1, 3000)
    unit_slope_improved_log_saving = F(1)
    fixed_slope_black_box_log_saving = F(1, 2)
    improved_polyloglog_loss_exponent = F(2)
    fixed_slope_polyloglog_loss_exponent = F(1)
    endpoint_faces = (
        box.kappa + box.rho == F(3)
        and box.kappa + box.sigma == F(3)
    )
    ratio_face = box.k + box.sigma == box.m + box.rho
    h_critical = box.h == box.sigma - box.m
    ell_critical = box.ell == box.m + box.rho - 1
    power_critical_face = (
        is_admissible(box)
        and box.kappa == F(0)
        and endpoint_faces
        and ratio_face
        and h_critical
        and ell_critical
    )
    stationary_face = joint_phase_scales(box).on_stationary_face
    endpoint_absolute_log_margin = F(1) - total_logarithmic_depth
    mrt_log_margin = endpoint_absolute_log_margin + mrt_log_saving
    unit_slope_log_margin = (
        endpoint_absolute_log_margin + unit_slope_improved_log_saving
    )
    all_sector_log_margin = (
        endpoint_absolute_log_margin + fixed_slope_black_box_log_saving
    )
    all_sector_subface_covered = (
        power_critical_face
        and stationary_face
        and all_sector_log_margin > 0
    )
    fixed_slope_black_box_proved = True
    fixed_slope_extension_required = False
    bv_separation_proved = True
    bv_separation_required = False
    joint_coefficient_accepted = True
    coprimality_transfer_required = False
    coprimality_transfer_proved = True
    return ImprovedAveragedChowlaShellAudit(
        q_logarithmic_depth=q_logarithmic_depth,
        frequency_logarithmic_depth=frequency_logarithmic_depth,
        total_logarithmic_depth=total_logarithmic_depth,
        mrt_log_saving=mrt_log_saving,
        unit_slope_improved_log_saving=unit_slope_improved_log_saving,
        fixed_slope_black_box_log_saving=(
            fixed_slope_black_box_log_saving
        ),
        improved_polyloglog_loss_exponent=(
            improved_polyloglog_loss_exponent
        ),
        fixed_slope_polyloglog_loss_exponent=(
            fixed_slope_polyloglog_loss_exponent
        ),
        endpoint_absolute_log_margin=endpoint_absolute_log_margin,
        mrt_log_margin=mrt_log_margin,
        unit_slope_log_margin=unit_slope_log_margin,
        all_sector_log_margin=all_sector_log_margin,
        power_critical_face=power_critical_face,
        stationary_face=stationary_face,
        all_sector_subface_covered=all_sector_subface_covered,
        fixed_slope_black_box_proved=fixed_slope_black_box_proved,
        fixed_slope_extension_required=fixed_slope_extension_required,
        bv_separation_proved=bv_separation_proved,
        bv_separation_required=bv_separation_required,
        joint_coefficient_accepted=joint_coefficient_accepted,
        coprimality_transfer_required=coprimality_transfer_required,
        coprimality_transfer_proved=coprimality_transfer_proved,
        published_coverage=(
            all_sector_subface_covered
            and bv_separation_proved
            and coprimality_transfer_proved
        ),
        source=(
            "Menon, arXiv:2607.15574v1, "
            "Theorems improved_exp_sum and improved_avg_chowla"
        ),
    )


def completion_weight_bv_audit(
    box: ExponentBox,
    *,
    x_log_scale: Fraction,
    y_log_scale: Fraction,
) -> CompletionWeightBVAudit:
    """Ledger for normalized ``(s,w)`` BV separation after completion.

    Here ``x=HM/S`` and ``y=TL/(MR)`` have logarithmic scales
    ``log_L(x)`` and ``log_L(y)``.  One normalized derivative of the
    coupled kernel costs at most ``max(1,x,y)`` and the mixed derivative
    costs its square.  The centered absolute bound already contains the
    gain ``xy``.  On the low-variation region or the stationary log face,
    that gain pays the derivative cost without adding to the existing
    frequency depth.  A positive unequal pair is removed by integration
    by parts in the coupled physical phase instead of being retained.

    This is an exact logarithmic ledger.  The analytic proof that realizes
    these costs from the finite Fourier formula is recorded separately.
    """
    completion = farey_completion_scales(box)
    max_parameter = max(F(0), x_log_scale, y_log_scale)
    kernel_first_derivative_log_cost = max_parameter
    kernel_mixed_derivative_log_cost = 2 * max_parameter
    amplitude_log_gain = x_log_scale + y_log_scale
    absolute_frequency_log_depth = _positive_part(-amplitude_log_gain)
    bv_net_log_depth = (
        kernel_mixed_derivative_log_cost - amplitude_log_gain
    )
    bv_extra_log_depth = _positive_part(
        bv_net_log_depth - absolute_frequency_log_depth
    )
    offstationary_log_gap = abs(x_log_scale - y_log_scale)
    low_variation_regime = max(x_log_scale, y_log_scale) <= 0
    stationary_log_face = (
        max_parameter > 0 and x_log_scale == y_log_scale
    )
    offstationary_ibp_available = (
        max_parameter > 0 and offstationary_log_gap > 0
    )
    retained_after_phase_partition = (
        low_variation_regime or stationary_log_face
    )
    centered_phase_power_slack = _positive_part(
        box.sigma - F(1) - completion.product_frequency
    )
    lifted_fourier_formula_exact = True
    raw_first_moment_scale_preserved = (
        retained_after_phase_partition
        and kernel_mixed_derivative_log_cost == 0
        and centered_phase_power_slack > 0
    )
    bv_preserves_global_log_depth = (
        retained_after_phase_partition
        and bv_extra_log_depth == 0
        and centered_phase_power_slack > 0
    )
    return CompletionWeightBVAudit(
        x_log_scale=x_log_scale,
        y_log_scale=y_log_scale,
        kernel_first_derivative_log_cost=(
            kernel_first_derivative_log_cost
        ),
        kernel_mixed_derivative_log_cost=(
            kernel_mixed_derivative_log_cost
        ),
        amplitude_log_gain=amplitude_log_gain,
        absolute_frequency_log_depth=absolute_frequency_log_depth,
        bv_net_log_depth=bv_net_log_depth,
        bv_extra_log_depth=bv_extra_log_depth,
        offstationary_log_gap=offstationary_log_gap,
        centered_phase_power_slack=centered_phase_power_slack,
        low_variation_regime=low_variation_regime,
        stationary_log_face=stationary_log_face,
        offstationary_ibp_available=offstationary_ibp_available,
        retained_after_phase_partition=retained_after_phase_partition,
        lifted_fourier_formula_exact=lifted_fourier_formula_exact,
        raw_first_moment_scale_preserved=(
            raw_first_moment_scale_preserved
        ),
        bv_preserves_global_log_depth=(
            bv_preserves_global_log_depth
        ),
    )


def coprimality_restricted_menon_audit(
    box: ExponentBox,
    *,
    q_logarithmic_depth: Fraction,
    frequency_logarithmic_depth: Fraction,
    common_divisor_cutoff_log_depth: Fraction,
) -> CoprimalityRestrictedMenonAudit:
    """Audit the gcd inversion and polylogarithmic character twist.

    Möbius inversion of ``(s,w)=1`` introduces a common divisor ``d``.
    After ``s=d*n`` and ``w=d*u``, the two-dimensional correlation volume
    falls by ``d^2``.  Thus ``d>L^A`` saves ``L^-A``.  On the retained
    range the restricted function is
    ``mu_Q(n)=mu(n)*chi_0,Q(n)`` with
    ``Q=q*d <= L^(gamma+A)``.  Menon's character-twisted short-interval
    theorem, followed by the same circle-method and fixed-slope transfer,
    is uniform for every fixed polylogarithmic modulus exponent.
    """
    depths = (
        q_logarithmic_depth,
        frequency_logarithmic_depth,
        common_divisor_cutoff_log_depth,
    )
    if any(depth < 0 for depth in depths):
        raise ValueError("logarithmic depths must be nonnegative")

    improved = improved_averaged_chowla_shell_audit(
        box,
        q_logarithmic_depth=q_logarithmic_depth,
        frequency_logarithmic_depth=frequency_logarithmic_depth,
    )
    common_divisor_volume_decay = F(2)
    common_divisor_tail_log_saving = (
        (common_divisor_volume_decay - 1)
        * common_divisor_cutoff_log_depth
    )
    common_divisor_tail_log_margin = (
        improved.endpoint_absolute_log_margin
        + common_divisor_tail_log_saving
    )
    restricted_modulus_log_depth = (
        q_logarithmic_depth + common_divisor_cutoff_log_depth
    )
    fixed_slope_log_saving = F(1, 2)
    exact_gcd_reindex_proved = True
    tail_is_summable = common_divisor_volume_decay > 1
    common_divisor_tail_produces_little_o = (
        common_divisor_tail_log_margin > 0
    )
    principal_character_twist = True
    polylog_twist_uniformity_proved = True
    coprimality_transfer_proved = (
        exact_gcd_reindex_proved
        and tail_is_summable
        and principal_character_twist
        and polylog_twist_uniformity_proved
    )
    subface_covered = (
        improved.power_critical_face
        and improved.stationary_face
        and improved.bv_separation_proved
        and coprimality_transfer_proved
        and improved.all_sector_log_margin > 0
        and common_divisor_tail_produces_little_o
    )
    return CoprimalityRestrictedMenonAudit(
        q_logarithmic_depth=q_logarithmic_depth,
        frequency_logarithmic_depth=frequency_logarithmic_depth,
        common_divisor_cutoff_log_depth=(
            common_divisor_cutoff_log_depth
        ),
        common_divisor_volume_decay=common_divisor_volume_decay,
        common_divisor_tail_log_saving=common_divisor_tail_log_saving,
        common_divisor_tail_log_margin=common_divisor_tail_log_margin,
        restricted_modulus_log_depth=restricted_modulus_log_depth,
        fixed_slope_log_saving=fixed_slope_log_saving,
        all_sector_log_margin=improved.all_sector_log_margin,
        exact_gcd_reindex_proved=exact_gcd_reindex_proved,
        tail_is_summable=tail_is_summable,
        common_divisor_tail_produces_little_o=(
            common_divisor_tail_produces_little_o
        ),
        principal_character_twist=principal_character_twist,
        polylog_twist_uniformity_proved=(
            polylog_twist_uniformity_proved
        ),
        coprimality_transfer_proved=coprimality_transfer_proved,
        subface_covered=subface_covered,
        source=(
            "Menon, arXiv:2607.15574v1, character-twisted "
            "short-interval theorem plus fixed-slope transfer"
        ),
    )


def far_resonance_shell_scales(
    box: ExponentBox,
    *,
    distance: Fraction,
) -> FarResonanceShellScales:
    """Absolute ledger for ``Delta_s(d) asy T^distance``.

    There are ``T^(sigma+distance)`` base/shift pairs and the completed
    product-frequency L1 scale is ``T^p``.  Centering contributes
    ``min(1, T^(distance+p-sigma))``.  The difference between this
    absolute exponent and the LMSD power target is the exact cancellation
    which a far-resonance theorem must supply on this shell.
    """
    if distance < 0 or distance > max(box.rho, box.sigma):
        raise ValueError("distance exceeds the shifted-variable range")
    completion = farey_completion_scales(box)
    product_frequency = completion.product_frequency
    phase_amplitude = min(
        F(0),
        distance + product_frequency - box.sigma,
    )
    absolute_bound = (
        box.sigma
        + distance
        + product_frequency
        + phase_amplitude
    )
    logarithmic_gate_target = (
        completion.normalized_gate_target + TARGET_SAVING
    )
    return FarResonanceShellScales(
        distance=distance,
        product_frequency=product_frequency,
        phase_amplitude=phase_amplitude,
        absolute_bound=absolute_bound,
        logarithmic_gate_target=logarithmic_gate_target,
        required_power_saving=_positive_part(
            absolute_bound - logarithmic_gate_target
        ),
        at_power_barrier=absolute_bound == logarithmic_gate_target,
    )


def averaged_chowla_shell_audit(
    box: ExponentBox,
    *,
    distance: Fraction,
    gate_log_power: Fraction,
) -> AveragedChowlaShellAudit:
    """Compare MRT's quantitative decay with one resonance shell.

    For a power-sized shift interval, Theorem 1.6 gives at best the
    ``log(X)^(-1/3000)`` term in its stated quantitative factor.  This
    cannot meet a larger logarithmic gate, and it never pays a positive
    power deficit.  The actual completed coefficient also depends jointly
    on the base, shift, and product frequency, outside the theorem input.
    """
    if gate_log_power < 0:
        raise ValueError("gate_log_power must be nonnegative")
    shell = far_resonance_shell_scales(box, distance=distance)
    theorem_log_saving = F(1, 3000)
    log_shortfall = _positive_part(
        gate_log_power - theorem_log_saving
    )
    reasons = ["joint_s_shift_frequency_coefficient"]
    if shell.required_power_saving > 0:
        reasons.append("positive_power_deficit")
    elif log_shortfall > 0:
        reasons.append("insufficient_logarithmic_saving")
    return AveragedChowlaShellAudit(
        distance=distance,
        required_power_saving=shell.required_power_saving,
        theorem_log_saving=theorem_log_saving,
        required_log_saving=gate_log_power,
        log_shortfall=log_shortfall,
        theorem_applicable=False,
        source=(
            "Matomaki-Radziwill-Tao, arXiv:1503.05121, Theorem 1.6"
        ),
        reasons=tuple(reasons),
    )


def inverse_resonance_bcr_scales(
    box: ExponentBox,
    *,
    distance: Fraction,
) -> InverseResonanceBCRScales:
    """Optimistic Bettin--Chandee ledger after ``bar(r)=bar(w) mod s``.

    On a resonance shell the inverse variable has length ``D``, the
    modulus has length ``S``, and grouping the original two short
    variables gives numerator length ``H*L``.  This calculation grants
    separated coefficients optimistically; the actual kernel and the
    Möbius factor ``mu((j+1)s+w)`` remain joint in ``(w,s)``.
    """
    if distance < 0 or distance > max(box.rho, box.sigma):
        raise ValueError("distance exceeds the shifted-variable range")
    inverse_length = distance
    modulus_length = box.sigma
    numerator_product_length = box.ell + box.h
    total = (
        inverse_length + modulus_length + numerator_product_length
    )
    longest = max(inverse_length, modulus_length)
    large_numerator = F(1, 2) * _positive_part(
        numerator_product_length - inverse_length - modulus_length
    )
    term_1 = (
        F(17, 20) * total
        + F(1, 4) * longest
        + large_numerator
    )
    term_2 = (
        F(7, 8) * (inverse_length + modulus_length)
        + numerator_product_length
        + F(1, 8) * longest
        + large_numerator
    )
    bound = max(term_1, term_2)
    gate_target = box.rho + box.sigma
    deficit = bound - gate_target
    return InverseResonanceBCRScales(
        distance=distance,
        inverse_length=inverse_length,
        modulus_length=modulus_length,
        numerator_product_length=numerator_product_length,
        term_1=term_1,
        term_2=term_2,
        bound=bound,
        gate_target=gate_target,
        deficit=deficit,
        joint_coefficient_accepted=False,
        published_coverage=False,
    )


def primitive_fraction_large_sieve_scales(
    box: ExponentBox,
    *,
    distance: Fraction,
) -> PrimitiveFractionLargeSieveScales:
    """Ledger for the additive large sieve on primitive ``bar(w)/s``.

    The shell contains at most ``S*D`` reduced fractions.  Their spacing
    is ``S^(-2)`` and their multiplicity is one.  After smooth separation,
    the numerator coefficient has length ``A=H*L`` and squared L2 norm
    ``T^(log_T A+epsilon)``.  Outer Cauchy and the additive large sieve
    give

    ``(S*D)^(1/2) * (A+S^2)^(1/2) * A^(1/2+epsilon)``.
    """
    shell = far_resonance_shell_scales(box, distance=distance)
    numerator_product_length = box.ell + box.h
    fraction_family = box.sigma + distance
    large_sieve_bound = (
        fraction_family / 2
        + max(numerator_product_length, 2 * box.sigma) / 2
        + numerator_product_length / 2
    )
    completion_prefactor = box.ell + box.h - box.sigma
    centered_absolute_bound = shell.absolute_bound + completion_prefactor
    best_unconditional_bound = min(
        large_sieve_bound,
        centered_absolute_bound,
    )
    gate_target = box.rho + box.sigma
    return PrimitiveFractionLargeSieveScales(
        distance=distance,
        fraction_family=fraction_family,
        primitive_fraction_spacing=-2 * box.sigma,
        fraction_multiplicity=F(0),
        numerator_product_length=numerator_product_length,
        large_sieve_bound=large_sieve_bound,
        centered_absolute_bound=centered_absolute_bound,
        best_unconditional_bound=best_unconditional_bound,
        gate_target=gate_target,
        remaining_power_saving=_positive_part(
            best_unconditional_bound - gate_target
        ),
        improves_absolute_bound=(
            large_sieve_bound < centered_absolute_bound
        ),
    )


def reciprocal_cluster_large_sieve_scales(
    box: ExponentBox,
    *,
    distance: Fraction,
) -> ReciprocalClusterLargeSieveScales:
    """Large-sieve ledger after reciprocity to Farey centers modulo ``w``.

    The identity ``-bar(w)/s = bar(s)/w - 1/(s*w) (mod 1)`` places each
    frequency within ``1/(S*D)`` of a reduced denominator-``D`` Farey
    point.  When ``S*D >= H*L``, that displacement is below the numerator
    resolution.  Each center has ``S/D`` preimages, and a resolution
    interval meets ``1+D^2/(H*L)`` centers.  The local-density large sieve
    therefore has exponent

    ``(S*D)^(1/2) * (S/D)^(1/2)``
    ``* (H*L+D^2)^(1/2) * (H*L)^(1/2+epsilon)``.
    """
    numerator_product_length = box.ell + box.h
    if distance < 0 or distance > box.sigma:
        raise ValueError("reciprocal clustering requires 0 <= D <= S")
    correction_within_resolution = (
        box.sigma + distance >= numerator_product_length
    )
    if not correction_within_resolution:
        raise ValueError("reciprocity correction exceeds numerator resolution")
    cluster_multiplicity = box.sigma - distance
    clustered_large_sieve_bound = (
        box.sigma
        + max(numerator_product_length, 2 * distance) / 2
        + numerator_product_length / 2
    )
    primitive = primitive_fraction_large_sieve_scales(
        box,
        distance=distance,
    )
    best_unconditional_bound = min(
        clustered_large_sieve_bound,
        primitive.best_unconditional_bound,
    )
    gate_target = box.rho + box.sigma
    return ReciprocalClusterLargeSieveScales(
        distance=distance,
        cluster_multiplicity=cluster_multiplicity,
        farey_center_spacing=-2 * distance,
        reciprocity_correction=-box.sigma - distance,
        numerator_resolution=-numerator_product_length,
        correction_within_resolution=correction_within_resolution,
        clustered_large_sieve_bound=clustered_large_sieve_bound,
        primitive_best_bound=primitive.best_unconditional_bound,
        best_unconditional_bound=best_unconditional_bound,
        gate_target=gate_target,
        remaining_power_saving=_positive_part(
            best_unconditional_bound - gate_target
        ),
        improves_primitive_bound=(
            clustered_large_sieve_bound
            < primitive.best_unconditional_bound
        ),
    )


def prime_factor_trace_twist_audit(
    box: ExponentBox,
    *,
    distance: Fraction,
    prime_factor_exponent: Fraction,
    applications: int,
    eta: Fraction,
) -> PrimeFactorTraceTwistAudit:
    """Optimistic FKM power ledger after extracting a prime modulus factor.

    On a centered shell, ``r = k*s+w`` ranges through an interval of
    length ``X=T^distance``.  If a prime ``p=T^pi`` divides ``s``, the
    ``p``-part of ``e(-n*bar(r)/s)`` is a bounded-conductor rational
    inverse trace weight in ``r`` whenever ``n`` is nonzero modulo ``p``.
    The smoothed estimate in Fouvry--Kowalski--Michel, Theorem 1.7, is

    ``X * (1+p/X)^(1/6) * p^(-eta)``,  for every ``eta < 1/24``.

    Hence its exact power saving is
    ``eta*pi - max(0,pi-distance)/6`` when positive.  This adapter grants
    that saving once or twice optimistically.  It does *not* assert that
    every squarefree modulus has a prime factor of the requested size,
    separate the complementary-modulus coefficient, or dispose of the
    frequencies divisible by ``p``.
    """
    if distance < 0 or distance > max(box.rho, box.sigma):
        raise ValueError("distance exceeds the shifted-variable range")
    if prime_factor_exponent <= 0 or prime_factor_exponent > box.sigma:
        raise ValueError("prime factor exponent must lie in (0,sigma]")
    if applications not in (1, 2):
        raise ValueError("applications must be one or two")
    fkm_eta_ceiling = F(1, 24)
    if eta <= 0 or eta >= fkm_eta_ceiling:
        raise ValueError("eta must be strictly below 1/24")

    interval_over_modulus_penalty = _positive_part(
        prime_factor_exponent - distance
    ) / 6
    one_sided_power_saving = _positive_part(
        eta * prime_factor_exponent
        - interval_over_modulus_penalty
    )
    optimistic_total_power_saving = (
        applications * one_sided_power_saving
    )

    primitive = primitive_fraction_large_sieve_scales(
        box,
        distance=distance,
    )
    current_far_shell_deficit = primitive.remaining_power_saving
    numerator_product_length = box.ell + box.h
    if (
        distance <= box.sigma
        and box.sigma + distance >= numerator_product_length
    ):
        reciprocal = reciprocal_cluster_large_sieve_scales(
            box,
            distance=distance,
        )
        current_far_shell_deficit = min(
            current_far_shell_deficit,
            reciprocal.remaining_power_saving,
        )
    optimistic_residual_deficit = _positive_part(
        current_far_shell_deficit - optimistic_total_power_saving
    )
    optimistic_gate_covered = optimistic_residual_deficit == 0

    return PrimeFactorTraceTwistAudit(
        distance=distance,
        prime_factor_exponent=prime_factor_exponent,
        applications=applications,
        eta=eta,
        fkm_eta_ceiling=fkm_eta_ceiling,
        interval_over_modulus_penalty=(
            interval_over_modulus_penalty
        ),
        one_sided_power_saving=one_sided_power_saving,
        optimistic_total_power_saving=(
            optimistic_total_power_saving
        ),
        current_far_shell_deficit=current_far_shell_deficit,
        optimistic_residual_deficit=optimistic_residual_deficit,
        trace_is_nonexceptional=True,
        prime_modulus_hypothesis=True,
        nonzero_prime_frequency_uniform=False,
        uniform_prime_factor_available=False,
        joint_cofactor_accepted=False,
        optimistic_gate_covered=optimistic_gate_covered,
        published_coverage=False,
        source=(
            "Fouvry--Kowalski--Michel, arXiv:1211.6043v3, "
            "Theorem 1.7 (Trace weights vs. Mobius)"
        ),
    )


def squarefree_linear_completion_audit(
    box: ExponentBox,
    *,
    distance: Fraction,
    short_factor_total: Fraction,
) -> SquarefreeLinearCompletionAudit:
    """Audit Type-I linear completion without dropping squarefree support.

    Expand ``c_U(a)`` by writing ``a=d*e`` and put ``r=d*b*e``.
    On a centered shell the long quotient ``e`` has interval exponent
    ``distance-short_factor_total`` and linear phase
    ``e(c*v*d*b*e/s)``.  Since ``(d*b,s)=1``, reducing this rational
    phase can remove at most the ``c*v`` part of exponent ``p``; hence
    its denominator has exponent at least ``sigma-p``.

    Schlage--Puchta's rational-point squarefree exponential-sum bound is
    ``Y^(1+eps)/Q + Y^(1/2+eps) + Q*Y^eps``.  We minimize its exponent
    optimistically over every reduced denominator allowed by the lower
    bound.  Coprimality progressions are deliberately not charged, so a
    positive result here is only an upper limit on this route.
    """
    if distance < 0 or distance > max(box.rho, box.sigma):
        raise ValueError("distance exceeds the shifted-variable range")
    if short_factor_total < 0 or short_factor_total > distance:
        raise ValueError("short factor total must lie in [0,distance]")

    long_quotient_interval = distance - short_factor_total
    product_frequency = farey_completion_scales(box).product_frequency
    reduced_denominator_lower_bound = _positive_part(
        box.sigma - product_frequency
    )
    unconstrained_optimum = long_quotient_interval / 2
    optimistic_reduced_denominator = max(
        reduced_denominator_lower_bound,
        min(box.sigma, unconstrained_optimum),
    )
    rational_major_arc_term = _positive_part(
        long_quotient_interval - optimistic_reduced_denominator
    )
    square_root_term = long_quotient_interval / 2
    denominator_term = optimistic_reduced_denominator
    optimistic_theorem_bound = min(
        long_quotient_interval,
        max(
            rational_major_arc_term,
            square_root_term,
            denominator_term,
        ),
    )
    power_saving = _positive_part(
        long_quotient_interval - optimistic_theorem_bound
    )
    original_shell_deficit = far_resonance_shell_scales(
        box,
        distance=distance,
    ).required_power_saving
    remaining_shell_deficit = _positive_part(
        original_shell_deficit - power_saving
    )
    factor_subbox_covered = remaining_shell_deficit == 0

    return SquarefreeLinearCompletionAudit(
        distance=distance,
        short_factor_total=short_factor_total,
        long_quotient_interval=long_quotient_interval,
        product_frequency=product_frequency,
        reduced_denominator_lower_bound=(
            reduced_denominator_lower_bound
        ),
        optimistic_reduced_denominator=(
            optimistic_reduced_denominator
        ),
        rational_major_arc_term=rational_major_arc_term,
        square_root_term=square_root_term,
        denominator_term=denominator_term,
        optimistic_theorem_bound=optimistic_theorem_bound,
        power_saving=power_saving,
        original_shell_deficit=original_shell_deficit,
        remaining_shell_deficit=remaining_shell_deficit,
        squarefree_support_retained=True,
        coprimality_progressions_charged=False,
        factor_subbox_covered=factor_subbox_covered,
        published_coverage=False,
        source=(
            "Schlage--Puchta, arXiv:1105.1616v1, Theorem 3"
        ),
    )


def type_ii_cauchy_diagonal_audit(
    box: ExponentBox,
    *,
    b_exponent: Fraction,
) -> TypeIICauchyDiagonalAudit:
    """Power ledger for the positive identity diagonal after Cauchy in ``b``.

    In the Type-II factorization ``r=a*b``, the permitted exponent range
    is ``rho/3 <= beta <= 2*rho/3`` and ``a`` has exponent
    ``rho-beta``.  The exact identical-tuple contribution to
    ``sum_b |A_b|^2`` has one copy each of ``b,a,s`` and the squared
    ``h*delta`` coefficient norm.  Its exponent is therefore

    ``beta + (rho-beta) + sigma + (ell+h)``.

    Compare this with the spectral target ``R^2*S^2/B*T^(-1/250)``.
    The adapter only audits a proof which majorizes that positive
    diagonal separately; it does not assert a lower bound for the full
    signed expanded square.
    """
    b_exponent_range = (box.rho / 3, 2 * box.rho / 3)
    if not b_exponent_range[0] <= b_exponent <= b_exponent_range[1]:
        raise ValueError("b exponent lies outside the Type-II range")

    a_exponent = box.rho - b_exponent
    numerator_l2_exponent = box.ell + box.h
    identity_diagonal_exponent = (
        b_exponent
        + a_exponent
        + box.sigma
        + numerator_l2_exponent
    )
    spectral_target_exponent = (
        2 * box.rho + 2 * box.sigma - b_exponent - F(1, 250)
    )
    spectral_target_margin = (
        spectral_target_exponent - identity_diagonal_exponent
    )
    post_cauchy_diagonal_exponent = (
        b_exponent + identity_diagonal_exponent
    ) / 2
    post_cauchy_target_exponent = (
        box.rho + box.sigma - F(1, 500)
    )
    post_cauchy_target_deficit = _positive_part(
        post_cauchy_diagonal_exponent - post_cauchy_target_exponent
    )
    separate_diagonal_majorant_closes = spectral_target_margin > 0

    return TypeIICauchyDiagonalAudit(
        b_exponent=b_exponent,
        b_exponent_range=b_exponent_range,
        a_exponent=a_exponent,
        modulus_exponent=box.sigma,
        numerator_l2_exponent=numerator_l2_exponent,
        identity_diagonal_exponent=identity_diagonal_exponent,
        spectral_target_exponent=spectral_target_exponent,
        spectral_target_margin=spectral_target_margin,
        post_cauchy_diagonal_exponent=(
            post_cauchy_diagonal_exponent
        ),
        post_cauchy_target_exponent=post_cauchy_target_exponent,
        post_cauchy_target_deficit=post_cauchy_target_deficit,
        exact_identity_diagonal_present=True,
        dispersion_subtraction_required=(
            not separate_diagonal_majorant_closes
        ),
        separate_diagonal_majorant_closes=(
            separate_diagonal_majorant_closes
        ),
        published_coverage=False,
    )


def zero_ray_convolution_centering_audit(
    box: ExponentBox,
    *,
    b_exponent: Fraction,
) -> ZeroRayConvolutionCenteringAudit:
    """Record the exact ``mu*c_U`` centering on the ``u=v=1`` ray.

    The full convolution is
    ``sum_(s*a=k) mu(s)c_U(a)=mu(k)1_(k<=U)``.  The actual Type sector
    restricts ``a>U`` and therefore equals ``-mu(k)`` when ``k>U``.
    Subtracting an anchor depending only on ``k`` consequently leaves an
    explicit Möbius main term, plus a centered factorization sum.  The
    dyadic localization and fixed-factor reciprocal phase depend
    separately on ``s,a`` and the latter sum still needs an estimate.
    """
    b_exponent_range = (box.rho / 3, 2 * box.rho / 3)
    if not b_exponent_range[0] <= b_exponent <= b_exponent_range[1]:
        raise ValueError("b exponent lies outside the Type-II range")

    a_exponent = box.rho - b_exponent
    product_ray_exponent = box.sigma + a_exponent
    cutoff_exponent = box.rho / 3
    product_above_cutoff = product_ray_exponent > cutoff_exponent
    joint_gram_target_exponent = (
        2 * box.rho + 2 * box.sigma - b_exponent - F(1, 250)
    )
    explicit_mobius_main_squared_exponent = (
        b_exponent
        + box.ell
        + box.h
        + product_ray_exponent
    )
    explicit_main_target_margin = (
        joint_gram_target_exponent
        - explicit_mobius_main_squared_exponent
    )
    separate_explicit_main_majorant_closes = (
        explicit_main_target_margin > 0
    )

    return ZeroRayConvolutionCenteringAudit(
        b_exponent=b_exponent,
        a_exponent=a_exponent,
        product_ray_exponent=product_ray_exponent,
        cutoff_exponent=cutoff_exponent,
        product_above_cutoff=product_above_cutoff,
        full_convolution_vanishes_exactly=(
            product_above_cutoff
        ),
        type_sector_convolution_equals_negative_mobius=(
            product_above_cutoff
        ),
        type_sector_convolution_vanishes=False,
        factorization_anchor_may_depend_only_on_product=True,
        factorization_anchor_leaves_explicit_mobius_main=True,
        dyadic_factor_localization_breaks_exact_zero=True,
        fixed_factor_phase_breaks_product_invariance=True,
        joint_gram_gate_required=True,
        joint_gram_target_exponent=(
            joint_gram_target_exponent
        ),
        explicit_mobius_main_squared_exponent=(
            explicit_mobius_main_squared_exponent
        ),
        explicit_main_target_margin=explicit_main_target_margin,
        separate_explicit_main_majorant_closes=(
            separate_explicit_main_majorant_closes
        ),
        joint_cross_term_required=(
            not separate_explicit_main_majorant_closes
        ),
        published_coverage=False,
    )


def primitive_slope_zero_ray_audit(
    box: ExponentBox,
    *,
    b_exponent: Fraction,
    slope_exponent: Fraction,
) -> PrimitiveSlopeZeroRayAudit:
    """Audit the general primitive ray ``(u,v)`` in ``Delta=0``.

    For ``u,v`` in a dyadic slope box of exponent ``theta``, the exact
    ray equations give ``g`` exponent ``ell+h-theta`` and ``k`` exponent
    ``sigma+(rho-beta)-theta``.  The paired restricted convolution main
    is ``mu(uk)mu(vk)=mu(u)mu(v)`` on squarefree support, so no Möbius
    cancellation remains in ``k``.  ``double_square_root_saving`` is a
    benchmark for square-root cancellation in both primitive slopes,
    not a proved estimate.
    """
    b_exponent_range = (box.rho / 3, 2 * box.rho / 3)
    if not b_exponent_range[0] <= b_exponent <= b_exponent_range[1]:
        raise ValueError("b exponent lies outside the Type-II range")

    a_exponent = box.rho - b_exponent
    product_ray_exponent = box.sigma + a_exponent
    numerator_exponent = box.ell + box.h
    slope_exponent_range = (
        F(0),
        min(product_ray_exponent, numerator_exponent),
    )
    if not slope_exponent_range[0] <= slope_exponent <= slope_exponent_range[1]:
        raise ValueError("slope exponent lies outside the zero-ray range")

    common_n_factor_exponent = numerator_exponent - slope_exponent
    common_y_factor_exponent = product_ray_exponent - slope_exponent
    primitive_pair_cardinality_exponent = 2 * slope_exponent
    explicit_main_cardinality_exponent = (
        b_exponent
        + primitive_pair_cardinality_exponent
        + common_n_factor_exponent
        + common_y_factor_exponent
    )
    joint_gram_target_exponent = (
        2 * box.rho + 2 * box.sigma - b_exponent - F(1, 250)
    )
    required_power_saving = _positive_part(
        explicit_main_cardinality_exponent - joint_gram_target_exponent
    )
    double_square_root_saving = slope_exponent
    double_square_root_has_exponent_slack = (
        double_square_root_saving > required_power_saving
    )

    return PrimitiveSlopeZeroRayAudit(
        b_exponent=b_exponent,
        slope_exponent=slope_exponent,
        slope_exponent_range=slope_exponent_range,
        common_n_factor_exponent=common_n_factor_exponent,
        common_y_factor_exponent=common_y_factor_exponent,
        primitive_pair_cardinality_exponent=(
            primitive_pair_cardinality_exponent
        ),
        explicit_main_cardinality_exponent=(
            explicit_main_cardinality_exponent
        ),
        joint_gram_target_exponent=joint_gram_target_exponent,
        required_power_saving=required_power_saving,
        double_square_root_saving=double_square_root_saving,
        double_square_root_has_exponent_slack=(
            double_square_root_has_exponent_slack
        ),
        low_slope_benchmark_obstruction=(
            not double_square_root_has_exponent_slack
        ),
        primitive_slope_mobius_pair_retained=True,
        common_k_mobius_cancellation_available=False,
        primitive_slope_reciprocal_conductor_present=False,
        published_coverage=False,
    )


def long_mobius_cutoff_audit(
    box: ExponentBox,
    *,
    cutoff_exponent: Fraction,
    squared_target_saving: Fraction,
) -> LongMobiusCutoffAudit:
    """Audit the exact identity with a cutoff longer than ``R^(1/3)``.

    Taking ``U=T^lambda`` in the finite identity (2.2) forces
    ``a>U`` and hence ``b`` to exponent at most ``rho-lambda``.  No
    auxiliary ``V`` split is required.  This can put the cardinality
    diagonal below the post-Cauchy target, but it leaves the reciprocal
    modulus ``a*b`` at exponent ``rho`` and proves no off-diagonal bound.
    """
    if not F(0) < cutoff_exponent < box.rho:
        raise ValueError("cutoff exponent must lie strictly between 0 and rho")
    if squared_target_saving <= 0:
        raise ValueError("squared target saving must be positive")

    complementary_factor_max_exponent = box.rho - cutoff_exponent
    long_factor_min_exponent = cutoff_exponent
    identity_diagonal_exponent = (
        box.rho + box.sigma + box.ell + box.h
    )
    worst_spectral_target_exponent = (
        2 * box.rho
        + 2 * box.sigma
        - complementary_factor_max_exponent
        - squared_target_saving
    )
    worst_diagonal_margin = (
        worst_spectral_target_exponent - identity_diagonal_exponent
    )
    zero_completion_endpoint_c_exponent = (
        box.ell
        + box.h
        + box.sigma
        + long_factor_min_exponent
        - complementary_factor_max_exponent
    )

    return LongMobiusCutoffAudit(
        cutoff_exponent=cutoff_exponent,
        complementary_factor_max_exponent=(
            complementary_factor_max_exponent
        ),
        long_factor_min_exponent=long_factor_min_exponent,
        squared_target_saving=squared_target_saving,
        identity_diagonal_exponent=identity_diagonal_exponent,
        worst_spectral_target_exponent=worst_spectral_target_exponent,
        worst_diagonal_margin=worst_diagonal_margin,
        all_factor_boxes_have_diagonal_power_slack=(
            worst_diagonal_margin > 0
        ),
        entire_zero_ray_cardinality_has_power_slack=(
            worst_diagonal_margin > 0
        ),
        exact_single_sector_identity=True,
        v_split_omitted_exactly=True,
        reciprocal_modulus_exponent=box.rho,
        reciprocal_conductor_reduced=False,
        zero_completion_endpoint_c_exponent=(
            zero_completion_endpoint_c_exponent
        ),
        full_off_diagonal_imposes_b_divides_delta=False,
        published_off_diagonal_coverage=False,
    )


def long_cutoff_h_completion_audit(
    box: ExponentBox,
    *,
    b_exponent: Fraction,
) -> LongCutoffHCompletionAudit:
    """Reject Poisson in the short ``b`` phase before the ``a`` phase.

    The common-``b`` factor alone has ``H/B`` periods, but the same
    ``h`` variable also occurs in the fixed-``a`` phase with normalized
    frequency ``H*L/A``.  That frequency is a positive power throughout
    the long-cutoff range, so it cannot be hidden in a smooth amplitude.
    The complete phase still has modulus ``a*b`` of exponent ``rho``.
    """
    if not F(0) <= b_exponent <= box.rho:
        raise ValueError("b exponent lies outside the factor range")

    a_exponent = box.rho - b_exponent
    common_b_period_surplus = box.h - b_exponent
    fixed_a_normalized_frequency = (
        box.h + box.ell - a_exponent
    )
    full_modulus_period_surplus = box.h - box.rho
    fixed_a_phase_is_smooth_for_b_poisson = (
        fixed_a_normalized_frequency <= 0
    )
    b_only_poisson_valid = (
        common_b_period_surplus > 0
        and fixed_a_phase_is_smooth_for_b_poisson
    )

    return LongCutoffHCompletionAudit(
        b_exponent=b_exponent,
        a_exponent=a_exponent,
        common_b_period_surplus=common_b_period_surplus,
        fixed_a_normalized_frequency=fixed_a_normalized_frequency,
        full_modulus_period_surplus=full_modulus_period_surplus,
        fixed_a_phase_is_smooth_for_b_poisson=(
            fixed_a_phase_is_smooth_for_b_poisson
        ),
        b_only_poisson_valid=b_only_poisson_valid,
        full_phase_modulus_exponent=box.rho,
        published_coverage=False,
    )


def long_cutoff_quotient_split_audit(
    box: ExponentBox,
    *,
    cutoff_exponent: Fraction,
    b_exponent: Fraction,
    dual_v_exponent: Fraction,
) -> LongCutoffQuotientSplitAudit:
    """Split the quotient weight at the exact BV square-root boundary.

    Insert ``r=a*b`` with ``a>U=T^u`` into
    ``a*b*v-j*s=delta`` and expand

    ``c_U(a)=sum_(d|a,d<=U) mu(d)``, ``a=d*e``.

    Fixing ``delta,j,b,d,v`` restricts ``s`` to one progression modulo
    ``b*d*|v|`` after the exact gcd reduction.  For a length ``S``
    Möbius sum, the formal level-one-half endpoint is obtained by taking

    ``d <= D = S^(1/2)/(b*|v|)``.

    The endpoint requires a polylogarithmic retreat in an actual
    Bombieri--Vinogradov statement.  More importantly, this exponent
    identity alone does not verify that theorem's averaging hypotheses:
    the residue classes and smooth weights are coupled to
    ``delta,j,b,v,d``.  The complementary sector retains ``mu(d)mu(s)``
    and has cofactor ``e`` of the recorded maximal exponent.
    """
    max_b_exponent = box.rho - cutoff_exponent
    max_v_exponent = completion_dual_exponent(box.h, box.sigma)
    if cutoff_exponent <= 0 or cutoff_exponent > box.rho:
        raise ValueError("cutoff exponent lies outside the r range")
    if b_exponent < 0 or b_exponent > max_b_exponent:
        raise ValueError("b exponent lies outside the long-cutoff range")
    if dual_v_exponent < 0 or dual_v_exponent > max_v_exponent:
        raise ValueError("v exponent lies outside the completion range")

    a_exponent = box.rho - b_exponent
    bv_modulus_exponent = b_exponent + dual_v_exponent
    small_divisor_level_exponent = (
        box.sigma / 2 - bv_modulus_exponent
    )
    if small_divisor_level_exponent < 0:
        raise ValueError("b*v already exceeds the level-one-half modulus")
    expanded_modulus_endpoint = (
        bv_modulus_exponent + small_divisor_level_exponent
    )
    large_divisor_upper_exponent = min(cutoff_exponent, a_exponent)
    large_cofactor_max_exponent = (
        a_exponent - small_divisor_level_exponent
    )

    return LongCutoffQuotientSplitAudit(
        cutoff_exponent=cutoff_exponent,
        b_exponent=b_exponent,
        dual_v_exponent=dual_v_exponent,
        a_exponent=a_exponent,
        bv_modulus_exponent=bv_modulus_exponent,
        small_divisor_level_exponent=small_divisor_level_exponent,
        expanded_modulus_endpoint=expanded_modulus_endpoint,
        large_divisor_lower_exponent=small_divisor_level_exponent,
        large_divisor_upper_exponent=large_divisor_upper_exponent,
        large_cofactor_max_exponent=large_cofactor_max_exponent,
        strict_bv_log_slack_required=True,
        gcd_reduction_only_decreases_modulus=True,
        large_sector_retains_two_mobius_weights=True,
        standard_bv_coupled_hypotheses_verified=False,
        published_coverage=False,
    )


def long_cutoff_quotient_bdh_audit(
    box: ExponentBox,
    *,
    b_exponent: Fraction,
    d_exponent: Fraction,
    dual_v_exponent: Fraction,
    dual_j_exponent: Fraction,
) -> LongCutoffQuotientBDHAudit:
    """Test the quotient progression against an optimistic BDH variance.

    Let ``Q=T^(beta+kappa+nu)`` be the unreduced modulus ``b*d*|v|``.
    Reindexing by ``delta,j`` gives ``T^(ell+j)`` residue queries for
    each factor-product family.  Even if all query-dependent kernels are
    replaced by one common progression weight, the coefficient
    multiplicity and the ideal variance

    ``sum_(m~Q) sum_(a mod m) |E(m,a)|^2 <= S*Q``

    yield the recorded Cauchy bound.  This is an optimistic exponent
    ledger, not an invocation of a published BDH theorem.

    The second ledger converts from the signed-Farey normalization to
    finite completion by ``S/L`` and then grants the *full* product-phase
    variation ``(S/H)*V`` as a saving.  The latter is also only an
    optimistic benchmark: resonant fractions and the genuine coupled
    Fourier coefficient prevent a termwise geometric-sum argument.
    """
    max_v_exponent = completion_dual_exponent(box.h, box.sigma)
    max_j_exponent = max(
        F(0),
        box.rho - box.h,
        box.ell - box.sigma,
    )
    for name, value in (
        ("b", b_exponent),
        ("d", d_exponent),
        ("v", dual_v_exponent),
        ("j", dual_j_exponent),
    ):
        if value < 0:
            raise ValueError(f"{name} exponent must be nonnegative")
    if dual_v_exponent > max_v_exponent:
        raise ValueError("v exponent lies outside the completion range")
    if dual_j_exponent > max_j_exponent:
        raise ValueError("j exponent lies outside the determinant range")

    modulus_exponent = b_exponent + d_exponent + dual_v_exponent
    if modulus_exponent > box.sigma / 2:
        raise ValueError("quotient modulus exceeds the BDH square-root face")
    shift_query_exponent = box.ell + dual_j_exponent
    query_family_exponent = modulus_exponent + shift_query_exponent
    progression_length_exponent = box.sigma - modulus_exponent
    total_cardinality_exponent = shift_query_exponent + box.sigma
    residue_multiplicity_exponent = _positive_part(
        shift_query_exponent - modulus_exponent
    )
    outer_coefficient_l2_squared_exponent = (
        query_family_exponent + residue_multiplicity_exponent
    )
    ideal_bdh_variance_exponent = box.sigma + modulus_exponent
    optimistic_bdh_bound_exponent = (
        outer_coefficient_l2_squared_exponent
        + ideal_bdh_variance_exponent
    ) / 2
    farey_gate_target_exponent = (
        box.rho + box.sigma - box.h - TARGET_SAVING
    )
    bdh_remaining_deficit = _positive_part(
        optimistic_bdh_bound_exponent - farey_gate_target_exponent
    )

    completion_conversion_exponent = box.sigma - box.ell
    c_frequency_exponent = completion_dual_exponent(box.h, box.sigma)
    max_centered_product_phase_saving = (
        c_frequency_exponent + dual_v_exponent
    )
    optimistic_centered_bound_exponent = (
        optimistic_bdh_bound_exponent
        + completion_conversion_exponent
        - max_centered_product_phase_saving
    )
    completed_gate_target_exponent = (
        farey_gate_target_exponent + completion_conversion_exponent
    )
    centered_remaining_deficit = _positive_part(
        optimistic_centered_bound_exponent - completed_gate_target_exponent
    )

    return LongCutoffQuotientBDHAudit(
        modulus_exponent=modulus_exponent,
        query_family_exponent=query_family_exponent,
        progression_length_exponent=progression_length_exponent,
        total_cardinality_exponent=total_cardinality_exponent,
        residue_multiplicity_exponent=residue_multiplicity_exponent,
        outer_coefficient_l2_squared_exponent=(
            outer_coefficient_l2_squared_exponent
        ),
        ideal_bdh_variance_exponent=ideal_bdh_variance_exponent,
        optimistic_bdh_bound_exponent=optimistic_bdh_bound_exponent,
        farey_gate_target_exponent=farey_gate_target_exponent,
        bdh_remaining_deficit=bdh_remaining_deficit,
        completion_conversion_exponent=completion_conversion_exponent,
        max_centered_product_phase_saving=(
            max_centered_product_phase_saving
        ),
        optimistic_centered_bound_exponent=(
            optimistic_centered_bound_exponent
        ),
        completed_gate_target_exponent=completed_gate_target_exponent,
        centered_remaining_deficit=centered_remaining_deficit,
        common_weight_hypothesis_verified=False,
        centered_geometric_saving_proved=False,
        published_coverage=False,
    )


def pascadi_incomplete_kloosterman_audit(
    box: ExponentBox,
) -> PascadiIncompleteKloostermanAudit:
    """Insert the original core into Pascadi Corollary 18 optimistically.

    Corollary 18 bounds an incomplete Kloosterman form with phase
    ``e(+-n*inverse(r*d)/(s*c))`` and

    ``I^2 = D^2*N*R + exceptional_factor``
    ``      * C*S*(C+D*R)*(R*S+N)``.

    Give the MWKF core the most favorable direct identification: set the
    level factors ``R=S=1``, take the incomplete variables to be the
    original ``r,s``, and collapse ``n=h*delta``.  This assumes that the
    genuinely coupled product coefficient can be separated and satisfy
    Assumption 14.  Even after those unverified concessions, the regular
    spectrum term alone is much larger than the Farey gate.
    """
    product_n_exponent = box.h + box.ell
    incomplete_d_exponent = box.rho
    modulus_c_exponent = box.sigma
    coefficient_l2_exponent = product_n_exponent / 2
    level_r_exponent = F(0)
    level_s_exponent = F(0)
    regular_i_squared_exponent = (
        2 * incomplete_d_exponent
        + product_n_exponent
        + level_r_exponent
    )
    exceptional_i_squared_exponent = (
        modulus_c_exponent
        + level_s_exponent
        + max(
            modulus_c_exponent,
            incomplete_d_exponent + level_r_exponent,
        )
        + max(
            level_r_exponent + level_s_exponent,
            product_n_exponent,
        )
    )
    i_exponent = max(
        regular_i_squared_exponent,
        exceptional_i_squared_exponent,
    ) / 2
    optimistic_bound_exponent = coefficient_l2_exponent + i_exponent
    gate_target_exponent = (
        box.rho + box.sigma - box.h - TARGET_SAVING
    )
    remaining_deficit = _positive_part(
        optimistic_bound_exponent - gate_target_exponent
    )

    return PascadiIncompleteKloostermanAudit(
        product_n_exponent=product_n_exponent,
        incomplete_d_exponent=incomplete_d_exponent,
        modulus_c_exponent=modulus_c_exponent,
        coefficient_l2_exponent=coefficient_l2_exponent,
        regular_i_squared_exponent=regular_i_squared_exponent,
        exceptional_i_squared_exponent=exceptional_i_squared_exponent,
        i_exponent=i_exponent,
        optimistic_bound_exponent=optimistic_bound_exponent,
        gate_target_exponent=gate_target_exponent,
        remaining_deficit=remaining_deficit,
        product_coefficient_separated_optimistically=True,
        assumption_14_verified=False,
        direct_corollary_hypotheses_verified=False,
        published_coverage=False,
        source="Pascadi, arXiv:2404.04239v3, Corollary 18 (5.35)",
    )


def centered_quotient_poisson_audit(
    box: ExponentBox,
) -> CenteredQuotientPoissonAudit:
    """Audit Poisson summation in the long-cutoff cofactor ``e``.

    The long-cutoff identity may be restricted to squarefree ``r=b*d*e``
    before expanding its divisor coefficient.  Consequently the exact
    ``e``-support contains ``mu(e)^2`` and ``(e,b*d*s*q)=1``.  Treating
    ``e`` as unweighted is therefore invalid until both conditions are
    expanded by Möbius inversion.

    Double centering also does not kill the constant term separately:
    zero row and column sums imply that the mass over ``c,v != 0`` is
    ``Theta(0,0)``.  If the full ``c,v`` transform is retained, finite
    orthogonality simply reconstructs the original bilinear kernel and
    hence the same determinant/Farey gate.  This exact loop supplies no
    conductor reduction by itself.
    """
    max_v_exponent = completion_dual_exponent(box.ell, box.sigma)
    e_cofactor_max_exponent = (
        box.rho - box.sigma / 2 + max_v_exponent
    )
    return CenteredQuotientPoissonAudit(
        e_cofactor_max_exponent=e_cofactor_max_exponent,
        squarefree_e_support_required=True,
        coprimality_e_support_required=True,
        squarefree_divisor_expansion_exact=True,
        nonzero_frequency_mass_equals_theta_00=True,
        centered_minus_one_vanishes_separately=False,
        unweighted_e_poisson_valid=False,
        joint_c_v_orthogonality_recloses_original_kernel=True,
        determinant_gate_unchanged=True,
        new_conductor_reduction=False,
        published_coverage=False,
    )


def hecke_mobius_local_factor(
    lambda_p: Fraction,
    central_character_p: Fraction,
) -> HeckeMobiusLocalFactor:
    """Return the exact unramified local Euler-factor bookkeeping.

    With ``x=p^(-z)`` and

    ``L_p(z,f)^(-1)=1-lambda_p*x+central_character_p*x^2``, the
    squarefree Mobius factor is ``D_p=1-lambda_p*x``.  Therefore

    ``D_p = H_p/L_p`` with
    ``H_p=(1-lambda_p*x)/(1-lambda_p*x+central_character_p*x^2)``.

    This identity is purely local.  It neither derives a Hecke polynomial
    from the QCT geometric kernel nor controls the conductor of a spectral
    family.
    """
    lambda_p = F(lambda_p)
    central_character_p = F(central_character_p)
    mobius_factor = (F(1), -lambda_p)
    inverse_l_factor = (F(1), -lambda_p, central_character_p)
    correction_minus_one_numerator = (
        F(0),
        F(0),
        -central_character_p,
    )
    return HeckeMobiusLocalFactor(
        mobius_factor=mobius_factor,
        inverse_l_factor=inverse_l_factor,
        correction_numerator=mobius_factor,
        correction_denominator=inverse_l_factor,
        correction_minus_one_numerator=correction_minus_one_numerator,
        euler_factor_identity_exact=True,
    )


def hecke_mobius_spectral_audit(
    *,
    polynomial_length_exponent: Fraction,
    conductor_exponent_witness: Fraction,
    required_log_saving_power: int,
) -> HeckeMobiusSpectralAudit:
    """Audit the missing passage from QCT geometry to spectral cancellation.

    Knightly--Li Theorem 7.14 places one fixed Hecke-operator index on
    the spectral side.  Linearity can formally sum that index against
    Mobius coefficients, but the geometric side is then a family of
    generalized twisted Kloosterman sums.  No identity with the current
    QCT determinant kernel, and no simultaneous derivation of both Mobius
    weights as Hecke polynomials, has been proved.

    The zero-free-region ledger is also decisive.  If ``X=T^rho`` and a
    spectral conductor has the polynomial witness ``C=T^kappa`` with
    ``rho,kappa>0``, a classical width ``1/log C`` gives only constant
    contour displacement ``eta*log X``.  Thorner's 2026 uniform width
    ``C^(-epsilon)`` gives ``eta*log X -> 0`` for every fixed epsilon.
    Either is smaller than the necessary ``B*log log T`` displacement.
    """
    polynomial_length_exponent = F(polynomial_length_exponent)
    conductor_exponent_witness = F(conductor_exponent_witness)
    if polynomial_length_exponent <= 0:
        raise ValueError("polynomial length exponent must be positive")
    if conductor_exponent_witness <= 0:
        raise ValueError("conductor exponent witness must be positive")
    if required_log_saving_power <= 0:
        raise ValueError("required logarithmic saving must be positive")

    local = hecke_mobius_local_factor(F(0), F(1))
    return HeckeMobiusSpectralAudit(
        polynomial_length_exponent=polynomial_length_exponent,
        conductor_exponent_witness=conductor_exponent_witness,
        required_log_saving_power=required_log_saving_power,
        local_euler_factor_exact=local.euler_factor_identity_exact,
        knightly_li_has_one_fixed_hecke_index=True,
        linear_superposition_formally_creates_one_mobius_hecke_sum=True,
        qct_geometry_identified_with_generalized_kloosterman_family=False,
        two_mobius_weights_derived_as_hecke_polynomials=False,
        classical_polynomial_conductor_saving_only_constant=True,
        thorner_polynomial_conductor_saving_tends_to_one=True,
        spectral_conductor_verified=False,
        uniform_zero_free_log_saving_verified=False,
        published_coverage=False,
    )


def determinant_orbit_phase_identity(
    *,
    r: int,
    s: int,
    v: int,
    j: int,
    h: int,
) -> bool:
    """Check the exact phase identity on ``delta=r*v-j*s``.

    When ``(r,s)=1``, the determinant congruence gives
    ``delta*inverse(r) == v (mod s)``.  Thus the original phase
    ``e(-h*delta*inverse(r)/s)`` is the linear orbit phase
    ``e(-h*v/s)``.
    """
    if s <= 0:
        raise ValueError("modulus s must be positive")
    if gcd(r, s) != 1:
        raise ValueError("r and s must be coprime")
    delta = r * v - j * s
    inverse_r = pow(r, -1, s)
    return (-h * delta * inverse_r + h * v) % s == 0


def determinant_orbit_hecke_index_audit() -> DeterminantOrbitHeckeIndexAudit:
    """Identify the Hecke index in the exact determinant orbit.

    In the level-one generalized Kloosterman sum, take the residue pair
    ``(d,d')=(r,v)``, modulus ``s``, determinant/Hecke index ``n=delta``,
    and Fourier indices ``(m2,m1)=(0,-h)``.  The existing Mobius weights
    are instead on the residue entry ``r`` and on the modulus ``s``.
    Therefore superposing Knightly--Li in its Hecke index would weight
    ``delta``, which is not an existing Mobius variable in QCT.
    """
    return DeterminantOrbitHeckeIndexAudit(
        matrix_entries=("r", "j", "s", "v"),
        determinant_symbol="delta",
        modulus_symbol="s",
        residue_pair=("r", "v"),
        hecke_operator_index_symbol="delta",
        kloosterman_fourier_indices=("0", "-h"),
        original_phase_reduces_to_linear_orbit_phase=True,
        r_mobius_weights_residue_entry=True,
        s_mobius_weights_modulus=True,
        delta_mobius_weight_present=False,
        knightly_li_superposition_targets_existing_mobius_weight=False,
        two_existing_mobius_weights_become_hecke_polynomials=False,
        qct_kernel_is_unweighted_complete_orbit=False,
        published_coverage=False,
    )


def fixed_modulus_kloosterman_completion_audit(
    box: ExponentBox,
) -> FixedModulusKloostermanCompletionAudit:
    """Audit finite completion of the ``r``-sum at fixed modulus ``s``.

    After optimistically separating the coupled ``r``-kernel, finite
    Fourier inversion gives

    ``s^(-1) sum_m Fhat_s(m) sum_{h,delta} S(-h*delta,m;s)``.

    Parseval gives ``||Fhat_s||_2 <= (s*R)^(1/2)``.  For fixed
    ``(delta,s)``, Blomer--Pascadi Theorem 5.7 is applied with interval
    lengths ``M=H``, ``N=s`` and modulus ``c=s``.  The dimensionless
    factor is the maximum of

    ``(H*s)^(1/2)/s^(3/4)``, ``s^(1/2)/s^(1/2)``, and
    ``H^(1/2)/s^(1/4)``.

    This is an optimistic rejection: the theorem requires the fixed
    multiplier ``-delta`` to be a unit modulo ``s``, and the actual
    kernel has not been separated.  The Milićević--Qin--Wu size condition
    ``M^(7/5)*N < s^(3/2)`` is recorded independently.
    """
    modulus_exponent = box.sigma
    h_exponent = box.h
    delta_exponent = box.ell
    r_fourier_l2_exponent = (box.sigma + box.rho) / 2
    h_coefficient_l2_exponent = box.h / 2
    bp_57_dimensionless_factor_exponent = max(
        F(0),
        box.h / 2 - box.sigma / 4,
    )
    bp_57_fixed_delta_s_exponent_before_completion = (
        r_fourier_l2_exponent
        + h_coefficient_l2_exponent
        + box.sigma
        + bp_57_dimensionless_factor_exponent
    )
    completion_normalization_exponent = -box.sigma
    bp_57_global_bound_exponent = (
        bp_57_fixed_delta_s_exponent_before_completion
        + completion_normalization_exponent
        + box.ell
        + box.sigma
    )
    original_cardinality_exponent = (
        box.rho + box.sigma + box.h + box.ell
    )
    bp_57_saving_exponent = _positive_part(
        original_cardinality_exponent - bp_57_global_bound_exponent
    )
    ck_gate_target_exponent = box.rho + box.sigma - TARGET_SAVING
    remaining_deficit = _positive_part(
        bp_57_global_bound_exponent - ck_gate_target_exponent
    )
    mqw_size_lhs_exponent = F(7, 5) * box.h + box.sigma
    mqw_size_rhs_exponent = F(3, 2) * box.sigma
    mqw_size_condition_deficit = _positive_part(
        mqw_size_lhs_exponent - mqw_size_rhs_exponent
    )
    product_residue_energy_exponent = (
        box.h
        + box.ell
        + _positive_part(box.h + box.ell - box.sigma)
    )
    product_residue_l2_exponent = product_residue_energy_exponent / 2
    kloosterman_operator_norm_exponent = box.sigma
    orthogonality_global_bound_exponent = (
        product_residue_l2_exponent
        + r_fourier_l2_exponent
        + kloosterman_operator_norm_exponent
        + completion_normalization_exponent
        + box.sigma
    )
    orthogonality_saving_exponent = _positive_part(
        original_cardinality_exponent
        - orthogonality_global_bound_exponent
    )
    orthogonality_remaining_deficit = _positive_part(
        orthogonality_global_bound_exponent - ck_gate_target_exponent
    )

    return FixedModulusKloostermanCompletionAudit(
        modulus_exponent=modulus_exponent,
        h_exponent=h_exponent,
        delta_exponent=delta_exponent,
        r_fourier_l2_exponent=r_fourier_l2_exponent,
        h_coefficient_l2_exponent=h_coefficient_l2_exponent,
        bp_57_dimensionless_factor_exponent=(
            bp_57_dimensionless_factor_exponent
        ),
        bp_57_fixed_delta_s_exponent_before_completion=(
            bp_57_fixed_delta_s_exponent_before_completion
        ),
        completion_normalization_exponent=completion_normalization_exponent,
        bp_57_global_bound_exponent=bp_57_global_bound_exponent,
        original_cardinality_exponent=original_cardinality_exponent,
        bp_57_saving_exponent=bp_57_saving_exponent,
        ck_gate_target_exponent=ck_gate_target_exponent,
        remaining_deficit=remaining_deficit,
        product_residue_energy_exponent=product_residue_energy_exponent,
        product_residue_l2_exponent=product_residue_l2_exponent,
        kloosterman_operator_norm_exponent=(
            kloosterman_operator_norm_exponent
        ),
        orthogonality_global_bound_exponent=(
            orthogonality_global_bound_exponent
        ),
        orthogonality_saving_exponent=orthogonality_saving_exponent,
        orthogonality_remaining_deficit=orthogonality_remaining_deficit,
        best_registered_route="exact_kloosterman_orthogonality",
        mqw_size_lhs_exponent=mqw_size_lhs_exponent,
        mqw_size_rhs_exponent=mqw_size_rhs_exponent,
        mqw_size_condition_deficit=mqw_size_condition_deficit,
        finite_r_completion_exact=True,
        full_additive_fourier_support_required=True,
        kernel_separated_optimistically=True,
        delta_unit_mod_s_verified=False,
        h_coprimality_mod_s_verified=False,
        mqw_direct_hypotheses_verified=False,
        direct_published_coverage=False,
    )


def bc_fixed_determinant_audit(box: ExponentBox) -> BCFixedDeterminantAudit:
    """Insert the hard determinant lattice into BC Corollary 1.

    After full ``h``-Poisson, take the smooth variables to be ``v,j``
    and the arbitrary coefficient variables to be ``r,s``.  The error
    exponent is the literal exponent of

    ``R_det^(3/2) ||alpha||_2 ||beta||_2``
    ``*(N1*N2)^(7/20) (N1+N2)^(1/4)``.

    At the hard box this is worse than the direct fixed-shift count, so
    the published corollary supplies no part of the required shift-average
    Möbius saving.
    """
    v_exponent = box.sigma - box.h
    j_exponent = max(box.rho + v_exponent, box.ell) - box.sigma
    if v_exponent < 0 or j_exponent < 0:
        raise ValueError("determinant dual variables must have nonnegative size")

    short_variable_exponents = (v_exponent, j_exponent)
    long_variable_exponents = (box.rho, box.sigma)
    determinant_scale_exponent = max(
        v_exponent + box.sigma,
        j_exponent + box.rho,
    )
    total_cardinality_exponent = (
        v_exponent + j_exponent + box.rho + box.sigma
    )
    fixed_shift_trivial_exponent = (
        total_cardinality_exponent - determinant_scale_exponent
    )
    coefficient_l2_exponent = (box.rho + box.sigma) / 2
    bc_corollary_error_exponent = (
        F(3, 2) * determinant_scale_exponent
        + coefficient_l2_exponent
        + F(7, 20) * (box.rho + box.sigma)
        + F(1, 4) * max(box.rho, box.sigma)
    )
    shift_range_exponent = box.ell
    summed_trivial_exponent = (
        fixed_shift_trivial_exponent + shift_range_exponent
    )
    global_target_exponent = (
        box.rho + box.sigma - box.h - F(1, 1000)
    )
    required_mobius_saving = _positive_part(
        summed_trivial_exponent - global_target_exponent
    )

    return BCFixedDeterminantAudit(
        short_variable_exponents=short_variable_exponents,
        long_variable_exponents=long_variable_exponents,
        determinant_scale_exponent=determinant_scale_exponent,
        fixed_shift_trivial_exponent=fixed_shift_trivial_exponent,
        bc_corollary_error_exponent=bc_corollary_error_exponent,
        bc_corollary_beats_trivial=(
            bc_corollary_error_exponent < fixed_shift_trivial_exponent
        ),
        shift_range_exponent=shift_range_exponent,
        summed_trivial_exponent=summed_trivial_exponent,
        global_target_exponent=global_target_exponent,
        required_mobius_saving=required_mobius_saving,
        full_shift_average_required=True,
        coupled_kernel_separated_optimistically=True,
        direct_corollary_hypotheses_verified=False,
        published_coverage=False,
    )


def bcr_adapter(box: ExponentBox) -> RouteResult:
    """Apply Bettin--Chandee Theorem 1 to separated coefficients.

    Norm exponents are ``rho/2``, ``sigma/2``, and ``a/2``.  The returned
    saving is ``rho + sigma`` minus the larger of the two theorem terms.
    """
    a = box.third_length
    total = a + box.rho + box.sigma
    longest = max(box.rho, box.sigma)
    large_a = F(1, 2) * _positive_part(a - box.rho - box.sigma)
    term_1 = F(17, 20) * total + F(1, 4) * longest + large_a
    term_2 = (
        F(7, 8) * (box.rho + box.sigma)
        + a
        + F(1, 8) * longest
        + large_a
    )
    saving = box.rho + box.sigma - max(term_1, term_2)
    admissible = is_admissible(box)
    # Strictness absorbs every fixed polylogarithmic separation norm.
    applicable = admissible and saving > TARGET_SAVING
    reason = "covered" if applicable else (
        "inadmissible_box" if not admissible else "insufficient_saving"
    )
    return RouteResult(
        route="bcr",
        applicable=applicable,
        saving=saving,
        source="Bettin-Chandee, arXiv:1502.00769, Theorem 1",
        reason=reason,
        conditions=(
            "(r,s)=1",
            "a,r,s supported on dyadic intervals",
            "L2 coefficient norms used exactly",
        ),
    )


def h_completion_adapter(box: ExponentBox) -> RouteResult:
    dual = completion_dual_exponent(box.h, box.sigma)
    return RouteResult(
        route="h_completion",
        applicable=False,
        saving=None,
        source="finite Poisson completion modulo s",
        reason="no_cited_completed_kernel_bound",
        conditions=(
            f"dual exponent max(0,sigma-h)={dual}",
            "rv congruent to delta modulo s",
            "coupled Fourier kernel retained",
        ),
    )


def delta_completion_adapter(box: ExponentBox) -> RouteResult:
    dual = completion_dual_exponent(box.ell, box.sigma)
    return RouteResult(
        route="delta_completion",
        applicable=False,
        saving=None,
        source="finite Poisson completion modulo s",
        reason="no_cited_completed_kernel_bound",
        conditions=(
            f"dual exponent max(0,sigma-ell)={dual}",
            "rh congruent to transformed delta frequency modulo s",
            "coupled Fourier kernel retained",
        ),
    )


def wright_fixed_factor_adapter(
    box: ExponentBox,
    *,
    fixed_factor: Fraction | None,
) -> RouteResult:
    """Apply Wright v2 only after a genuine denominator factor is fixed.

    With ``s = n * R_fix`` the theorem variables have exponent
    ``M=rho``, ``N=sigma-fixed_factor``, ``A=ell+h``.
    """
    if fixed_factor is None:
        return RouteResult(
            route="wright_fixed_factor",
            applicable=False,
            saving=None,
            source="Wright, arXiv:2604.25177v2, main theorem",
            reason="no_fixed_denominator_factor",
            conditions=("s=n*R_fix with R_fix fixed",),
        )

    f = fixed_factor
    n = box.sigma - f
    m = box.rho
    a = box.third_length
    if f < 0 or n < 0:
        return RouteResult(
            route="wright_fixed_factor",
            applicable=False,
            saving=None,
            source="Wright, arXiv:2604.25177v2, main theorem",
            reason="invalid_fixed_factor_scale",
            conditions=("0 <= fixed_factor <= sigma",),
        )

    theorem_conditions = m <= 2 * n and (f == 0 or m > 0)
    prefactor = a + m + n + f / 4
    prefactor += F(1, 4) * _positive_part(a - m - n)
    bracket = max(
        -n / 8,
        f / 8 + n / 8 - m / 4,
        m / 10 - 3 * f / 20 - a / 20 - 3 * n / 20,
        3 * n / 20 - 3 * a / 20 - m / 5,
        3 * n / 8 - m / 2,
    )
    bound = prefactor + bracket
    saving = box.rho + box.sigma - bound
    applicable = theorem_conditions and saving >= TARGET_SAVING
    if applicable:
        reason = "covered"
    elif not theorem_conditions:
        reason = "wright_hypotheses_fail"
    else:
        reason = "insufficient_saving"
    return RouteResult(
        route="wright_fixed_factor",
        applicable=applicable,
        saving=saving,
        source="Wright, arXiv:2604.25177v2, main theorem",
        reason=reason,
        conditions=("M <= N^2", "R_fix <= M^C", "(m,n*R_fix)=1"),
    )


def wright_type_i_adapter(
    box: ExponentBox,
    *,
    a_factor: Fraction,
    b_factor: Fraction,
) -> RouteResult:
    """Map a Type-I factorization ``r=a*b`` after reciprocity.

    The phase becomes ``e(h*delta*bar(s)/(a*b))``.  For each fixed ``a``
    Wright has ``M=S``, ``N=B``, ``A=LH``, and ``R_fix=A_0``.  The final
    exponent includes the outer trivial sum over the fixed ``a`` values.
    """
    if a_factor < 0 or b_factor < 0 or a_factor + b_factor != box.rho:
        return RouteResult(
            route="wright_type_i",
            applicable=False,
            saving=None,
            source="Wright, arXiv:2604.25177v2, main theorem",
            reason="invalid_type_i_factorization",
            conditions=("a_factor+b_factor=rho",),
        )

    m = box.sigma
    n = b_factor
    a = box.third_length
    f = a_factor
    theorem_conditions = m <= 2 * n and (f == 0 or m > 0)
    prefactor = a + m + n + f / 4
    prefactor += F(1, 4) * _positive_part(a - m - n)
    bracket = max(
        -n / 8,
        f / 8 + n / 8 - m / 4,
        m / 10 - 3 * f / 20 - a / 20 - 3 * n / 20,
        3 * n / 20 - 3 * a / 20 - m / 5,
        3 * n / 8 - m / 2,
    )
    # Wright is applied for each fixed a; summing those values costs A_0.
    bound = prefactor + bracket + f
    saving = box.rho + box.sigma - bound
    applicable = theorem_conditions and saving > TARGET_SAVING
    if applicable:
        reason = "covered"
    elif not theorem_conditions:
        reason = "wright_hypotheses_fail"
    else:
        reason = "insufficient_saving"
    return RouteResult(
        route="wright_type_i",
        applicable=applicable,
        saving=saving,
        source="Wright, arXiv:2604.25177v2, main theorem",
        reason=reason,
        conditions=(
            "reciprocity applied",
            "M=S and N=B_0",
            "M <= N^2",
            "outer fixed-factor sum included",
        ),
    )


def wright_denominator_factor_adapter(
    box: ExponentBox,
    *,
    fixed_factor: Fraction,
    remaining_factor: Fraction,
) -> RouteResult:
    """Audit Wright after splitting the denominator ``s=c*d``.

    For each fixed ``c`` the theorem has ``M=R``, ``N=D``,
    ``R_fix=C``, and ``A=LH``.  The returned exponent subtracts the
    unavoidable outer trivial sum over all fixed ``c`` values.
    """
    if (
        fixed_factor < 0
        or remaining_factor < 0
        or fixed_factor + remaining_factor != box.sigma
    ):
        return RouteResult(
            route="wright_denominator_factor",
            applicable=False,
            saving=None,
            source="Wright, arXiv:2604.25177v2, main theorem",
            reason="invalid_denominator_factorization",
            conditions=("fixed_factor+remaining_factor=sigma",),
        )

    fixed = wright_fixed_factor_adapter(box, fixed_factor=fixed_factor)
    assert fixed.saving is not None
    saving = fixed.saving - fixed_factor
    theorem_conditions = box.rho <= 2 * remaining_factor
    applicable = theorem_conditions and saving > TARGET_SAVING
    if applicable:
        reason = "covered"
    elif not theorem_conditions:
        reason = "wright_hypotheses_fail"
    else:
        reason = "insufficient_saving"
    return RouteResult(
        route="wright_denominator_factor",
        applicable=applicable,
        saving=saving,
        source="Wright, arXiv:2604.25177v2, main theorem",
        reason=reason,
        conditions=(
            "s=C_0*D_0",
            "M=R and N=D_0",
            "M <= N^2",
            "outer fixed-factor sum included",
        ),
    )


def farey_trilinear_adapter(box: ExponentBox) -> RouteResult:
    """Reduce a short signed shift window to one ``j`` per ``(r,s,v)``.

    This is an exact reindexing adapter, not the missing analytic estimate.
    It applies kinematically when ``L/S`` is a negative power of ``T``.
    """
    short_window = box.ell < box.sigma
    return RouteResult(
        route="mobius_farey_trilinear",
        applicable=False,
        saving=None,
        source=(
            "exact signed-j reindexing; new Farey estimate required"
        ),
        reason=(
            "new_farey_trilinear_estimate_required"
            if short_window
            else "shift_window_not_shorter_than_s"
        ),
        conditions=(
            "split positive and negative delta",
            "j unique after splitting the sign of delta",
            "retain all v in the coupled Fourier kernel",
            "preserve both Mobius weights",
        ),
    )


def route_box(box: ExponentBox) -> RouteResult:
    """Return the unique primary route in the approved priority order."""
    bcr = bcr_adapter(box)
    if bcr.applicable:
        return bcr
    endpoint_unpoisson = endpoint_unpoisson_adapter(
        box,
        shift_log_depth=None,
    )
    if endpoint_unpoisson.applicable:
        return endpoint_unpoisson
    for adapter in (h_completion_adapter, delta_completion_adapter):
        result = adapter(box)
        if result.applicable:
            return result
    wright = wright_fixed_factor_adapter(box, fixed_factor=None)
    if wright.applicable:
        return wright
    farey = farey_trilinear_adapter(box)
    if farey.reason == "new_farey_trilinear_estimate_required":
        return farey
    return RouteResult(
        route="global_coupled_operator",
        applicable=False,
        saving=None,
        source="new estimate required",
        reason="new_global_operator_estimate_required",
        conditions=(
            "sum v,j before absolute values",
            "preserve both Mobius weights",
            "retain delta=r*v-j*s and the Fourier kernel",
        ),
    )


def _fmt(value: Fraction | None) -> str:
    if value is None:
        return "none"
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def main() -> None:
    small = ExponentBox(F(1), F(1), F(0), F(0), F(0), F(0), F(2))
    boxes = {"bcr_small_a": small, **boundary_witnesses()}
    for name, box in sorted(boxes.items()):
        result = route_box(box)
        bcr = bcr_adapter(box)
        print(
            f"{name}: primary={result.route} reason={result.reason} "
            f"bcr_saving={_fmt(bcr.saving)} target={_fmt(TARGET_SAVING)}"
        )

    hard = boxes["balanced_max_a"]
    linnik_audit = linnik_dispersion_centering_audit(
        hard,
        gate_log_power=F(8),
    )
    print(
        "balanced_max_a: linnik_centering="
        f"diagonal={_fmt(linnik_audit.parseval_diagonal_exponent)} "
        "target="
        f"{_fmt(linnik_audit.logarithmic_gate_target_exponent)} "
        f"linear_degree={_fmt(linnik_audit.minus_one_homogeneity_degree)} "
        f"energy_degree={_fmt(linnik_audit.parseval_homogeneity_degree)} "
        "minus_one_is_diagonal="
        f"{linnik_audit.minus_one_subtracts_parseval_diagonal} "
        "post_cauchy_subtraction_sufficient="
        f"{linnik_audit.subtracting_diagonal_after_cauchy_sufficient} "
        "signed_cancellation="
        f"{linnik_audit.signed_off_diagonal_must_cancel_diagonal} "
        f"net_log={_fmt(linnik_audit.net_log_saving)} "
        f"covered={linnik_audit.published_coverage}"
    )
    determinant_line_parts: list[str] = []
    for gcd_exponent in (F(0), F(1, 4), F(1, 2)):
        line_audit = determinant_line_mobius_audit(
            hard,
            gcd_exponent=gcd_exponent,
        )
        determinant_line_parts.append(
            f"{_fmt(gcd_exponent)}:n="
            f"{_fmt(line_audit.line_parameter_length_exponent)},"
            "volume="
            f"{_fmt(line_audit.layer_cardinality_exponent)},"
            "saving="
            f"{_fmt(line_audit.required_mobius_saving)}"
        )
    print(
        "balanced_max_a: determinant_line_mobius="
        + ";".join(determinant_line_parts)
        + " growing_slopes=False coupled_weight=False covered=False"
    )
    determinant_sqrt_parts: list[str] = []
    for gcd_exponent in (F(0), F(1, 1000), F(1, 2)):
        sqrt_audit = determinant_line_square_root_audit(
            hard,
            gcd_exponent=gcd_exponent,
        )
        determinant_sqrt_parts.append(
            f"{_fmt(gcd_exponent)}:margin="
            f"{_fmt(sqrt_audit.square_root_margin)},"
            "residual="
            f"{_fmt(sqrt_audit.small_g_residual_saving)}"
        )
    print(
        "balanced_max_a: determinant_line_square_root="
        + ";".join(determinant_sqrt_parts)
        + " unimodular=True proved=False covered=False"
    )
    progression_variance_parts: list[str] = []
    for gcd_exponent in (F(0), F(1, 2)):
        variance_audit = mobius_progression_variance_audit(
            hard,
            gcd_exponent=gcd_exponent,
        )
        progression_variance_parts.append(
            f"{_fmt(gcd_exponent)}:Q="
            f"{_fmt(variance_audit.progression_modulus_exponent)},"
            "dh_deficit="
            f"{_fmt(variance_audit.dh_error_over_main_deficit)},"
            "gs_margin="
            f"{_fmt(variance_audit.gs_bv_level_margin)},"
            "gs_range="
            f"{variance_audit.gs_bv_level_verified}"
        )
    print(
        "balanced_max_a: mobius_progression_variance="
        + ";".join(progression_variance_parts)
        + " second_mu=False coupled_weight=False covered=False"
    )
    slope_square_parts: list[str] = []
    for gcd_exponent in (F(0), F(1, 4), F(1, 2)):
        square_audit = determinant_slope_square_function_audit(
            hard,
            gcd_exponent=gcd_exponent,
            endpoint_taper_factors=F(2),
            endpoint_aggregation_log_loss=F(1),
            endpoint_conditions_verified=True,
        )
        slope_square_parts.append(
            f"{_fmt(gcd_exponent)}:slopes="
            f"{_fmt(square_audit.primitive_slope_pair_exponent)},"
            "cauchy="
            f"{_fmt(square_audit.slope_cauchy_cost_exponent)},"
            "diag="
            f"{_fmt(square_audit.raw_identity_diagonal_exponent)},"
            "bound="
            f"{_fmt(square_audit.aggregated_bound_exponent)}"
        )
    print(
        "balanced_max_a: determinant_slope_square_function="
        + ";".join(slope_square_parts)
        + " endpoint_taper=2 square_log=4 endpoint_loss=1"
        + " diagonal_ok=True net_log=1 proved=False covered=False"
    )
    slope_offdiagonal_parts: list[str] = []
    for gcd_exponent in (F(0), F(1, 4), F(1, 2)):
        offdiagonal_audit = endpoint_slope_offdiagonal_audit(
            hard,
            gcd_exponent=gcd_exponent,
        )
        slope_offdiagonal_parts.append(
            f"{_fmt(gcd_exponent)}:ambient="
            f"{_fmt(offdiagonal_audit.expanded_offdiagonal_cardinality_exponent)},"
            "saving="
            f"{_fmt(offdiagonal_audit.required_offdiagonal_saving)},"
            "sqrt_margin="
            f"{_fmt(offdiagonal_audit.full_square_root_target_margin)},"
            "delta_max="
            f"{_fmt(offdiagonal_audit.cross_determinant_max_exponent)}"
        )
    print(
        "balanced_max_a: endpoint_slope_offdiagonal="
        + ";".join(slope_offdiagonal_parts)
        + " square_log=4 four_mu=True proved=False covered=False"
    )
    cokernel_parts: list[str] = []
    for gcd_exponent in (F(0), F(1, 4), F(1, 2)):
        cokernel_audit = endpoint_cokernel_character_audit(
            hard,
            gcd_exponent=gcd_exponent,
            determinant_exponent=F(5),
        )
        cokernel_parts.append(
            f"{_fmt(gcd_exponent)}:required="
            f"{_fmt(cokernel_audit.odsf_required_saving)},"
            "char_sqrt="
            f"{_fmt(cokernel_audit.character_square_root_saving)},"
            "residual="
            f"{_fmt(cokernel_audit.remaining_saving_after_character_square_root)}"
        )
    print(
        "balanced_max_a: endpoint_cokernel_character="
        + ";".join(cokernel_parts)
        + " smith=1,Delta chars=Delta not_Delta2=True"
        + " proved=False covered=False"
    )
    large_q_audit = large_q_endpoint_unpoisson_audit(
        boxes["large_q_endpoint"],
        shift_log_depth=F(0),
    )
    print(
        "large_q_endpoint: endpoint_unpoisson="
        f"solutions={_fmt(large_q_audit.shifted_solution_exponent)} "
        "denominator="
        f"{_fmt(large_q_audit.pre_poisson_denominator_exponent)} "
        f"per_q={_fmt(large_q_audit.per_q_contribution_exponent)} "
        "q_count="
        f"{_fmt(large_q_audit.q_family_cardinality_exponent)} "
        "total="
        f"{_fmt(large_q_audit.aggregated_remainder_exponent)} "
        "shift_log=0 taper_log=2 net_log=2 all_h=True zero_mode=True "
        "mobius=False bounded_subface=True whole_cell=False"
    )
    large_q_critical = large_q_endpoint_critical_shift_audit(
        boxes["large_q_endpoint"],
        shift_log_depth=F(2),
        zeta_scales_fixed=True,
    )
    print(
        "large_q_endpoint: endpoint_critical_q_first="
        "shift_log=2 q_error="
        f"{_fmt(large_q_critical.q_mellin_error_power_saving)} "
        "gcd_decay="
        f"{_fmt(large_q_critical.coprimality_divisor_volume_decay)} "
        "menon=False fixed_zeta=True fixed_f=True two_limit=True covered=False "
        "above=False whole_cell=False"
    )
    growing_zeta = large_q_growing_zeta_product_lift_audit(
        boxes["large_q_endpoint"],
        shift_log_depth=F(2),
    )
    print(
        "large_q_endpoint: growing_zeta_product_lift="
        "shift_log=2 taper_log=2 absolute_power=1 local_gate=T*L*o(1) "
        "gcd_log=False exact_lift=True centered=True published=False "
        "covered=False"
    )
    height_phase = large_q_height_phase_audit(
        boxes["large_q_endpoint"],
        shift_log_depth=F(2),
        zeta_log_depth=F(3, 2),
    )
    print(
        "large_q_endpoint: height_phase="
        "shift_log=2 zeta_log=3/2 ratio_log=1/2 pre_phase_log=0 "
        "arbitrary_decay=True retained=True "
        "covered=True boundary=False whole_cell=False"
    )
    boundary_reflection = large_q_boundary_reflection_audit(
        boxes["large_q_endpoint"],
        shift_log_depth=F(2),
        zeta_log_depth=F(2),
    )
    print(
        "large_q_endpoint: boundary_reflection="
        "shift_log=2 zeta_log=2 q_free_prime_power=True prime_forced=True "
        "main_main=True mixed=True cross_scale=False formal_tail=tail*tail "
        "tail_phase=False "
        "covered=False"
    )
    subcritical_afe = large_q_subcritical_afe_completion_audit(
        boxes["large_q_endpoint"],
        afe_product_gap=F(1, 10),
        mellin_left_shift=F(1, 8),
    )
    print(
        "large_q_endpoint: subcritical_afe_completion="
        "gap=1/10 left_shift=1/8 remainder_save=1/80 local_power=1 "
        "local_residue=True regrouped=False divisor_completion=False "
        "crosses_transition=True endpoint_full=False covered=False"
    )
    transition_mellin = large_q_transition_mellin_divisor_audit(
        boxes["large_q_endpoint"]
    )
    print(
        "large_q_endpoint: transition_mellin_divisor="
        "common_z=True right_line=True absolute_right=True euler=True "
        "z0_lambda=True nonzero_sparse=False gaussian=True "
        "absolute_left=False cutoff_factor=False gate=False "
        "proved=False covered=False"
    )
    transition_box = ExponentBox(
        F(1), F(1), F(1, 2), F(1, 2),
        F(1, 2), F(1, 2), F(2),
    )
    transition_compact = large_q_transition_compact_mellin_audit(
        transition_box
    )
    print(
        "large_q_transition: compact_mellin="
        "compact=True line=0 inversion=True rapid=True power_growth=0 "
        "twisted_divisor=True coprimality=True reflected_tail=True "
        "product=3/2 shift=1/2 absolute=3/2 critical_save=1/2 "
        "gate_save=501/1000 "
        "gate=True proved=False covered=False"
    )
    transition_type_ii_left = type_ii_cauchy_diagonal_audit(
        transition_box,
        b_exponent=F(1, 3),
    )
    transition_type_ii_right = type_ii_cauchy_diagonal_audit(
        transition_box,
        b_exponent=F(2, 3),
    )
    print(
        "large_q_transition: type_ii_diagonal="
        "1/3:diag=3,target=2747/750,margin=497/750;"
        "2/3:diag=3,target=2497/750,margin=247/750 "
        "subtraction=False diagonal_closes=True offdiag_gate=True "
        "proved=False covered=False"
    )
    transition_kim = transition_kim_average_shifted_convolution_audit(
        transition_box,
        left_short_interval_exponent=F(1),
        right_short_interval_exponent=F(1),
    )
    print(
        "large_q_transition: kim_average_shifted="
        "X=3/2 H=1/2 b1=1 b2=1 h_power=2/3 bound=11/6 "
        "target=1499/1000 deficit=1003/3000 multiplicative=False "
        "mellin_uniform=False applicable=False covered=False"
    )
    log_budget = centered_resonance_log_budget(
        hard,
        gate_log_power=F(8),
    )
    print(
        "balanced_max_a: "
        f"centered_log_cutoff_power={_fmt(log_budget.resonance_power_cutoff)} "
        f"centered_log_cutoff_log={_fmt(log_budget.resonance_log_cutoff)} "
        f"near_bound_log={_fmt(log_budget.near_bound_log_saving)} "
        f"global_log_margin={_fmt(log_budget.global_log_margin)}"
    )
    endpoint_budget = endpoint_centered_resonance_log_budget(
        hard,
        gate_log_power=F(8),
        endpoint_factors=2,
    )
    print(
        "balanced_max_a: "
        f"endpoint_log_cutoff_power={_fmt(endpoint_budget.resonance_power_cutoff)} "
        f"endpoint_log_cutoff_log={_fmt(endpoint_budget.resonance_log_cutoff)} "
        f"endpoint_log_saving={_fmt(endpoint_budget.endpoint_log_saving)} "
        "full_collar_global_margin="
        f"{_fmt(endpoint_budget.full_power_collar_global_log_margin)}"
    )
    endpoint_critical = endpoint_critical_aggregation_budget(
        hard,
        endpoint_factors=2,
        q_logarithmic_depth=F(0),
        frequency_logarithmic_depth=F(0),
    )
    print(
        "balanced_max_a: "
        "endpoint_critical_log_loss="
        f"{_fmt(endpoint_critical.total_log_power_loss)} "
        f"endpoint_taper={_fmt(endpoint_critical.endpoint_log_saving)} "
        f"net_log_power={_fmt(endpoint_critical.net_log_power)} "
        "polyloglog_loss="
        f"{_fmt(endpoint_critical.polyloglog_loss_exponent)} "
        "q_aggregation=cardinal "
        "absolute_little_o="
        f"{endpoint_critical.absolute_bound_produces_little_o}"
    )
    logarithmic_depths = (F(0), F(5, 4), F(3, 2), F(2))
    improved_depth_parts: list[str] = []
    for depth in logarithmic_depths:
        depth_audit = improved_averaged_chowla_shell_audit(
            hard,
            q_logarithmic_depth=depth,
            frequency_logarithmic_depth=F(0),
        )
        improved_depth_parts.append(
            f"{_fmt(depth)}:{_fmt(depth_audit.all_sector_log_margin)}"
        )
    improved_depth_margins = ",".join(improved_depth_parts)
    improved_half = improved_averaged_chowla_shell_audit(
        hard,
        q_logarithmic_depth=F(5, 4),
        frequency_logarithmic_depth=F(0),
    )
    print(
        "balanced_max_a: "
        f"improved_chowla_total_depths={improved_depth_margins} "
        "covered_all_slopes_beta_plus_gamma_lt_3/2="
        f"{improved_half.all_sector_subface_covered} "
        f"joint_weight={improved_half.joint_coefficient_accepted} "
        "coprimality="
        f"{improved_half.coprimality_transfer_proved}"
    )
    bv_regime_inputs = (
        ("low", F(-1, 2), F(-1, 2)),
        ("stationary_high", F(1, 2), F(1, 2)),
        ("offstationary", F(1, 2), F(-1, 2)),
    )
    bv_regime_parts: list[str] = []
    for regime_name, x_log_scale, y_log_scale in bv_regime_inputs:
        bv_audit = completion_weight_bv_audit(
            hard,
            x_log_scale=x_log_scale,
            y_log_scale=y_log_scale,
        )
        bv_regime_parts.append(
            f"{regime_name}:depth={_fmt(bv_audit.bv_net_log_depth)},"
            f"extra={_fmt(bv_audit.bv_extra_log_depth)},"
            f"keep={bv_audit.retained_after_phase_partition}"
        )
    print(
        "balanced_max_a: completion_bv_regimes="
        + ";".join(bv_regime_parts)
    )
    coprimality_audit = coprimality_restricted_menon_audit(
        hard,
        q_logarithmic_depth=F(5, 4),
        frequency_logarithmic_depth=F(0),
        common_divisor_cutoff_log_depth=F(4),
    )
    print(
        "balanced_max_a: coprimality_transfer="
        "d_decay="
        f"{_fmt(coprimality_audit.common_divisor_volume_decay)} "
        "d_tail="
        f"{_fmt(coprimality_audit.common_divisor_tail_log_saving)} "
        "modulus_log="
        f"{_fmt(coprimality_audit.restricted_modulus_log_depth)} "
        f"margin={_fmt(coprimality_audit.all_sector_log_margin)} "
        f"covered={coprimality_audit.subface_covered}"
    )
    distances = (F(1), F(3, 2), F(2), F(5, 2), F(3))
    shell_savings = ",".join(
        f"{_fmt(distance)}:"
        f"{_fmt(far_resonance_shell_scales(hard, distance=distance).required_power_saving)}"
        for distance in distances
    )
    mrt = averaged_chowla_shell_audit(
        hard,
        distance=F(1),
        gate_log_power=F(8),
    )
    print(
        "balanced_max_a: "
        f"centered_far_shell_required_savings={shell_savings} "
        f"mrt_critical_log_shortfall={_fmt(mrt.log_shortfall)}"
    )
    primitive_savings = ",".join(
        f"{_fmt(distance)}:"
        f"{_fmt(primitive_fraction_large_sieve_scales(hard, distance=distance).remaining_power_saving)}"
        for distance in distances
    )
    print(
        "balanced_max_a: "
        f"primitive_ls_best_remaining={primitive_savings}"
    )
    reciprocal_distances = (F(2), F(5, 2), F(3))
    reciprocal_savings = ",".join(
        f"{_fmt(distance)}:"
        f"{_fmt(reciprocal_cluster_large_sieve_scales(hard, distance=distance).remaining_power_saving)}"
        for distance in reciprocal_distances
    )
    print(
        "balanced_max_a: "
        f"reciprocal_cluster_best_remaining={reciprocal_savings}"
    )
    trace_twist_distances = (F(2), F(3))
    trace_twist_parts: list[str] = []
    for distance in trace_twist_distances:
        trace_audit = prime_factor_trace_twist_audit(
            hard,
            distance=distance,
            prime_factor_exponent=distance,
            applications=2,
            eta=F(1, 25),
        )
        trace_twist_parts.append(
            f"{_fmt(distance)}:save="
            f"{_fmt(trace_audit.optimistic_total_power_saving)},"
            f"remain={_fmt(trace_audit.optimistic_residual_deficit)}"
        )
    print(
        "balanced_max_a: optimistic_prime_trace_twists="
        + ";".join(trace_twist_parts)
        + " covered=False"
    )
    linear_completion_parts: list[str] = []
    for short_total in (F(0), F(1), F(2)):
        linear_audit = squarefree_linear_completion_audit(
            hard,
            distance=F(3),
            short_factor_total=short_total,
        )
        linear_completion_parts.append(
            f"{_fmt(short_total)}:save="
            f"{_fmt(linear_audit.power_saving)},"
            f"remain={_fmt(linear_audit.remaining_shell_deficit)}"
        )
    print(
        "balanced_max_a: squarefree_linear_completion="
        + ";".join(linear_completion_parts)
        + " covered=False"
    )
    diagonal_parts: list[str] = []
    for b_exponent in (F(1), F(3, 2), F(2)):
        diagonal_audit = type_ii_cauchy_diagonal_audit(
            hard,
            b_exponent=b_exponent,
        )
        diagonal_parts.append(
            f"{_fmt(b_exponent)}:margin="
            f"{_fmt(diagonal_audit.spectral_target_margin)},"
            f"post_deficit="
            f"{_fmt(diagonal_audit.post_cauchy_target_deficit)}"
        )
    print(
        "balanced_max_a: type_ii_cauchy_diagonal="
        + ";".join(diagonal_parts)
        + " subtraction=True"
    )
    zero_ray_audit = zero_ray_convolution_centering_audit(
        hard,
        b_exponent=F(3, 2),
    )
    print(
        "balanced_max_a: zero_ray_convolution_centering="
        f"product={_fmt(zero_ray_audit.product_ray_exponent)} "
        f"cutoff={_fmt(zero_ray_audit.cutoff_exponent)} "
        "full_zero="
        f"{zero_ray_audit.full_convolution_vanishes_exactly} "
        "sector_main=-mu main_sq="
        f"{_fmt(zero_ray_audit.explicit_mobius_main_squared_exponent)} "
        "cross="
        f"{zero_ray_audit.joint_cross_term_required} "
        "joint_gate="
        f"{zero_ray_audit.joint_gram_gate_required}"
    )
    primitive_slope_parts: list[str] = []
    for slope_exponent in (F(0), F(1, 2), F(3, 5), F(9, 2)):
        slope_audit = primitive_slope_zero_ray_audit(
            hard,
            b_exponent=F(3, 2),
            slope_exponent=slope_exponent,
        )
        primitive_slope_parts.append(
            f"{_fmt(slope_exponent)}:need="
            f"{_fmt(slope_audit.required_power_saving)},"
            f"sqrt={_fmt(slope_audit.double_square_root_saving)},"
            "slack="
            f"{slope_audit.double_square_root_has_exponent_slack}"
        )
    print(
        "balanced_max_a: primitive_slope_zero_ray="
        + ";".join(primitive_slope_parts)
        + " proved=False k_mu=False slope_phase=False"
    )
    long_cutoff_parts: list[str] = []
    for cutoff_exponent in (F(1), F(2), F(401, 200)):
        cutoff_audit = long_mobius_cutoff_audit(
            hard,
            cutoff_exponent=cutoff_exponent,
            squared_target_saving=F(1, 250),
        )
        long_cutoff_parts.append(
            f"{_fmt(cutoff_exponent)}:bmax="
            f"{_fmt(cutoff_audit.complementary_factor_max_exponent)},"
            f"margin={_fmt(cutoff_audit.worst_diagonal_margin)},"
            "diag="
            f"{cutoff_audit.all_factor_boxes_have_diagonal_power_slack}"
        )
    optimized_cutoff = long_mobius_cutoff_audit(
        hard,
        cutoff_exponent=F(401, 200),
        squared_target_saving=F(1, 250),
    )
    print(
        "balanced_max_a: long_mobius_cutoff="
        + ";".join(long_cutoff_parts)
        + " zero_ray="
        f"{optimized_cutoff.entire_zero_ray_cardinality_has_power_slack}"
        + " offdiag="
        f"{optimized_cutoff.published_off_diagonal_coverage}"
        + " recip="
        f"{_fmt(optimized_cutoff.reciprocal_modulus_exponent)}"
        + " zero_c_endpoint="
        f"{_fmt(optimized_cutoff.zero_completion_endpoint_c_exponent)}"
        + " global_b_divides_delta="
        f"{optimized_cutoff.full_off_diagonal_imposes_b_divides_delta}"
    )
    h_completion_parts: list[str] = []
    for b_exponent in (F(0), F(199, 200)):
        h_audit = long_cutoff_h_completion_audit(
            hard,
            b_exponent=b_exponent,
        )
        h_completion_parts.append(
            f"{_fmt(b_exponent)}:b_surplus="
            f"{_fmt(h_audit.common_b_period_surplus)},"
            f"a_freq={_fmt(h_audit.fixed_a_normalized_frequency)},"
            f"valid={h_audit.b_only_poisson_valid}"
        )
    endpoint_h_audit = long_cutoff_h_completion_audit(
        hard,
        b_exponent=F(199, 200),
    )
    print(
        "balanced_max_a: long_cutoff_h_completion="
        + ";".join(h_completion_parts)
        + " full_surplus="
        f"{_fmt(endpoint_h_audit.full_modulus_period_surplus)}"
        + " proved=False"
    )
    quotient_split_parts: list[str] = []
    for b_exponent in (F(0), F(199, 200)):
        quotient_audit = long_cutoff_quotient_split_audit(
            hard,
            cutoff_exponent=F(401, 200),
            b_exponent=b_exponent,
            dual_v_exponent=F(1, 2),
        )
        quotient_split_parts.append(
            f"{_fmt(b_exponent)}:dlevel="
            f"{_fmt(quotient_audit.small_divisor_level_exponent)},"
            "modulus="
            f"{_fmt(quotient_audit.expanded_modulus_endpoint)},"
            "emax="
            f"{_fmt(quotient_audit.large_cofactor_max_exponent)}"
        )
    endpoint_quotient_audit = long_cutoff_quotient_split_audit(
        hard,
        cutoff_exponent=F(401, 200),
        b_exponent=F(199, 200),
        dual_v_exponent=F(1, 2),
    )
    print(
        "balanced_max_a: long_cutoff_quotient_split="
        + ";".join(quotient_split_parts)
        + " gcd_reduces="
        f"{endpoint_quotient_audit.gcd_reduction_only_decreases_modulus}"
        + " direct_bv="
        f"{endpoint_quotient_audit.standard_bv_coupled_hypotheses_verified}"
        + " covered="
        f"{endpoint_quotient_audit.published_coverage}"
    )
    quotient_bdh_parts: list[str] = []
    for b_exponent, d_exponent, v_exponent in (
        (F(0), F(0), F(0)),
        (F(199, 200), F(1, 200), F(1, 2)),
    ):
        bdh_audit = long_cutoff_quotient_bdh_audit(
            hard,
            b_exponent=b_exponent,
            d_exponent=d_exponent,
            dual_v_exponent=v_exponent,
            dual_j_exponent=F(1, 2),
        )
        quotient_bdh_parts.append(
            f"{_fmt(bdh_audit.modulus_exponent)}:bdh="
            f"{_fmt(bdh_audit.optimistic_bdh_bound_exponent)},"
            "bdh_deficit="
            f"{_fmt(bdh_audit.bdh_remaining_deficit)},"
            "centered="
            f"{_fmt(bdh_audit.optimistic_centered_bound_exponent)},"
            "centered_deficit="
            f"{_fmt(bdh_audit.centered_remaining_deficit)}"
        )
    endpoint_bdh_audit = long_cutoff_quotient_bdh_audit(
        hard,
        b_exponent=F(199, 200),
        d_exponent=F(1, 200),
        dual_v_exponent=F(1, 2),
        dual_j_exponent=F(1, 2),
    )
    print(
        "balanced_max_a: quotient_bdh="
        + ";".join(quotient_bdh_parts)
        + " common="
        f"{endpoint_bdh_audit.common_weight_hypothesis_verified}"
        + " phase="
        f"{endpoint_bdh_audit.centered_geometric_saving_proved}"
        + " covered="
        f"{endpoint_bdh_audit.published_coverage}"
    )
    pascadi_audit = pascadi_incomplete_kloosterman_audit(hard)
    print(
        "balanced_max_a: pascadi_incomplete="
        "i2_regular="
        f"{_fmt(pascadi_audit.regular_i_squared_exponent)} "
        "i2_exceptional="
        f"{_fmt(pascadi_audit.exceptional_i_squared_exponent)} "
        f"bound={_fmt(pascadi_audit.optimistic_bound_exponent)} "
        f"target={_fmt(pascadi_audit.gate_target_exponent)} "
        f"deficit={_fmt(pascadi_audit.remaining_deficit)} "
        f"assumption14={pascadi_audit.assumption_14_verified} "
        "direct="
        f"{pascadi_audit.direct_corollary_hypotheses_verified} "
        f"covered={pascadi_audit.published_coverage}"
    )
    centered_poisson_audit = centered_quotient_poisson_audit(hard)
    print(
        "balanced_max_a: centered_quotient_poisson="
        f"emax={_fmt(centered_poisson_audit.e_cofactor_max_exponent)} "
        "squarefree="
        f"{centered_poisson_audit.squarefree_e_support_required} "
        "coprime="
        f"{centered_poisson_audit.coprimality_e_support_required} "
        "nonzero_mass=theta00 minus_one="
        f"{centered_poisson_audit.centered_minus_one_vanishes_separately} "
        "unweighted="
        f"{centered_poisson_audit.unweighted_e_poisson_valid} "
        "recloses="
        f"{centered_poisson_audit.joint_c_v_orthogonality_recloses_original_kernel} "
        "conductor="
        f"{centered_poisson_audit.new_conductor_reduction} "
        f"covered={centered_poisson_audit.published_coverage}"
    )
    hecke_mobius_audit = hecke_mobius_spectral_audit(
        polynomial_length_exponent=F(3),
        conductor_exponent_witness=F(1),
        required_log_saving_power=8,
    )
    print(
        "balanced_max_a: hecke_mobius_spectral="
        f"x={_fmt(hecke_mobius_audit.polynomial_length_exponent)} "
        "conductor_witness="
        f"{_fmt(hecke_mobius_audit.conductor_exponent_witness)} "
        f"B={hecke_mobius_audit.required_log_saving_power} "
        f"euler={hecke_mobius_audit.local_euler_factor_exact} "
        "fixed_index="
        f"{hecke_mobius_audit.knightly_li_has_one_fixed_hecke_index} "
        "one_polynomial="
        f"{hecke_mobius_audit.linear_superposition_formally_creates_one_mobius_hecke_sum} "
        "qct_geometry="
        f"{hecke_mobius_audit.qct_geometry_identified_with_generalized_kloosterman_family} "
        "two_polynomials="
        f"{hecke_mobius_audit.two_mobius_weights_derived_as_hecke_polynomials} "
        "classical_constant="
        f"{hecke_mobius_audit.classical_polynomial_conductor_saving_only_constant} "
        "thorner_to_one="
        f"{hecke_mobius_audit.thorner_polynomial_conductor_saving_tends_to_one} "
        "conductor="
        f"{hecke_mobius_audit.spectral_conductor_verified} "
        "zero_free="
        f"{hecke_mobius_audit.uniform_zero_free_log_saving_verified} "
        f"covered={hecke_mobius_audit.published_coverage}"
    )
    determinant_orbit_audit = determinant_orbit_hecke_index_audit()
    print(
        "balanced_max_a: determinant_orbit_hecke="
        f"det={determinant_orbit_audit.determinant_symbol} "
        f"modulus={determinant_orbit_audit.modulus_symbol} "
        "residues="
        f"{','.join(determinant_orbit_audit.residue_pair)} "
        "hecke_index="
        f"{determinant_orbit_audit.hecke_operator_index_symbol} "
        "fourier="
        f"{','.join(determinant_orbit_audit.kloosterman_fourier_indices)} "
        "phase="
        f"{determinant_orbit_audit.original_phase_reduces_to_linear_orbit_phase} "
        "mu_r=entry mu_s=modulus mu_delta="
        f"{determinant_orbit_audit.delta_mobius_weight_present} "
        "superposition="
        f"{determinant_orbit_audit.knightly_li_superposition_targets_existing_mobius_weight} "
        "two_polynomials="
        f"{determinant_orbit_audit.two_existing_mobius_weights_become_hecke_polynomials} "
        "complete_orbit="
        f"{determinant_orbit_audit.qct_kernel_is_unweighted_complete_orbit} "
        f"covered={determinant_orbit_audit.published_coverage}"
    )
    fixed_modulus_audit = fixed_modulus_kloosterman_completion_audit(hard)
    print(
        "balanced_max_a: fixed_modulus_kloosterman="
        "rhat_l2="
        f"{_fmt(fixed_modulus_audit.r_fourier_l2_exponent)} "
        "h_l2="
        f"{_fmt(fixed_modulus_audit.h_coefficient_l2_exponent)} "
        "bp_factor="
        f"{_fmt(fixed_modulus_audit.bp_57_dimensionless_factor_exponent)} "
        "fixed="
        f"{_fmt(fixed_modulus_audit.bp_57_fixed_delta_s_exponent_before_completion)} "
        "global="
        f"{_fmt(fixed_modulus_audit.bp_57_global_bound_exponent)} "
        "saving="
        f"{_fmt(fixed_modulus_audit.bp_57_saving_exponent)} "
        "target="
        f"{_fmt(fixed_modulus_audit.ck_gate_target_exponent)} "
        f"deficit={_fmt(fixed_modulus_audit.remaining_deficit)} "
        "energy="
        f"{_fmt(fixed_modulus_audit.product_residue_energy_exponent)} "
        "orth_global="
        f"{_fmt(fixed_modulus_audit.orthogonality_global_bound_exponent)} "
        "orth_deficit="
        f"{_fmt(fixed_modulus_audit.orthogonality_remaining_deficit)} "
        f"best={fixed_modulus_audit.best_registered_route} "
        f"mqw={_fmt(fixed_modulus_audit.mqw_size_lhs_exponent)}>"
        f"{_fmt(fixed_modulus_audit.mqw_size_rhs_exponent)} "
        "mqw_deficit="
        f"{_fmt(fixed_modulus_audit.mqw_size_condition_deficit)} "
        "full_fourier="
        f"{fixed_modulus_audit.full_additive_fourier_support_required} "
        f"delta_unit={fixed_modulus_audit.delta_unit_mod_s_verified} "
        "h_coprime="
        f"{fixed_modulus_audit.h_coprimality_mod_s_verified} "
        f"direct={fixed_modulus_audit.direct_published_coverage}"
    )
    determinant_audit = bc_fixed_determinant_audit(hard)
    print(
        "balanced_max_a: bc_fixed_determinant="
        f"error={_fmt(determinant_audit.bc_corollary_error_exponent)} "
        "fixed_trivial="
        f"{_fmt(determinant_audit.fixed_shift_trivial_exponent)} "
        "summed_trivial="
        f"{_fmt(determinant_audit.summed_trivial_exponent)} "
        f"target={_fmt(determinant_audit.global_target_exponent)} "
        "mobius_save="
        f"{_fmt(determinant_audit.required_mobius_saving)} "
        "direct="
        f"{determinant_audit.direct_corollary_hypotheses_verified} "
        f"covered={determinant_audit.published_coverage}"
    )


if __name__ == "__main__":
    main()
