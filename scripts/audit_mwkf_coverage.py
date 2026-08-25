#!/usr/bin/env python3
"""Exact-rational adapters for published MWKF core estimates.

The adapters only certify a route when every encoded hypothesis and the
fixed target saving hold.  A rejected result is a coverage witness, not a
claim that the corresponding theorem is false.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import gcd, isqrt
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
class TransitionTypeIIDeterminantAudit:
    b_exponent: Fraction
    a_exponent: Fraction
    numerator_product_exponent: Fraction
    factorized_y_exponent: Fraction
    full_zero_determinant_exponent: Fraction
    square_target_exponent: Fraction
    full_zero_determinant_margin: Fraction
    nonzero_determinant_max_exponent: Fraction
    reciprocalized_y_modulus_exponent: Fraction
    y_modulus_square_root_exponent: Fraction
    b_below_y_modulus_square_root_gap: Fraction
    y_modulus_completed_dual_length_exponent: Fraction
    full_zero_determinant_separate_majorant_closes: bool
    y_modulus_fixed_b_interval_reaches_square_root: bool
    y_modulus_single_completion_supplies_saving: bool
    nonzero_determinant_gate_required: bool
    nonzero_determinant_estimate_proved: bool
    published_coverage: bool


@dataclass(frozen=True)
class TransitionTypeIILcmCompletionAudit:
    b_exponent: Fraction
    gcd_s_exponent: Fraction
    lcm_modulus_exponent: Fraction
    modulus_square_root_exponent: Fraction
    b_below_square_root_gap: Fraction
    b_above_square_root_surplus: Fraction
    completed_dual_length_exponent: Fraction
    blomer_pascadi_dimensionless_loss: Fraction
    nonzero_cardinality_exponent: Fraction
    square_target_exponent: Fraction
    required_total_saving: Fraction
    single_b_weil_saving: Fraction
    remaining_saving_after_single_b_completion: Fraction
    original_phase_compresses_to_lcm: bool
    fixed_b_completion_has_kinematic_saving: bool
    fixed_b_completion_closes_square_target: bool
    squarefree_coprime_b_weight_is_smooth: bool
    blomer_pascadi_adapter_closes: bool
    published_coverage: bool


@dataclass(frozen=True)
class TransitionLongCutoffMobiusTraceAudit:
    cutoff_gap_exponent: Fraction
    cutoff_exponent: Fraction
    b_exponent: Fraction
    a_exponent: Fraction
    short_reflected_divisor_exponent: Fraction
    trace_modulus_exponent: Fraction
    trace_length_over_sqrt_modulus_margin: Fraction
    ambient_unsquared_exponent: Fraction
    fixed_type_ii_target_exponent: Fraction
    remaining_power_deficit_after_two_log_savings: Fraction
    squarefree_reflection_identity_exact: bool
    published_theorem_requires_prime_modulus: bool
    all_actual_moduli_are_prime: bool
    nonexceptional_trace_hypothesis_uniform: bool
    two_logarithmic_savings_close_power_target: bool
    published_coverage: bool
    source: str


@dataclass(frozen=True)
class TransitionReciprocalClusterClosureAudit:
    distance_max: Fraction
    numerator_product_exponent: Fraction
    clustered_large_sieve_exponent: Fraction
    raw_gate_exponent: Fraction
    remaining_power_deficit: Fraction
    endpoint_taper_log_saving: Fraction
    product_coefficient_l2_log_loss: Fraction
    dyadic_distance_log_loss: Fraction
    dimensionless_kernel_log_loss: Fraction
    net_log_saving: Fraction
    global_remainder_power_exponent: Fraction
    reciprocity_cluster_identity_exact: bool
    product_coefficient_energy_bound_proved: bool
    fixed_transition_kernel_has_uniform_seminorms: bool
    low_difference_union_covered: bool
    whole_transition_face_covered: bool
    residual_distance_open_interval: tuple[Fraction, Fraction]
    residual_required_saving_at_top: Fraction


@dataclass(frozen=True)
class TransitionFarShellMobiusGateAudit:
    distance: Fraction
    shifted_variable_exponent: Fraction
    modulus_exponent: Fraction
    product_frequency_exponent: Fraction
    current_cluster_bound_exponent: Fraction
    fixed_gate_target_exponent: Fraction
    required_new_mobius_saving: Fraction
    fkm_eta: Fraction
    optimistic_fkm_applications: int
    optimistic_fkm_total_saving: Fraction
    residual_after_optimistic_fkm: Fraction
    left_mobius_weight_retained: bool
    right_mobius_weight_retained: bool
    coupled_kernel_retained: bool
    uniform_prime_factor_hypothesis: bool
    nonzero_prime_frequency_uniform: bool
    joint_cofactor_hypothesis: bool
    new_joint_two_mobius_estimate_required: bool
    estimate_proved: bool
    published_coverage: bool


@dataclass(frozen=True)
class TransitionFarShellFactorBoxAudit:
    distance: Fraction
    mobius_cutoff_exponent: Fraction
    type_split_exponent: Fraction
    b_exponent: Fraction
    b_exponent_range: tuple[Fraction, Fraction]
    a_exponent: Fraction
    shifted_equation_is_exact: bool
    reciprocal_phase_reindexed_exactly: bool
    unsquared_cluster_bound_exponent: Fraction
    unsquared_fixed_target_exponent: Fraction
    unsquared_required_saving: Fraction
    identity_diagonal_exponent: Fraction
    type_ii_square_target_exponent: Fraction
    identity_diagonal_margin: Fraction
    identity_diagonal_closes: bool
    nonzero_joint_gram_estimate_required: bool
    nonzero_joint_gram_estimate_proved: bool
    published_coverage: bool


@dataclass(frozen=True)
class TransitionFactorSquareGeometryAudit:
    distance: Fraction
    b_exponent: Fraction
    a_exponent: Fraction
    geometric_determinant_max_exponent: Fraction
    full_zero_geometry_exponent: Fraction
    type_ii_square_target_exponent: Fraction
    full_zero_geometry_margin: Fraction
    common_b_cross_relation_exact: bool
    zero_determinant_primitive_pairs_identical: bool
    product_frequency_offdiagonal_retained: bool
    reciprocal_cluster_l2_applied_before_absolute_n_pairs: bool
    full_zero_geometry_closes: bool
    nonzero_geometric_determinant_gate_required: bool
    nonzero_geometric_determinant_gate_proved: bool
    published_coverage: bool


@dataclass(frozen=True)
class TransitionNonzeroGammaShellAudit:
    distance: Fraction
    b_exponent: Fraction
    a_exponent: Fraction
    determinant_exponent: Fraction
    determinant_exponent_range: tuple[Fraction, Fraction]
    s_gcd_exponent: Fraction
    a_gcd_exponent: Fraction
    s_gcd_divides_determinant: bool
    a_gcd_divides_determinant: bool
    common_b_cross_relation_exact: bool
    lcm_modulus_exponent: Fraction
    b_completion_dual_exponent: Fraction
    primitive_a_step_exponent: Fraction
    determinant_orbit_length_exponent: Fraction
    determinant_orbit_parametrization_exact: bool
    current_cluster_square_bound_exponent: Fraction
    cluster_square_bound_independently_proved: bool
    type_ii_square_target_exponent: Fraction
    required_joint_saving_exponent: Fraction
    reciprocity_modulus_exponent: Fraction
    reciprocity_strictly_reduces_modulus: bool
    both_s_mobius_weights_retained: bool
    product_frequency_pair_retained: bool
    coupled_kernel_retained: bool
    complete_nonzero_shell_estimate_required: bool
    complete_nonzero_shell_estimate_proved: bool
    published_coverage: bool


@dataclass(frozen=True)
class TransitionGammaGraphEnergyAudit:
    distance: Fraction
    b_exponent: Fraction
    a_exponent: Fraction
    determinant_exponent: Fraction
    determinant_max_exponent: Fraction
    determinant_fiber_exponent: Fraction
    maximum_graph_degree_exponent: Fraction
    reciprocal_cluster_vertex_energy_exponent: Fraction
    graph_energy_bound_exponent: Fraction
    type_ii_square_target_exponent: Fraction
    graph_energy_target_margin: Fraction
    coverage_lhs: Fraction
    coverage_threshold: Fraction
    maximum_degree_energy_inequality_exact: bool
    product_frequency_cluster_l2_used: bool
    mobius_cancellation_used: bool
    phase_cancellation_between_distinct_vertices_used: bool
    shell_covered_unconditionally: bool
    published_coverage: bool


@dataclass(frozen=True)
class TransitionGammaGcdGraphEnergyAudit:
    distance: Fraction
    b_exponent: Fraction
    a_exponent: Fraction
    determinant_exponent: Fraction
    s_gcd_exponent: Fraction
    a_gcd_exponent: Fraction
    raw_determinant_fiber_exponent: Fraction
    gcd_reduced_fiber_exponent: Fraction
    maximum_graph_degree_exponent: Fraction
    reciprocal_cluster_vertex_energy_exponent: Fraction
    graph_energy_bound_exponent: Fraction
    type_ii_square_target_exponent: Fraction
    graph_energy_target_margin: Fraction
    coverage_lhs: Fraction
    coverage_threshold: Fraction
    a_gcd_candidate_reduction_exact: bool
    s_gcd_fiber_reduction_exact: bool
    product_frequency_cluster_l2_used: bool
    mobius_cancellation_used: bool
    shell_covered_unconditionally: bool
    published_coverage: bool


@dataclass(frozen=True)
class TransitionCrossDeterminantLatticeAudit:
    distance: Fraction
    b_exponent: Fraction
    a_exponent: Fraction
    determinant_exponent: Fraction
    maximum_graph_degree_exponent: Fraction
    reciprocal_cluster_vertex_energy_exponent: Fraction
    graph_energy_bound_exponent: Fraction
    type_ii_square_target_exponent: Fraction
    graph_energy_target_margin: Fraction
    coverage_lhs: Fraction
    coverage_threshold: Fraction
    cross_determinant_relation_exact: bool
    entry_gcd_bounded_by_fixed_slope: bool
    fixed_value_fiber_has_bounded_cardinality: bool
    product_frequency_cluster_l2_used: bool
    mobius_cancellation_used: bool
    shell_covered_unconditionally: bool
    published_coverage: bool


@dataclass(frozen=True)
class TransitionFareyHeckeOrbitAudit:
    distance: Fraction
    b_exponent: Fraction
    determinant_exponent: Fraction
    hecke_index_exponent: Fraction
    entry_exponent: Fraction
    modulus_exponent: Fraction
    product_frequency_exponent: Fraction
    type_ii_square_target_exponent: Fraction
    signed_entry_determinant_exact: bool
    reciprocal_square_phase_exact: bool
    hecke_index_contains_common_b: bool
    common_b_weight_is_mobius_squared: bool
    hecke_index_has_mobius_weight: bool
    both_entry_mobius_weights_retained: bool
    affine_cofactor_weights_joint_in_entry_and_modulus: bool
    archimedean_reciprocity_correction_retained: bool
    coupled_kernel_retained: bool
    classical_kuznetsov_adapter_verified: bool
    new_entry_weighted_hecke_estimate_required: bool
    new_entry_weighted_hecke_estimate_proved: bool
    published_coverage: bool


@dataclass(frozen=True)
class TransitionEntryMobiusFactorizationAudit:
    distance: Fraction
    b_exponent: Fraction
    entry_cutoff_exponent: Fraction
    entry_long_factor_exponent: Fraction
    entry_short_factor_exponent: Fraction
    fixed_denominator_factor_exponent: Fraction
    wright_size_hypothesis_holds: bool
    optimistic_wright_saving_exponent: Fraction
    factor_box_target_saving_exponent: Fraction
    optimistic_wright_deficit: Fraction
    mobius_factorization_exact: bool
    double_reciprocity_cancels_archimedean_term: bool
    affine_cofactor_remains_joint: bool
    shift_window_remains_joint: bool
    coupled_kernel_remains_joint: bool
    actual_wright_coefficient_hypotheses_verified: bool
    two_entry_type_ii_estimate_required: bool
    two_entry_type_ii_estimate_proved: bool
    published_coverage: bool


@dataclass(frozen=True)
class TransitionCrossGcdLatticeAudit:
    distance: Fraction
    b_exponent: Fraction
    determinant_exponent: Fraction
    a_gcd_exponent: Fraction
    w_gcd_exponent: Fraction
    reduced_determinant_value_exponent: Fraction
    maximum_graph_degree_exponent: Fraction
    reciprocal_cluster_vertex_energy_exponent: Fraction
    graph_energy_bound_exponent: Fraction
    type_ii_square_target_exponent: Fraction
    graph_energy_target_margin: Fraction
    coverage_lhs: Fraction
    coverage_threshold: Fraction
    a_w_common_gcd_is_slope_bounded: bool
    combined_gcd_divides_determinant: bool
    fixed_value_fiber_has_bounded_cardinality: bool
    product_frequency_cluster_l2_used: bool
    mobius_cancellation_used: bool
    shell_covered_unconditionally: bool
    published_coverage: bool


@dataclass(frozen=True)
class TransitionTripleGcdLatticeAudit:
    distance: Fraction
    b_exponent: Fraction
    determinant_exponent: Fraction
    a_gcd_exponent: Fraction
    s_gcd_exponent: Fraction
    w_gcd_exponent: Fraction
    reduced_determinant_value_exponent: Fraction
    maximum_graph_degree_exponent: Fraction
    reciprocal_cluster_vertex_energy_exponent: Fraction
    graph_energy_bound_exponent: Fraction
    type_ii_square_target_exponent: Fraction
    graph_energy_target_margin: Fraction
    coverage_lhs: Fraction
    coverage_threshold: Fraction
    a_s_gcds_coprime: bool
    s_w_gcds_coprime: bool
    a_w_common_gcd_is_slope_bounded: bool
    triple_gcd_divides_determinant: bool
    product_frequency_cluster_l2_used: bool
    mobius_cancellation_used: bool
    shell_covered_unconditionally: bool
    published_coverage: bool


@dataclass(frozen=True)
class TransitionFinalTwoEntryGateAudit:
    distance: Fraction
    b_exponent: Fraction
    determinant_exponent: Fraction
    total_gcd_exponent: Fraction
    reduced_determinant_exponent: Fraction
    current_graph_bound_exponent: Fraction
    two_entry_square_root_saving_exponent: Fraction
    required_two_entry_bound_exponent: Fraction
    raw_type_ii_square_target_exponent: Fraction
    power_margin: Fraction
    margin_identity_exact: bool
    is_unique_power_critical_face: bool
    endpoint_taper_square_log_saving: Fraction
    product_energy_log_loss: Fraction
    post_cauchy_log_saving: Fraction
    beta_box_union_log_loss: Fraction
    global_net_log_saving: Fraction
    global_remainder_power_exponent: Fraction
    two_entry_square_root_gate_required: bool
    two_entry_square_root_gate_proved: bool
    whole_transition_face_covered: bool


@dataclass(frozen=True)
class TransitionHPoissonLineAudit:
    distance: Fraction
    common_gcd_exponent: Fraction
    h_poisson_factor_exponent: Fraction
    dual_v_exponent: Fraction
    dual_j_exponent: Fraction
    primitive_v_exponent: Fraction
    primitive_j_exponent: Fraction
    shift_quotient_exponent: Fraction
    line_parameter_exponent: Fraction
    inner_delta_n_area_exponent: Fraction
    outer_slope_family_exponent: Fraction
    pre_poisson_layer_cardinality_exponent: Fraction
    absolute_post_poisson_exponent: Fraction
    asymptotic_local_target_exponent: Fraction
    required_inner_saving_exponent: Fraction
    inner_square_root_saving_exponent: Fraction
    square_root_power_margin: Fraction
    determinant_line_parametrization_exact: bool
    mobius_entry_change_is_unimodular: bool
    is_unique_power_critical_layer: bool
    absolute_count_reaches_power_target: bool
    maximal_gcd_layer_closes_with_endpoint_tapers: bool
    fixed_slope_square_root_proved: bool
    averaged_slope_square_function_proved: bool
    whole_far_shell_covered: bool


@dataclass(frozen=True)
class TransitionHPoissonSquareOffdiagonalAudit:
    primitive_slope_pair_exponent: Fraction
    inner_area_exponent: Fraction
    expanded_square_cardinality_exponent: Fraction
    identity_diagonal_exponent: Fraction
    square_function_target_exponent: Fraction
    required_offdiagonal_saving_exponent: Fraction
    cross_determinant_max_exponent: Fraction
    top_cokernel_character_exponent: Fraction
    character_square_root_saving_exponent: Fraction
    remaining_mobius_entry_saving_exponent: Fraction
    zero_cross_determinant_is_identity_diagonal: bool
    nonzero_cross_determinant_recovers_unique_slope: bool
    cokernel_is_one_cyclic_character_family: bool
    signed_four_mobius_hecke_sum_required: bool
    hybrid_mobius_hecke_estimate_proved: bool
    critical_square_function_proved: bool


@dataclass(frozen=True)
class TransitionPublishedKloostermanEntryAudit:
    modulus_exponent: Fraction
    delta_interval_exponent: Fraction
    required_mobius_entry_saving_exponent: Fraction
    bp_uniform_saving_exponent: Fraction
    bp_uniform_deficit: Fraction
    mqw_uniform_saving_exponent: Fraction
    mqw_uniform_deficit: Fraction
    pascadi_factorable_saving_exponent: Fraction
    pascadi_factorable_deficit: Fraction
    optimistic_four_bp_applications_saving_exponent: Fraction
    optimistic_four_bp_deficit: Fraction
    bp_square_root_length_condition_holds: bool
    bp_arbitrary_sequences_allowed: bool
    standard_kloosterman_kernel_verified: bool
    coefficients_separate_from_matrix_entries: bool
    fixed_modulus_before_entry_sum_verified: bool
    pascadi_uniform_for_all_moduli: bool
    published_coverage: bool
    bp_source: str
    mqw_source: str
    pascadi_source: str


@dataclass(frozen=True)
class TransitionDeltaLatticePoissonAudit:
    determinant_exponent: Fraction
    delta_length_exponent: Fraction
    delta_box_area_exponent: Fraction
    primitive_divisor_exponent: Fraction
    primitive_divisor_weight_exponent: Fraction
    lattice_covolume_exponent: Fraction
    zero_mode_density_exponent: Fraction
    entry_pair_shell_exponent: Fraction
    zero_mode_absolute_exponent: Fraction
    square_function_target_exponent: Fraction
    required_zero_mode_saving_exponent: Fraction
    longitudinal_dual_spacing_exponent: Fraction
    transverse_dual_spacing_exponent: Fraction
    active_longitudinal_frequency_exponent: Fraction
    active_transverse_frequency_exponent: Fraction
    weighted_active_longitudinal_exponent: Fraction
    primitive_zero_mode_coefficient: str
    primitive_euler_factor_tail_exponent: Fraction
    primitive_mobius_inversion_exact: bool
    primitive_divisor_layers_do_not_worsen: bool
    zero_mode_obstruction_independent_of_determinant_shell: bool
    zero_mode_covolume_jacobian_cancels_exactly: bool
    zero_mode_is_continuous_slope_gram: bool
    full_zero_mode_gram_positive_semidefinite: bool
    offdiagonal_is_full_gram_minus_identity_diagonal: bool
    kernel_alone_annihilates_zero_mode: bool
    square_function_route_is_only_sufficient: bool
    zero_mode_weight_separates_in_the_entries: bool
    zero_mode_mobius_variance_proved: bool
    whole_delta_lattice_covered: bool


@dataclass(frozen=True)
class TransitionDenominatorGcdLineAudit:
    determinant_exponent: Fraction
    denominator_gcd_exponent: Fraction
    denominator_cofactor_exponent: Fraction
    denominator_pair_exponent: Fraction
    determinant_quotient_exponent: Fraction
    line_parameter_exponent: Fraction
    raw_line_family_exponent: Fraction
    square_function_target_exponent: Fraction
    required_saving_exponent: Fraction
    two_denominator_mobius_length_exponent: Fraction
    two_denominator_square_root_saving_exponent: Fraction
    post_square_root_exponent: Fraction
    square_root_power_margin: Fraction
    mobius_product_reduction_exact: bool
    top_determinant_is_unique_critical_face: bool
    absolute_count_reaches_target: bool
    two_mobius_line_square_root_proved: bool
    shell_covered: bool


@dataclass(frozen=True)
class TransitionDenominatorMobiusTypeIIAudit:
    determinant_exponent: Fraction
    denominator_gcd_exponent: Fraction
    denominator_cofactor_exponent: Fraction
    cutoff_exponent: Fraction
    left_short_mobius_exponent: Fraction
    left_cutoff_divisor_exponent: Fraction
    left_unsigned_cofactor_exponent: Fraction
    right_short_mobius_exponent: Fraction
    right_cutoff_divisor_exponent: Fraction
    right_unsigned_cofactor_exponent: Fraction
    signed_mobius_atom_volume_exponent: Fraction
    signed_atom_square_root_saving_exponent: Fraction
    required_total_saving_exponent: Fraction
    top_face_unsigned_half_volume_exponent: Fraction
    off_top_power_margin_exponent: Fraction
    remaining_completion_saving_exponent: Fraction
    left_type_ii_boundary: bool
    right_type_ii_boundary: bool
    exact_c_u_factorization_used: bool
    top_face_deficit_identity_exact: bool
    general_deficit_identity_exact: bool
    no_unsigned_completion_needed: bool
    signed_atom_square_root_proved: bool
    unsigned_cofactor_completion_proved: bool
    cell_closed_by_registered_bounds: bool


@dataclass(frozen=True)
class TransitionBourgainGaraevMultilinearAudit:
    modulus_exponent: Fraction
    atom_interval_exponent: Fraction
    actual_multilinear_variable_count: int
    required_saving_exponent: Fraction
    theorem9_grouped_interval_exponent: Fraction
    theorem9_saving_exponent: Fraction
    theorem9_deficit: Fraction
    theorem10_k2_saving_exponent: Fraction
    theorem10_k2_deficit: Fraction
    theorem11_minimum_variable_count: int
    theorem11_product_length_condition_holds: bool
    theorem11_variable_count_condition_holds: bool
    theorem12_section10_4_proof_constant_lower_bound: int
    theorem12_published_constant: int
    theorem12_n4_threshold_exponent: Fraction
    theorem12_length_condition_holds: bool
    theorem13_product_interval_exponent: Fraction
    theorem13_threshold_exponent: Fraction
    theorem13_available_epsilon_margin: Fraction
    theorem13_product_condition_holds: bool
    theorem13_saving_exponent_is_explicit: bool
    theorem13_required_half_power_saving_certified: bool
    theorems_require_prime_modulus: bool
    actual_determinant_moduli_all_prime: bool
    grouped_product_sets_are_intervals: bool
    actual_four_atom_weights_separate: bool
    reciprocal_product_phase_verified: bool
    published_coverage: bool
    source: str


@dataclass(frozen=True)
class TransitionBourgainGaraevIteratedFactorizationAudit:
    original_atom_exponent: Fraction
    desired_equal_subatom_count: int
    desired_subatom_exponent: Fraction
    formal_total_variable_count: int
    theorem11_minimum_variable_count: int
    formal_theorem11_count_condition_holds: bool
    formal_theorem11_product_condition_holds: bool
    theorem11_required_half_power_saving_certified: bool
    prime_atom_has_balanced_two_factor_decomposition: bool
    iterated_identity_forces_seven_positive_length_variables: bool
    actual_phase_is_reciprocal_product: bool
    actual_moduli_all_prime: bool
    published_coverage: bool


@dataclass(frozen=True)
class TransitionMobiusHeckeReciprocalLAudit:
    physical_spectral_line: Fraction
    required_mobius_saving_exponent: Fraction
    k_local_first_nontrivial_degree: int
    local_factorization_exact: bool
    k_euler_product_absolutely_convergent_at_half: bool
    balanced_two_factor_local_factorization_exact: bool
    balanced_reciprocal_l_factor_count: int
    balanced_zeta_factor_count: int
    balanced_k_local_first_nontrivial_degree: int
    classical_kuznetsov_hecke_index_is_shift: bool
    mobius_entries_are_not_classical_hecke_indices: bool
    balanced_factor_is_conditional_spectral_diagnostic: bool
    actual_kuznetsov_reduction_derived: bool
    reciprocal_l_negative_moment_proved: bool
    required_half_power_saving_certified: bool
    whole_line_family_covered: bool


@dataclass(frozen=True)
class TransitionEntryWeightedRelativeTraceAudit:
    required_nonspherical_primes: tuple[int, ...]
    minimum_global_level: int
    asymptotic_log_level_scale: Fraction
    minimum_global_level_is_primorial: bool
    local_spherical_vector_is_constant_on_primitive_columns: bool
    primitive_entry_weight_is_not_k_invariant: bool
    exact_squarefree_weight_needs_depth_two_for_small_primes: bool
    hecke_index_is_shift_not_entry: bool
    polynomial_conductor_preserved: bool
    published_entry_weighted_adapter: bool
    whole_line_family_covered: bool


@dataclass(frozen=True)
class TransitionSmallPrimeSpectralHybridAudit:
    fixed_rough_factor_cap: int
    fixed_cap_cutoff_exponent: Fraction
    polynomial_level_exponent: Fraction
    required_saving_exponent: Fraction
    rough_density_power_saving_exponent: Fraction
    residual_power_deficit: Fraction
    logarithmic_cutoff_keeps_polynomial_level: bool
    logarithmic_cutoff_forces_fixed_factor_count: bool
    fixed_factor_cutoff_has_superpolynomial_level: bool
    published_rough_cofactor_half_power_bound: bool
    whole_line_family_covered: bool


@dataclass(frozen=True)
class TransitionGeneralCutoffLineGateAudit:
    determinant_exponent: Fraction
    denominator_gcd_exponent: Fraction
    cofactor_exponent: Fraction
    cutoff_ratio: Fraction
    type_split_ratio: Fraction
    cutoff_exponent: Fraction
    type_split_exponent: Fraction
    left_unsigned_exponent: Fraction
    right_unsigned_exponent: Fraction
    signed_square_root_saving: Fraction
    unsigned_completion_saving: Fraction
    required_saving: Fraction
    total_hypothetical_saving: Fraction
    top_face_power_margin: Fraction
    cutoff_independent_deficit_identity: bool
    cutoff_choice_creates_positive_power_slack: bool
    cell_closed_by_registered_bounds: bool


@dataclass(frozen=True)
class TransitionBBLRQuadraticDivisorAudit:
    denominator_gcd_exponent: Fraction
    cofactor_exponent: Fraction
    side_product_exponent: Fraction
    left_signed_outer_exponent: Fraction
    right_signed_outer_exponent: Fraction
    total_signed_outer_exponent: Fraction
    maximum_signed_outer_exponent: Fraction
    unsigned_pair_parameter_exponent: Fraction
    shift_exponent: Fraction
    frequency_parameter_exponent: Fraction
    sharp_error_formula_applicable: bool
    sharp_error_ab_exponent: Fraction
    sharp_error_watt_exponent: Fraction
    sharp_error_exponent: Fraction
    general_error_first_exponent: Fraction
    general_error_h_squared_exponent: Fraction
    general_error_exponent: Fraction
    target_exponent: Fraction
    best_error_exponent: Fraction
    best_error_power_margin: Fraction
    hard_face_global_best_power_margin: Fraction
    outer_slots_absorb_all_signed_atoms: bool
    remaining_slots_are_two_unsigned_factors_per_side: bool
    arbitrary_coefficients_allowed_only_in_outer_slots: bool
    independent_internal_smooth_weights_supported: bool
    side_product_balance_verified: bool
    outer_coefficient_divisor_bound_verified: bool
    proposition_3_1_hypotheses_verified: bool
    four_main_terms_cancelled_after_mobius_recombination: bool
    published_theorem_closes_cell: bool
    source: str


@dataclass(frozen=True)
class TransitionBBLRHardUnsignedCellAudit:
    poisson_gcd_exponent: Fraction
    outer_a_exponent: Fraction
    outer_b_exponent: Fraction
    m1_exponent: Fraction
    m2_exponent: Fraction
    n1_exponent: Fraction
    n2_exponent: Fraction
    shift_exponent: Fraction
    lemma_3_1_z_exponent: Fraction
    x_interval_exponent: Fraction
    poisson_gcd_count_exponent: Fraction
    dyadic_layer_exponent: Fraction
    initial_h_squared_error_exponent: Fraction
    global_error_exponent: Fraction
    target_exponent: Fraction
    power_margin: Fraction
    one_mobius_pure_unsigned_coefficient: int
    four_mobius_pure_unsigned_coefficient: int
    cellwise_mobius_cancellation_available: bool
    cross_outer_scale_recombination_required: bool
    uncompressed_lemma_improves_proposition_bound: bool
    source: str


@dataclass(frozen=True)
class TransitionBanksShparlinskiPreCauchyAudit:
    entry_scale_exponent: Fraction
    dual_v_exponent: Fraction
    dual_j_exponent: Fraction
    fixed_slope_family_exponent: Fraction
    shift_variable_exponent: Fraction
    fixed_slope_geometric_count_exponent: Fraction
    best_theorem_role_bound_exponent: Fraction
    best_fixed_slope_bound_exponent: Fraction
    h_poisson_factor_exponent: Fraction
    aggregated_exponent: Fraction
    target_exponent: Fraction
    power_margin: Fraction
    short_interval_threshold_exponent: Fraction
    actual_short_interval_exponent: Fraction
    short_interval_threshold_margin: Fraction
    additive_theorem_requires_fixing_both_bilinear_slopes: bool
    original_shift_has_no_mobius_weight: bool
    divisor_convolution_can_insert_the_missing_mobius_weight: bool
    divisor_convolution_creates_power_saving: bool
    all_actual_kernel_hypotheses_verified: bool
    published_theorem_closes_pre_cauchy_sum: bool
    source: str


@dataclass(frozen=True)
class TransitionRamareMediumPrimeAudit:
    entry_exponent: Fraction
    band_lower_exponent: Fraction
    band_upper_exponent: Fraction
    required_line_saving_exponent: Fraction
    prime_exceptional_set_exponent: Fraction
    prime_exceptional_log_density_saving: Fraction
    prime_exceptional_power_density_saving: Fraction
    uncovered_power_deficit: Fraction
    band_reaches_entry_scale: bool
    proper_band_leaves_prime_sector_exceptional: bool
    prime_sector_is_in_ramare_sum: bool
    prime_sector_extracted_factor_exponent: Fraction
    prime_sector_cofactor_exponent: Fraction
    prime_sector_positive_length_factor_count: int
    forces_two_positive_length_factors: bool
    ramare_decomposition_closes_line_gate: bool
    source: str


@dataclass(frozen=True)
class TransitionPrimeKloostermanAudit:
    modulus_exponent: Fraction
    prime_interval_exponent: Fraction
    required_saving_exponent: Fraction
    unrestricted_prime_bound_exponent: Fraction
    unrestricted_prime_saving_exponent: Fraction
    progression_prime_bound_exponent: Fraction
    progression_prime_saving_exponent: Fraction
    progression_modulus_cap_exponent: Fraction
    optimistic_four_unrestricted_saving_exponent: Fraction
    optimistic_four_unrestricted_deficit: Fraction
    optimistic_four_progression_saving_exponent: Fraction
    optimistic_four_progression_deficit: Fraction
    published_theorem_has_fixed_prime_modulus: bool
    actual_determinant_moduli_all_prime: bool
    standard_single_kloosterman_argument_verified: bool
    other_entry_weights_separate: bool
    published_theorem_closes_prime_sector: bool
    source: str


@dataclass(frozen=True)
class PoissonExchangeSecondOrderAudit:
    physical_shifted_sum_swap_is_conjugate: bool
    poisson_modulus_changes_under_swap: bool
    reciprocity_correction_retained: bool
    full_poisson_term_swap_is_conjugate: bool
    completed_coefficient_forced_real: bool
    imaginary_coefficient_has_linear_centered_term: bool
    second_order_bound_requires_real_coefficient: bool
    second_order_collar_unconditional: bool


@dataclass(frozen=True)
class CommonModulusExchangeAudit:
    common_modulus_exponent: Fraction
    raw_dual_c_exponent: Fraction
    raw_dual_v_exponent: Fraction
    original_gauss_support_divisor_exponent: Fraction
    swapped_gauss_support_divisor_exponent: Fraction
    reduced_dual_c_exponent: Fraction
    reduced_dual_v_exponent: Fraction
    original_frequency_sublattice_is_r_times_square: bool
    swapped_frequency_sublattice_is_s_times_square: bool
    nonzero_sublattice_intersection_empty_mod_rs: bool
    centered_zero_frequency_annihilated: bool
    common_modulus_forces_real_completed_coefficient: bool
    common_modulus_reduces_conductor: bool
    second_order_collar_unconditional: bool


@dataclass(frozen=True)
class MidpointHermitianCompletionAudit:
    common_modulus_exponent: Fraction
    raw_dual_c_exponent: Fraction
    raw_dual_v_exponent: Fraction
    completed_ambient_exponent: Fraction
    completion_prefactor_exponent: Fraction
    completed_gate_target_exponent: Fraction
    square_root_ambient_exponent: Fraction
    allowance_beyond_square_root_exponent: Fraction
    midpoint_coefficient_is_unit: bool
    midpoint_coefficient_is_involution: bool
    exchange_negates_midpoint_coefficient: bool
    same_frequency_swap_is_conjugate: bool
    centered_multiplier_zero_on_c_zero_row: bool
    centered_multiplier_zero_on_v_zero_column: bool
    modular_involution_phase_is_near_diagonal_small: bool
    published_bound_verified: bool


@dataclass(frozen=True)
class MidpointPublishedHermitianAdapterAudit:
    numerator_exponent: Fraction
    rs_trivial_exponent: Fraction
    withdrawn_claimed_outer_inner_bound_exponent: Fraction
    withdrawn_claimed_outer_inner_saving_exponent: Fraction
    withdrawn_claimed_bulk_inner_bound_exponent: Fraction
    withdrawn_claimed_bulk_inner_saving_exponent: Fraction
    theorem_has_moving_numerator: bool
    theorem_accepts_joint_r_s_c_v_coefficient: bool
    theorem_supplies_c_v_frequency_average: bool
    claim_withdrawn_for_missing_l_squared_factor: bool
    corrected_argument_gives_claimed_improvement: bool
    withdrawn_claim_closes_midpoint_gate: bool
    source: str


@dataclass(frozen=True)
class MidpointUnitaryDivisorAudit:
    product_variable_exponent: Fraction
    root_modulus_exponent: Fraction
    physical_numerator_exponent: Fraction
    dual_numerator_exponent: Fraction
    factorization_root_bijection_exact: bool
    mobius_product_collapses_to_single_mobius: bool
    root_multiplicity_is_subpower: bool
    balanced_dyadic_condition_is_root_filter: bool
    root_trace_coefficient_remains_joint: bool
    unitary_root_trace_bound_verified: bool


@dataclass(frozen=True)
class MidpointRootFareyLargeSieveAudit:
    root_point_count_exponent: Fraction
    denominator_exponent: Fraction
    reciprocal_spacing_exponent: Fraction
    physical_numerator_length_exponent: Fraction
    physical_product_energy_exponent: Fraction
    physical_large_sieve_bound_exponent: Fraction
    physical_target_exponent: Fraction
    physical_deficit_exponent: Fraction
    dual_numerator_length_exponent: Fraction
    dual_product_energy_exponent: Fraction
    dual_large_sieve_bound_exponent: Fraction
    dual_target_exponent: Fraction
    dual_deficit_exponent: Fraction
    root_fractions_injective: bool
    root_fractions_reduced: bool
    actual_joint_coefficient_is_separated: bool
    root_farey_large_sieve_closes_gate: bool


@dataclass(frozen=True)
class MidpointRootTypeIIAudit:
    product_exponent: Fraction
    left_factor_exponent: Fraction
    right_factor_exponent: Fraction
    physical_numerator_exponent: Fraction
    dual_numerator_exponent: Fraction
    generalized_crt_exact: bool
    reciprocal_phase_split_exact: bool
    left_factor_has_truncated_divisor_coefficient: bool
    right_factor_retains_mobius: bool
    root_fibers_are_subpower: bool
    completed_centering_exact: bool
    physical_zero_residue_vanishes: bool
    physical_centered_subtraction_present: bool
    published_hermitian_theorem_has_root_dependent_numerator: bool
    actual_transform_coefficient_remains_joint: bool
    root_type_ii_bound_verified: bool


@dataclass(frozen=True)
class MidpointRootFourFactorAudit:
    left_product_exponent: Fraction
    right_product_exponent: Fraction
    physical_numerator_exponent: Fraction
    recovered_r_exponent: Fraction
    recovered_s_exponent: Fraction
    root_fibers_unfold_to_ordered_factorizations: bool
    four_factors_are_pairwise_coprime: bool
    truncated_divisor_coefficient_remains_on_left_product: bool
    mobius_splits_over_right_factors: bool
    kloosterman_phase_identity_exact: bool
    completed_centering_exact: bool
    physical_zero_residue_vanishes: bool
    physical_centered_subtraction_present: bool
    extreme_sector_recovers_hard_fraction: bool
    actual_smooth_weight_remains_joint: bool
    four_factor_type_ii_bound_verified: bool


@dataclass(frozen=True)
class MidpointPhysicalPoissonAudit:
    modulus_exponent: Fraction
    h_exponent: Fraction
    delta_exponent: Fraction
    resonance_window_exponent: Fraction
    lattice_parameter_exponent: Fraction
    pointwise_bilinear_bound_exponent: Fraction
    raw_bilinear_exponent: Fraction
    physical_oscillation_saving_exponent: Fraction
    outer_root_point_exponent: Fraction
    outer_target_exponent: Fraction
    required_outer_saving_exponent: Fraction
    resonance_lattice_bijection_exact: bool
    one_variable_poisson_exact: bool
    joint_weight_has_uniform_delta_derivatives: bool
    determinant_line_correspondence_exact: bool
    physical_poisson_route_is_independent: bool
    outer_mobius_square_root_verified: bool


@dataclass(frozen=True)
class RootSalieAdapterAudit:
    modulus_exponent: Fraction
    physical_numerator_exponent: Fraction
    fixed_numerator_bound_exponent: Fraction
    fixed_numerator_saving_exponent: Fraction
    absolute_numerator_sum_bound_exponent: Fraction
    physical_target_exponent: Fraction
    absolute_numerator_sum_deficit_exponent: Fraction
    odd_full_root_trace_identity_exact: bool
    even_midpoint_modulus_adapter_verified: bool
    theorem_accepts_balanced_root_filter: bool
    theorem_accepts_mobius_modulus_weight: bool
    theorem_accepts_moving_numerator: bool
    square_numerator_exception_covered: bool
    theorem_accepts_joint_transform_weight: bool
    salie_adapter_closes_root_gate: bool


@dataclass(frozen=True)
class RootSalieJointAverageAudit:
    left_root_factor_exponent: Fraction
    right_root_factor_exponent: Fraction
    physical_numerator_exponent: Fraction
    bcr_term_1_exponent: Fraction
    bcr_term_2_exponent: Fraction
    bcr_bound_exponent: Fraction
    physical_target_exponent: Fraction
    bcr_deficit_exponent: Fraction
    square_product_pair_count_exponent: Fraction
    dfi_square_main_short_factor_cutoff_exponent: Fraction
    dfi_long_long_cutoff_exponent: Fraction
    balanced_root_factor_exponent: Fraction
    fixed_square_hermitian_bound_exponent: Fraction
    absolute_square_family_bound_exponent: Fraction
    absolute_square_family_deficit_exponent: Fraction
    salie_factorization_matches_midpoint_phase: bool
    joint_average_is_existing_bcr_endpoint: bool
    bcr_accepts_mobius_coefficients: bool
    bcr_uses_mobius_beyond_l2: bool
    balanced_root_filter_excludes_dfi_square_main: bool
    joint_salie_route_closes_root_gate: bool


@dataclass(frozen=True)
class SquareSalieGaussCompletionAudit:
    r_exponent: Fraction
    s_exponent: Fraction
    square_root_exponent: Fraction
    x_exponent: Fraction
    y_exponent: Fraction
    gauss_normalization_exponent: Fraction
    t_poisson_resonance_exponent: Fraction
    localized_pointwise_exponent: Fraction
    direct_square_sector_pointwise_exponent: Fraction
    double_gauss_identity_exact: bool
    cross_character_depends_only_on_mod8: bool
    square_root_variable_is_linearized: bool
    remaining_quadratic_weight_is_joint: bool
    gauss_completion_improves_square_sector: bool
    square_salie_gauss_route_closes_gate: bool


@dataclass(frozen=True)
class MobiusProductShiftedVarianceAudit:
    factor_length_exponent: Fraction
    product_length_exponent: Fraction
    transform_shift_exponent: Fraction
    diagonal_power_exponent: Fraction
    diagonal_logarithmic_exponent: Fraction
    raw_shifted_determinant_exponent: Fraction
    shifted_determinant_target_exponent: Fraction
    required_shifted_determinant_saving_exponent: Fraction
    product_convolution_identity_exact: bool
    diagonal_parameterization_exact: bool
    schwartz_tail_is_power_negligible: bool
    polylogarithmic_transition_collar_retained: bool
    equivalent_to_separated_mixed_fourth_moment_gate: bool
    shifted_mobius_determinant_bound_proved: bool
    original_signed_kernel_requires_component_gate: bool
    route_closes_mwkf_gate: bool


@dataclass(frozen=True)
class GangulyGuriaDeterminantAudit:
    variable_length_exponent: Fraction
    shift_range_exponent: Fraction
    ramanujan_exponent: Fraction
    fixed_shift_error_exponent: Fraction
    absolute_shift_sum_error_exponent: Fraction
    shifted_determinant_target_exponent: Fraction
    absolute_shift_sum_power_deficit: Fraction
    fixed_shift_main_exponent: Fraction
    absolute_shift_sum_main_exponent: Fraction
    smooth_unweighted_fixed_shift_theorem_proved: bool
    distinct_tensor_weights_accepted_as_stated: bool
    arithmetic_coefficients_accepted: bool
    coefficient_form_uniformity_quantified: bool
    mobius_type_i_ii_adapter_proved: bool
    ramanujan_conjecture_removes_power_deficit: bool
    ramanujan_conjecture_supplies_logarithmic_saving: bool
    mobius_main_term_cancellation_proved: bool
    ganguly_guria_route_closes_mobius_gate: bool


@dataclass(frozen=True)
class DarbarDasShortVarianceAudit:
    ambient_length_exponent: Fraction
    short_window_exponent: Fraction
    generic_short_variance_exponent: Fraction
    required_short_variance_exponent: Fraction
    required_variance_saving_exponent: Fraction
    full_mobius_convolution_zeta_power: int
    required_auxiliary_zeta_power: int
    required_auxiliary_prime_coefficient: int
    required_auxiliary_prime_square_coefficient: int
    required_auxiliary_prime_cube_coefficient: int
    auxiliary_fits_squarefree_m_class: bool
    auxiliary_fits_completely_multiplicative_g_class: bool
    restricted_convolution_is_multiplicative: bool
    published_theorem_covers_full_mobius_convolution: bool
    published_theorem_covers_restricted_convolution: bool
    darbar_das_route_closes_mobius_gate: bool


@dataclass(frozen=True)
class RestrictedMobiusRatioMellinAudit:
    factor_length_exponent: Fraction
    product_length_exponent: Fraction
    short_window_exponent: Fraction
    required_short_variance_exponent: Fraction
    ratio_coordinate_identity_exact: bool
    ratio_fourier_inversion_exact: bool
    integrand_coefficient_is_multiplicative: bool
    shifted_inverse_zeta_dirichlet_series_exact: bool
    product_coordinate_weight_is_smooth: bool
    ratio_transform_is_rapidly_decaying: bool
    uniform_single_tau_variance_is_sufficient: bool
    tau_zero_is_full_mobius_convolution: bool
    tau_zero_square_dirichlet_series_zeta_pole_order: int
    tau_zero_diagonal_log_exponent: int
    required_diagonal_log_exponent: int
    tau_zero_euler_remainder_has_no_prime_term: bool
    tau_zero_euler_remainder_converges_for_real_part_gt_half: bool
    tau_zero_formal_diagonal_log_excess: int
    tau_zero_diagonal_excess_requires_offdiagonal_cancellation: bool
    diagonal_term_is_not_lower_bound_for_full_variance: bool
    tau_zero_diagonal_alone_disproves_uniform_gate: bool
    joint_ratio_recombination_has_restricted_diagonal_log_order_one: bool
    optimistic_mangerel_variance_exponent: Fraction
    mangerel_power_deficit: Fraction
    mangerel_only_supplies_logarithmic_saving: bool
    uniform_tau_mangerel_hypotheses_verified: bool
    shifted_inverse_zeta_variance_proved: bool
    ratio_mellin_route_closes_mobius_gate: bool


@dataclass(frozen=True)
class BasakRoblesZaharescuMobiusConvolutionAudit:
    ambient_length_exponent: Fraction
    short_window_exponent: Fraction
    critical_denominator_exponent: Fraction
    first_pointwise_term_exponent: Fraction
    second_pointwise_term_exponent: Fraction
    third_pointwise_term_exponent: Fraction
    best_published_pointwise_exponent: Fraction
    required_pointwise_exponent: Fraction
    pointwise_exponent_deficit: Fraction
    direct_local_arc_variance_exponent: Fraction
    required_local_variance_exponent: Fraction
    local_arc_variance_deficit: Fraction
    major_arc_direct_variance_exponent: Fraction
    major_arc_power_deficit: Fraction
    published_full_mobius_convolution_pointwise_bound: bool
    published_ratio_twisted_family_bound: bool
    published_local_l2_bound: bool
    brz_direct_pointwise_route_closes_variance_gate: bool


@dataclass(frozen=True)
class InverseZetaVarianceZeroFreeAudit:
    ambient_length_exponent: Fraction
    short_window_exponent: Fraction
    variance_bound_exponent: Fraction
    dyadic_coefficient_block_exponent: Fraction
    implied_dyadic_convergence_abscissa: Fraction
    x_integration_identity_exact: bool
    cauchy_schwarz_exponent_exact: bool
    dyadic_continuation_argument_exact: bool
    implies_zeta_zero_free_real_part_gt_three_quarters: bool
    original_mwkf_asymptotic_requires_this_gate: bool
    inverse_zeta_variance_gate_available_unconditionally: bool


@dataclass(frozen=True)
class BBLRHPoissonUnsignedHardBoxAudit:
    old_weil_bound_exponent: Fraction
    h_poisson_bound_exponent: Fraction
    local_target_exponent: Fraction
    recovered_power_saving: Fraction
    h_length_matches_reduced_modulus: bool
    h_poisson_identity_exact: bool
    inverse_fraction_becomes_linear_congruence: bool
    weighted_gcd_sum_is_diagonal_scale: bool
    positive_gcd_layers_are_power_negligible: bool
    approximation_error_exponent: Fraction
    all_unsigned_hard_box_power_closed: bool
    global_logarithmic_little_o_closed: bool
    whole_signed_hard_face_covered: bool


@dataclass(frozen=True)
class BBLRHPoissonSignedCellAudit:
    outer_scale_exponent: Fraction
    large_inner_factor_exponent: Fraction
    small_inner_factor_exponent: Fraction
    transformed_shift_exponent: Fraction
    transformed_side_product_exponent: Fraction
    transformed_raw_count_exponent: Fraction
    transformed_required_bound_exponent: Fraction
    required_outer_mobius_saving: Fraction
    h_poisson_prefactor_exponent: Fraction
    first_total_bblr_error_exponent: Fraction
    second_total_bblr_error_exponent: Fraction
    global_target_exponent: Fraction
    power_margin: Fraction
    dyadic_cross_terms_reduce_to_diagonal_norms: bool
    transformed_bblr_sharp_condition_holds: bool
    published_bblr_power_covers_cell: bool
    boundary_logarithmic_little_o_closed: bool
    published_bblr_power_coverage_upper: Fraction
    signed_residual_lower_exponent: Fraction
    signed_residual_upper_exponent: Fraction
    whole_signed_hard_face_covered: bool


@dataclass(frozen=True)
class SignedDualConvolutionAudit:
    outer_atom_exponent: Fraction
    h_poisson_dual_exponent: Fraction
    product_variable_exponent: Fraction
    signed_atom_count: int
    signed_dual_product_collapse_exact: bool
    collapsed_coefficient_is_one_mobius: bool
    cutoff_condition_retained_exactly: bool
    actual_transformed_weight_product_compatible: bool
    ratio_mellin_family_required: bool
    weighted_collapse_bound_proved: bool
    whole_signed_hard_face_covered: bool


@dataclass(frozen=True)
class CoupledRatioMellinTypeIIGateAudit:
    outer_scale_exponent: Fraction
    long_mobius_variable_exponent: Fraction
    collapsed_product_variable_exponent: Fraction
    shift_exponent: Fraction
    convolution_ambient_exponent: Fraction
    progression_modulus_exponent: Fraction
    modulus_level_relative_to_ambient: Fraction
    raw_shifted_count_exponent: Fraction
    required_inner_bound_exponent: Fraction
    required_cancellation_exponent: Fraction
    two_collapsed_coefficients_square_root_saving: Fraction
    square_root_power_margin: Fraction
    modulus_within_bombieri_vinogradov_level: bool
    fixed_shift_dispersion_suffices_after_shift_sum: bool
    quotient_mobius_prevents_direct_bv: bool
    full_shift_average_must_remain_coupled: bool
    coprimality_prime_allocation_required: bool
    four_variable_reduction_exact: bool
    coupled_ratio_mellin_type_ii_bound_proved: bool
    whole_signed_hard_face_covered: bool


@dataclass(frozen=True)
class CollapsedCoprimalityAllocationAudit:
    cross_coprimality_condition_count: int
    mobius_allocation_divisor_count: int
    product_gcd_factorization_exact: bool
    allocation_is_finite_reindexing: bool
    positive_power_loss_exponent: Fraction
    registered_logarithmic_loss: Fraction
    four_variable_superposition_exact: bool
    collapsed_coefficients_independent_of_long_variables: bool
    standard_bombieri_vinogradov_adapter_applies: bool
    coupled_ratio_mellin_type_ii_bound_proved: bool
    whole_signed_hard_face_covered: bool


@dataclass(frozen=True)
class CollapsedChowlaFaceAudit:
    outer_scale_exponent: Fraction
    long_mobius_variable_exponent: Fraction
    collapsed_product_variable_exponent: Fraction
    equal_face_raw_exponent: Fraction
    required_inner_bound_exponent: Fraction
    positive_power_margin: Fraction
    equal_collapsed_product_face_present: bool
    determinant_reduces_to_fixed_shift: bool
    primitive_gcd_excludes_face: bool
    pointwise_zero_ratio_coefficient_is_mobius: bool
    face_contains_two_point_chowla: bool
    ordinary_two_point_chowla_available_unconditionally: bool
    logarithmic_little_o_required: bool
    uniform_ratio_frequency_triangle_gate_admissible: bool
    joint_ratio_integral_must_remain_coupled: bool
    coupled_ratio_mellin_type_ii_bound_proved: bool
    whole_signed_hard_face_covered: bool


@dataclass(frozen=True)
class PhysicalJointRatioRecombinationAudit:
    ratio_mellin_recombines_to_finite_divisor_kernel: bool
    primitive_equal_face_coefficient_can_be_nonzero: bool
    witness_equal_face_coefficient: int
    joint_ratio_integration_alone_annihilates_chowla_face: bool
    arbitrary_smooth_weight_enlargement_admissible: bool
    allocationwise_triangle_inequality_admissible: bool
    equal_face_separate_bound_available_unconditionally: bool
    full_outer_scale_and_kernel_sum_must_remain_coupled: bool
    centered_coupled_dispersion_bound_proved: bool
    whole_signed_hard_face_covered: bool


@dataclass(frozen=True)
class CollapsedGcdLayerCenteredKernelAudit:
    collapsed_exponent: Fraction
    gcd_exponent: Fraction
    cofactor_exponent: Fraction
    product_length_exponent: Fraction
    primitive_shift_exponent: Fraction
    raw_dyadic_layer_exponent: Fraction
    global_target_exponent: Fraction
    required_saving_exponent: Fraction
    fourier_inner_target_exponent: Fraction
    shift_weight_vanishes_near_zero: bool
    product_diagonal_annihilated_exactly: bool
    constant_fourier_mode_centered_exactly: bool
    full_g_sum_retained: bool
    full_allocation_and_ratio_sum_retained: bool
    top_equal_product_face: bool
    fixed_affine_chowla_must_remain_inside_g_sum: bool
    pointwise_fixed_affine_chowla_bound_assumed: bool
    published_averaged_chowla_adapter_applies: bool
    centered_coupled_dispersion_bound_proved: bool
    whole_signed_hard_face_covered: bool


@dataclass(frozen=True)
class TopEqualProductOuterPntAudit:
    signed_atom_exponent: Fraction
    poisson_quotient_exponent: Fraction
    outer_pair_raw_exponent: Fraction
    long_correlation_trivial_exponent: Fraction
    face_raw_exponent: Fraction
    face_target_exponent: Fraction
    power_margin: Fraction
    primitive_equal_product_factorization_exact: bool
    signed_atom_interval_convolution_exact: bool
    balanced_cutoff_ratios_verified: bool
    uniform_coprime_pnt_log_saving_available: bool
    coprime_euler_factor_loss_only_polylogarithmic: bool
    long_mobius_correlation_used_only_trivially: bool
    fixed_affine_chowla_estimate_required: bool
    top_equal_product_face_closed_unconditionally: bool
    whole_signed_hard_face_covered: bool


@dataclass(frozen=True)
class PolylogGcdCollarOuterPntAudit:
    polylog_depth: int
    cofactor_power_exponent: Fraction
    cross_gcd_power_exponent: Fraction
    poisson_quotient_power_exponent: Fraction
    required_power_saving_exponent: Fraction
    primitive_unequal_product_factorization_exact: bool
    cross_gcd_product_identity_exact: bool
    prescribed_divisibility_coprime_pnt_available: bool
    arbitrary_log_saving_absorbs_polylog_variables: bool
    long_affine_mobius_sum_used_only_trivially: bool
    polylog_gcd_collar_closed_unconditionally: bool
    strict_positive_power_gcd_layers_covered: bool
    whole_signed_hard_face_covered: bool


@dataclass(frozen=True)
class StrictPowerGcdCoreAudit:
    collapsed_exponent: Fraction
    cofactor_exponent: Fraction
    gcd_exponent: Fraction
    quotient_exponent: Fraction
    left_cross_gcd_exponent: Fraction
    right_cross_gcd_exponent: Fraction
    left_reduced_slope_exponent: Fraction
    right_reduced_slope_exponent: Fraction
    left_reduced_signed_exponent: Fraction
    right_reduced_signed_exponent: Fraction
    unsigned_reduced_block_exponent: Fraction
    signed_reduced_block_exponent: Fraction
    reconstructed_gcd_exponent: Fraction
    raw_core_exponent: Fraction
    target_core_exponent: Fraction
    required_saving_exponent: Fraction
    exponent_polytope_feasible: bool
    unsigned_block_equals_full_deficit: bool
    all_allocations_and_ratio_integrals_retained: bool
    long_and_collapsed_arithmetic_weights_on_each_side: bool
    bblr_arbitrary_outer_coefficient_adapter_applies: bool
    centered_three_block_type_ii_required: bool
    centered_three_block_type_ii_proved: bool
    whole_signed_hard_face_covered: bool


@dataclass(frozen=True)
class StrictPowerConvolutionKloostermanAudit:
    collapsed_exponent: Fraction
    cofactor_exponent: Fraction
    gcd_exponent: Fraction
    quotient_exponent: Fraction
    left_cross_gcd_exponent: Fraction
    right_cross_gcd_exponent: Fraction
    left_convolved_outer_exponent: Fraction
    right_convolved_outer_exponent: Fraction
    left_inner_slope_exponent: Fraction
    right_inner_slope_exponent: Fraction
    side_product_exponent: Fraction
    remaining_outer_exponent: Fraction
    bblr_convolution_hypotheses_verified: bool
    bblr_ab_error_exponent: Fraction
    bblr_watt_error_exponent: Fraction
    bblr_inner_target_exponent: Fraction
    bblr_ab_deficit: Fraction
    bblr_watt_deficit: Fraction
    bblr_convolution_route_covered: bool
    poisson_dual_exponent: Fraction
    poisson_numerator_exponent: Fraction
    poisson_normalization_exponent: Fraction
    bc_poisson_hypotheses_verified: bool
    bc_first_total_exponent: Fraction
    bc_second_total_exponent: Fraction
    bc_first_deficit: Fraction
    bc_second_deficit: Fraction
    bc_poisson_route_covered: bool
    original_cross_diagonal_removed_by_centering: bool
    cauchy_tuple_diagonal_exponent: Fraction
    cauchy_grouped_diagonal_exponent: Fraction
    cauchy_diagonal_target_exponent: Fraction
    cauchy_grouped_diagonal_deficit: Fraction
    cauchy_grouped_diagonal_is_raw_scale: bool
    cauchy_grouped_diagonal_killed_by_centering: bool
    hard_vertex_inverse_zeta_square_variance: bool
    near_frequency_type_ii_proved: bool


@dataclass(frozen=True)
class StrictPowerRatioMellinBandwidthAudit:
    collapsed_exponent: Fraction
    cofactor_exponent: Fraction
    quotient_exponent: Fraction
    left_cross_gcd_exponent: Fraction
    right_cross_gcd_exponent: Fraction
    left_hidden_fibre_exponent: Fraction
    right_hidden_fibre_exponent: Fraction
    total_hidden_fibre_exponent: Fraction
    height_phase_log_derivative_power_exponent: Fraction
    ratio_weight_log_derivative_power_exponent: Fraction
    effective_mellin_frequency_power_exponent: Fraction
    left_adjacent_resolution_frequency_exponent: Fraction
    right_adjacent_resolution_frequency_exponent: Fraction
    remaining_cauchy_deficit_exponent: Fraction
    mellin_power_tail_is_rapid: bool
    scaled_T_tau_not_independent_bandwidth: bool
    height_phase_creates_second_power_coordinate: bool
    ratio_mellin_resolves_positive_hidden_fibres: bool
    ratio_mellin_supplies_required_delta_saving: bool
    pre_cauchy_joint_kernel_still_required: bool


@dataclass(frozen=True)
class StrictPowerDoublePoissonResonanceAudit:
    collapsed_exponent: Fraction
    cofactor_exponent: Fraction
    gcd_exponent: Fraction
    quotient_exponent: Fraction
    left_cross_gcd_exponent: Fraction
    right_cross_gcd_exponent: Fraction
    left_slope_exponent: Fraction
    right_slope_exponent: Fraction
    left_modulus_exponent: Fraction
    right_modulus_exponent: Fraction
    left_dual_exponent: Fraction
    right_dual_exponent: Fraction
    dual_side_product_exponent: Fraction
    resonance_shift_exponent: Fraction
    poisson_amplitude_exponent: Fraction
    overlap_integral_exponent: Fraction
    transformed_absolute_inner_exponent: Fraction
    original_inner_raw_exponent: Fraction
    absolute_transform_loss_exponent: Fraction
    transformed_global_absolute_exponent: Fraction
    global_target_exponent: Fraction
    transformed_required_saving_exponent: Fraction
    resonance_identity_exact: bool
    two_poisson_scales_exact: bool
    absolute_transform_loss_is_one_minus_delta_plus_theta: bool
    absolute_double_poisson_route_covered: bool
    pre_cauchy_signed_resonance_estimate_required: bool
    bblr_sharp_range_verified: bool
    bblr_ab_before_normalization_exponent: Fraction
    bblr_watt_before_normalization_exponent: Fraction
    transform_normalization_exponent: Fraction
    bblr_ab_total_exponent: Fraction
    bblr_watt_total_exponent: Fraction
    bblr_ab_deficit: Fraction
    bblr_watt_deficit: Fraction
    original_bblr_ab_deficit: Fraction
    original_bblr_watt_deficit: Fraction
    bblr_ab_deficit_is_invariant: bool
    bblr_watt_extra_deficit: Fraction
    bblr_watt_extra_deficit_is_nonnegative: bool
    double_poisson_improves_bblr: bool


@dataclass(frozen=True)
class TransitionLineFourierMicroarcAudit:
    denominator_gcd_exponent: Fraction
    denominator_cofactor_exponent: Fraction
    h_window_exponent: Fraction
    product_phase_scale_exponent: Fraction
    full_frequency_window_exponent: Fraction
    constant_phase_microarc_exponent: Fraction
    microarcs_in_full_window_exponent: Fraction
    fixed_g_raw_line_exponent: Fraction
    fixed_g_target_exponent: Fraction
    required_fixed_g_saving_exponent: Fraction
    separated_mertens_product_trivial_exponent: Fraction
    separated_mertens_product_target_exponent: Fraction
    required_mertens_product_saving_exponent: Fraction
    finite_fourier_orthogonality_exact: bool
    h_window_poisson_localization_exact: bool
    actual_coupled_weight_tensor_separated: bool
    nonzero_constant_tensor_mode_verified: bool
    microarc_mertens_reduction_is_actual_gate: bool
    whole_line_family_covered: bool


@dataclass(frozen=True)
class TransitionBalancedMobiusConvolutionAudit:
    denominator_gcd_exponent: Fraction
    cofactor_length_exponent: Fraction
    product_center_exponent: Fraction
    product_difference_exponent: Fraction
    raw_autocorrelation_exponent: Fraction
    diagonal_scale_target_exponent: Fraction
    required_variance_saving_exponent: Fraction
    optimistic_mangerel_bound_exponent: Fraction
    optimistic_mangerel_power_deficit: Fraction
    endpoint_taper_count_in_square: int
    product_energy_log_loss: int
    net_endpoint_log_saving: int
    finite_autocorrelation_identity_exact: bool
    fejer_short_interval_identity_exact: bool
    balanced_coefficient_is_multiplicative: bool
    exact_mellin_twisted_convolution_available: bool
    actual_coprimality_layers_aggregated: bool
    actual_coupled_kernel_nuclear_norm_verified: bool
    published_square_root_variance_proved: bool
    whole_line_family_covered: bool
    source: str


@dataclass(frozen=True)
class TransitionCoprimalityLayerAudit:
    denominator_gcd_exponent: Fraction
    cofactor_length_exponent: Fraction
    exact_three_indicator_expansion: bool
    non_g_prime_p2_coefficient: int
    non_g_prime_p3_coefficient: int
    non_g_prime_p4_coefficient: int
    non_g_absolute_euler_product_converges: bool
    g_prime_loss_is_subpolylogarithmic: bool
    lifted_kernel_dimension: int
    fourier_derivative_order: int
    determinant_cutoff_derivative_power_cost: Fraction
    lifted_kernel_fourier_nuclear_norm_verified: bool
    layer_density_aggregation_verified: bool
    required_layer_variance_saving_exponent: Fraction
    published_layer_variance_proved: bool
    actual_line_family_reduced_to_layered_variance: bool
    whole_line_family_covered: bool


@dataclass(frozen=True)
class TransitionMobiusDirichletFourthMomentAudit:
    denominator_gcd_exponent: Fraction
    cofactor_length_exponent: Fraction
    long_mobius_polynomial_exponent: Fraction
    product_polynomial_exponent: Fraction
    physical_height_exponent: Fraction
    dcv_coefficient_target_exponent: Fraction
    coefficient_to_moment_normalization_exponent: Fraction
    moment_target_exponent: Fraction
    generic_mean_value_exponent: Fraction
    generic_mean_value_power_deficit: Fraction
    exact_dirichlet_product_identity: bool
    exact_scaled_log_coordinate_kernel_inversion: bool
    transform_is_schwartz_localized_at_height_T: bool
    separated_transform_compactly_excludes_zero_frequency: bool
    coprimality_layers_already_aggregated: bool
    dcv_exact_mixed_fourth_moment_superposition: bool
    uniform_mixed_fourth_moment_sufficient_for_dcv: bool
    dcv_implies_each_separated_moment: bool
    symmetric_top_face_is_mobius_fourth_moment: bool
    published_mixed_fourth_moment_proved: bool
    whole_line_family_covered: bool
    source: str


@dataclass(frozen=True)
class TransitionMobiusLargeValueAudit:
    amplitude_exponent: Fraction
    unnormalized_fourth_moment_target_exponent: Fraction
    required_large_value_count_exponent: Fraction
    required_count_exponent_is_negative: bool
    classical_large_value_count_exponent: Fraction
    classical_fourth_contribution_exponent: Fraction
    guth_maynard_term1_contribution_exponent: Fraction
    guth_maynard_term2_contribution_exponent: Fraction
    guth_maynard_term3_contribution_exponent: Fraction
    guth_maynard_fourth_contribution_exponent: Fraction
    best_published_fourth_contribution_exponent: Fraction
    best_published_power_deficit: Fraction
    menon_positive_power_saving_exponent: Fraction
    componentwise_fourth_moment_pointwise_threshold: Fraction
    mobius_large_value_theorem_proved: bool
    power_boundary_covered: bool
    original_signed_dcv_requires_componentwise_large_values: bool
    whole_line_family_covered: bool
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


def transition_type_ii_determinant_audit(
    box: ExponentBox,
    *,
    b_exponent: Fraction,
) -> TransitionTypeIIDeterminantAudit:
    """Audit the exact determinant split after transition Type-II Cauchy.

    In the original coupled sum put ``r=a*b``, ``n_i=h_i*delta_i``
    and ``y_i=s_i*a_i`` after expanding the square in the common factor
    ``b``.  The common reciprocal phase is governed by
    ``Delta=n1*y2-n2*y1``.  The full zero ray has cardinality
    ``B*N*Y*T^epsilon`` by primitive-slope parametrization, not merely
    the literal identical-tuple cardinality.  For ``Delta != 0`` the
    reciprocity-expanded modulus is ``y1*y2`` and completion in that
    nonprimitive modulus has dual length ``Y^2/B``.
    """
    if not _is_large_q_afe_transition_face(box):
        raise ValueError("box is not on the large-q AFE transition face")
    b_range = (box.rho / 3, 2 * box.rho / 3)
    if not b_range[0] <= b_exponent <= b_range[1]:
        raise ValueError("b exponent lies outside the Type-II range")

    a_exponent = box.rho - b_exponent
    numerator_product = box.ell + box.h
    factorized_y = box.sigma + a_exponent
    zero_determinant = b_exponent + numerator_product + factorized_y
    square_target = (
        2 * box.rho + 2 * box.sigma
        - b_exponent
        - F(1, 250)
    )
    zero_margin = square_target - zero_determinant
    determinant_max = numerator_product + factorized_y
    modulus = 2 * factorized_y
    modulus_square_root = factorized_y
    b_gap = modulus_square_root - b_exponent
    completed_dual = modulus - b_exponent
    reaches_square_root = b_exponent >= modulus_square_root

    return TransitionTypeIIDeterminantAudit(
        b_exponent=b_exponent,
        a_exponent=a_exponent,
        numerator_product_exponent=numerator_product,
        factorized_y_exponent=factorized_y,
        full_zero_determinant_exponent=zero_determinant,
        square_target_exponent=square_target,
        full_zero_determinant_margin=zero_margin,
        nonzero_determinant_max_exponent=determinant_max,
        reciprocalized_y_modulus_exponent=modulus,
        y_modulus_square_root_exponent=modulus_square_root,
        b_below_y_modulus_square_root_gap=b_gap,
        y_modulus_completed_dual_length_exponent=completed_dual,
        full_zero_determinant_separate_majorant_closes=zero_margin > 0,
        y_modulus_fixed_b_interval_reaches_square_root=(
            reaches_square_root
        ),
        y_modulus_single_completion_supplies_saving=reaches_square_root,
        nonzero_determinant_gate_required=True,
        nonzero_determinant_estimate_proved=False,
        published_coverage=False,
    )


def transition_type_ii_lcm_completion_audit(
    box: ExponentBox,
    *,
    b_exponent: Fraction,
    gcd_s_exponent: Fraction,
) -> TransitionTypeIILcmCompletionAudit:
    """Use the primitive common-``b`` modulus ``lcm(s1,s2)``.

    Before reciprocity, the squared phase is a single reciprocal phase
    in ``b`` modulo ``lcm(s1,s2)``.  If ``(s1,s2)=T^gamma`` on the
    transition face, this modulus has exponent ``2-gamma``.  The
    Blomer--Pascadi Theorem 5.7 comparison uses the optimistic interval
    lengths ``M=c`` and ``N=c/B`` after completion; its largest
    dimensionless term has exponent ``c/4`` and hence does not improve
    the exact Kloosterman operator bound.
    """
    if not _is_large_q_afe_transition_face(box):
        raise ValueError("box is not on the large-q AFE transition face")
    b_range = (box.rho / 3, 2 * box.rho / 3)
    if not b_range[0] <= b_exponent <= b_range[1]:
        raise ValueError("b exponent lies outside the Type-II range")
    if gcd_s_exponent < 0 or gcd_s_exponent > box.sigma:
        raise ValueError("gcd exponent lies outside [0,sigma]")

    lcm_modulus = 2 * box.sigma - gcd_s_exponent
    modulus_square_root = lcm_modulus / 2
    b_gap = _positive_part(modulus_square_root - b_exponent)
    b_surplus = _positive_part(b_exponent - modulus_square_root)
    completed_dual = lcm_modulus - b_exponent
    bp_loss = lcm_modulus / 4
    nonzero_cardinality = (
        F(6) - b_exponent - gcd_s_exponent
    )
    square_target = (
        2 * box.rho + 2 * box.sigma
        - b_exponent
        - F(1, 250)
    )
    required_total_saving = nonzero_cardinality - square_target
    remaining_after_b = required_total_saving - b_surplus

    return TransitionTypeIILcmCompletionAudit(
        b_exponent=b_exponent,
        gcd_s_exponent=gcd_s_exponent,
        lcm_modulus_exponent=lcm_modulus,
        modulus_square_root_exponent=modulus_square_root,
        b_below_square_root_gap=b_gap,
        b_above_square_root_surplus=b_surplus,
        completed_dual_length_exponent=completed_dual,
        blomer_pascadi_dimensionless_loss=bp_loss,
        nonzero_cardinality_exponent=nonzero_cardinality,
        square_target_exponent=square_target,
        required_total_saving=required_total_saving,
        single_b_weil_saving=b_surplus,
        remaining_saving_after_single_b_completion=remaining_after_b,
        original_phase_compresses_to_lcm=True,
        fixed_b_completion_has_kinematic_saving=b_surplus > 0,
        fixed_b_completion_closes_square_target=remaining_after_b <= 0,
        squarefree_coprime_b_weight_is_smooth=False,
        blomer_pascadi_adapter_closes=False,
        published_coverage=False,
    )


def transition_long_cutoff_mobius_trace_audit(
    box: ExponentBox,
    *,
    cutoff_gap_exponent: Fraction,
    b_exponent: Fraction,
) -> TransitionLongCutoffMobiusTraceAudit:
    """Audit a long cutoff followed by Möbius--trace orthogonality.

    Put U=T^(rho-eta), r=a*b, and beta<=eta.  On squarefree support,
    complementing the divisor sum writes c_U(a) as -mu(a) times a
    divisor sum of reflected length T^(eta-beta).  Korolev--Shparlinski
    Theorem 2.1 supplies only a log-log over log saving, even when its
    prime-modulus and nonexceptional hypotheses are granted.  Two such
    optimistic logarithmic savings do not alter the positive power gap
    between the ambient transition sum and the fixed Type-II target.
    """
    if not _is_large_q_afe_transition_face(box):
        raise ValueError("box is not on the large-q AFE transition face")
    if cutoff_gap_exponent <= 0 or cutoff_gap_exponent >= box.rho:
        raise ValueError("cutoff gap must lie in (0,rho)")
    if b_exponent < 0 or b_exponent > cutoff_gap_exponent:
        raise ValueError("b exponent must lie in [0,cutoff gap]")

    cutoff_exponent = box.rho - cutoff_gap_exponent
    a_exponent = box.rho - b_exponent
    reflected = cutoff_gap_exponent - b_exponent
    trace_modulus = box.sigma
    trace_margin = a_exponent - trace_modulus / 2
    ambient = box.rho + box.sigma + box.ell + box.h
    fixed_target = box.rho + box.sigma - F(1, 500)
    power_deficit = ambient - fixed_target

    return TransitionLongCutoffMobiusTraceAudit(
        cutoff_gap_exponent=cutoff_gap_exponent,
        cutoff_exponent=cutoff_exponent,
        b_exponent=b_exponent,
        a_exponent=a_exponent,
        short_reflected_divisor_exponent=reflected,
        trace_modulus_exponent=trace_modulus,
        trace_length_over_sqrt_modulus_margin=trace_margin,
        ambient_unsquared_exponent=ambient,
        fixed_type_ii_target_exponent=fixed_target,
        remaining_power_deficit_after_two_log_savings=power_deficit,
        squarefree_reflection_identity_exact=True,
        published_theorem_requires_prime_modulus=True,
        all_actual_moduli_are_prime=False,
        nonexceptional_trace_hypothesis_uniform=False,
        two_logarithmic_savings_close_power_target=False,
        published_coverage=False,
        source="Korolev--Shparlinski, arXiv:1804.01337v2, Theorem 2.1",
    )


def transition_reciprocal_cluster_closure_audit(
    box: ExponentBox,
    *,
    distance_max: Fraction,
) -> TransitionReciprocalClusterClosureAudit:
    """Close the centered transition collar by reciprocity clustering.

    On the transition face S=H*L=T.  The clustered large-sieve bound is
    S*(H*L+D^2)^(1/2)*(H*L)^(1/2), hence has exponent two throughout
    D<=T^(1/2).  The exact product-coefficient energy costs one half
    logarithm, the dyadic D-union costs one logarithm, and the two
    endpoint mollifier tapers save two.  Since the dimensionless kernel
    parameters are all constant on this fixed face, no separation
    logarithm remains.  The q-cardinal aggregation is then
    O(T*log(T)^(-1/2)).
    """
    if not _is_large_q_afe_transition_face(box):
        raise ValueError("box is not on the large-q AFE transition face")
    if distance_max < 0 or distance_max > F(1, 2):
        raise ValueError("closure only applies for 0 <= Dmax <= 1/2")

    cluster = reciprocal_cluster_large_sieve_scales(
        box,
        distance=distance_max,
    )
    raw_gate = box.rho + box.sigma
    taper_log_saving = F(2)
    coefficient_log_loss = F(1, 2)
    shell_log_loss = F(1)
    kernel_log_loss = F(0)
    net_log_saving = (
        taper_log_saving
        - coefficient_log_loss
        - shell_log_loss
        - kernel_log_loss
    )
    low_union_covered = (
        cluster.remaining_power_saving == 0
        and net_log_saving > 0
    )

    return TransitionReciprocalClusterClosureAudit(
        distance_max=distance_max,
        numerator_product_exponent=box.ell + box.h,
        clustered_large_sieve_exponent=(
            cluster.clustered_large_sieve_bound
        ),
        raw_gate_exponent=raw_gate,
        remaining_power_deficit=cluster.remaining_power_saving,
        endpoint_taper_log_saving=taper_log_saving,
        product_coefficient_l2_log_loss=coefficient_log_loss,
        dyadic_distance_log_loss=shell_log_loss,
        dimensionless_kernel_log_loss=kernel_log_loss,
        net_log_saving=net_log_saving,
        global_remainder_power_exponent=F(1),
        reciprocity_cluster_identity_exact=True,
        product_coefficient_energy_bound_proved=True,
        fixed_transition_kernel_has_uniform_seminorms=True,
        low_difference_union_covered=low_union_covered,
        whole_transition_face_covered=False,
        residual_distance_open_interval=(F(1, 2), F(1)),
        residual_required_saving_at_top=F(1, 2),
    )


def transition_far_shell_mobius_gate_audit(
    box: ExponentBox,
    *,
    distance: Fraction,
    fkm_eta: Fraction,
    optimistic_fkm_applications: int,
) -> TransitionFarShellMobiusGateAudit:
    """State the surviving transition shell as one two-Möbius sum.

    For D=T^theta with theta>1/2, reciprocity clustering gives exponent
    3/2+theta.  The fixed coupled-kernel gate has exponent
    2-1/1000.  Fouvry--Kowalski--Michel can save eta*theta per
    optimistic application when a prime factor of exactly the requested
    size and every nonzero-frequency/cofactor hypothesis are granted.
    Those hypotheses are not uniform in the actual squarefree moduli.
    """
    if not _is_large_q_afe_transition_face(box):
        raise ValueError("box is not on the large-q AFE transition face")
    if distance <= F(1, 2) or distance > F(1):
        raise ValueError("far transition shell requires 1/2 < theta <= 1")
    if fkm_eta <= 0 or fkm_eta >= F(1, 24):
        raise ValueError("FKM eta must lie strictly between 0 and 1/24")
    if optimistic_fkm_applications not in (1, 2):
        raise ValueError("FKM applications must be one or two")

    cluster = reciprocal_cluster_large_sieve_scales(
        box,
        distance=distance,
    )
    fixed_target = box.rho + box.sigma - TARGET_SAVING
    required = cluster.best_unconditional_bound - fixed_target
    fkm_total = optimistic_fkm_applications * fkm_eta * distance
    residual = _positive_part(required - fkm_total)

    return TransitionFarShellMobiusGateAudit(
        distance=distance,
        shifted_variable_exponent=distance,
        modulus_exponent=box.sigma,
        product_frequency_exponent=box.ell + box.h,
        current_cluster_bound_exponent=cluster.best_unconditional_bound,
        fixed_gate_target_exponent=fixed_target,
        required_new_mobius_saving=required,
        fkm_eta=fkm_eta,
        optimistic_fkm_applications=optimistic_fkm_applications,
        optimistic_fkm_total_saving=fkm_total,
        residual_after_optimistic_fkm=residual,
        left_mobius_weight_retained=True,
        right_mobius_weight_retained=True,
        coupled_kernel_retained=True,
        uniform_prime_factor_hypothesis=False,
        nonzero_prime_frequency_uniform=False,
        joint_cofactor_hypothesis=False,
        new_joint_two_mobius_estimate_required=True,
        estimate_proved=False,
        published_coverage=False,
    )


def transition_far_shell_factor_box_audit(
    box: ExponentBox,
    *,
    distance: Fraction,
    b_exponent: Fraction,
) -> TransitionFarShellFactorBoxAudit:
    """Factor the surviving far shell by the exact Möbius identity.

    Use U=V=T^(rho/3), r=a*b=k*s+w, and dyadically localize
    b=T^beta.  The original reciprocal phase is unchanged because
    a*b is congruent to w modulo s.  Cauchy in b leaves an identity
    diagonal of exponent beta+(rho-beta)+distance+(ell+h).
    """
    if not _is_large_q_afe_transition_face(box):
        raise ValueError("box is not on the large-q AFE transition face")
    if distance <= F(1, 2) or distance > F(1):
        raise ValueError("far transition shell requires 1/2 < theta <= 1")
    cutoff = box.rho / 3
    b_range = (F(0), 2 * box.rho / 3)
    if not b_range[0] <= b_exponent <= b_range[1]:
        raise ValueError("b exponent lies outside the exact factor range")

    a_exponent = box.rho - b_exponent
    cluster = reciprocal_cluster_large_sieve_scales(
        box,
        distance=distance,
    )
    unsquared_target = box.rho + box.sigma - F(1, 500)
    unsquared_required = (
        cluster.best_unconditional_bound - unsquared_target
    )
    identity_diagonal = (
        b_exponent
        + a_exponent
        + distance
        + box.ell
        + box.h
    )
    square_target = 2 * unsquared_target - b_exponent
    diagonal_margin = square_target - identity_diagonal

    return TransitionFarShellFactorBoxAudit(
        distance=distance,
        mobius_cutoff_exponent=cutoff,
        type_split_exponent=cutoff,
        b_exponent=b_exponent,
        b_exponent_range=b_range,
        a_exponent=a_exponent,
        shifted_equation_is_exact=True,
        reciprocal_phase_reindexed_exactly=True,
        unsquared_cluster_bound_exponent=(
            cluster.best_unconditional_bound
        ),
        unsquared_fixed_target_exponent=unsquared_target,
        unsquared_required_saving=unsquared_required,
        identity_diagonal_exponent=identity_diagonal,
        type_ii_square_target_exponent=square_target,
        identity_diagonal_margin=diagonal_margin,
        identity_diagonal_closes=diagonal_margin > 0,
        nonzero_joint_gram_estimate_required=True,
        nonzero_joint_gram_estimate_proved=False,
        published_coverage=False,
    )


def transition_factor_square_geometry_audit(
    box: ExponentBox,
    *,
    distance: Fraction,
    b_exponent: Fraction,
) -> TransitionFactorSquareGeometryAudit:
    """Split the factor-box square by Gamma=a1*s2-a2*s1.

    The common-b equations w_i=a_i*b-k*s_i imply
    a2*w1-a1*w2=k*Gamma, so Gamma has exponent at most
    (rho-beta)+distance.  Gamma=0 forces the two primitive coprime
    pairs (a_i,s_i) to agree.  The remaining product-frequency
    offdiagonal is bounded in L2 by the same reciprocity-cluster energy,
    giving exponent 2+theta rather than the squared L1 exponent.
    """
    factor = transition_far_shell_factor_box_audit(
        box,
        distance=distance,
        b_exponent=b_exponent,
    )
    determinant_max = factor.a_exponent + distance
    zero_geometry = box.rho + box.ell + box.h + distance
    margin = factor.type_ii_square_target_exponent - zero_geometry

    return TransitionFactorSquareGeometryAudit(
        distance=distance,
        b_exponent=b_exponent,
        a_exponent=factor.a_exponent,
        geometric_determinant_max_exponent=determinant_max,
        full_zero_geometry_exponent=zero_geometry,
        type_ii_square_target_exponent=(
            factor.type_ii_square_target_exponent
        ),
        full_zero_geometry_margin=margin,
        common_b_cross_relation_exact=True,
        zero_determinant_primitive_pairs_identical=True,
        product_frequency_offdiagonal_retained=True,
        reciprocal_cluster_l2_applied_before_absolute_n_pairs=True,
        full_zero_geometry_closes=margin > 0,
        nonzero_geometric_determinant_gate_required=True,
        nonzero_geometric_determinant_gate_proved=False,
        published_coverage=False,
    )


def factor_determinant_orbit_parameter(
    *,
    a1: int,
    a2: int,
    s1: int,
    s2: int,
    other_s1: int,
    other_s2: int,
) -> int | None:
    """Recover the exact affine-orbit parameter at fixed determinant.

    Put d=gcd(a1,a2) and u_i=a_i/d.  Two integer pairs have the same
    determinant a1*s2-a2*s1 exactly when their difference is
    t*(u1,u2) for an integer t.  None records a different determinant
    or inconsistent coordinate quotients.
    """
    if min(a1, a2) <= 0:
        raise ValueError("factor entries must be positive")
    determinant = a1 * s2 - a2 * s1
    other_determinant = a1 * other_s2 - a2 * other_s1
    if determinant != other_determinant:
        return None

    common = gcd(a1, a2)
    u1 = a1 // common
    u2 = a2 // common
    delta_s1 = other_s1 - s1
    delta_s2 = other_s2 - s2
    if delta_s1 % u1 != 0 or delta_s2 % u2 != 0:
        return None
    t1 = delta_s1 // u1
    t2 = delta_s2 // u2
    return t1 if t1 == t2 else None


def signed_reciprocity_phase_identity(*, w: int, s: int, n: int) -> bool:
    """Verify reciprocity after moving the modulus from s to abs(w)."""
    if w == 0 or s <= 0:
        raise ValueError("reciprocity requires w nonzero and s positive")
    modulus_w = abs(w)
    if gcd(modulus_w, s) != 1:
        raise ValueError("reciprocity requires coprime entries")
    sign_w = 1 if w > 0 else -1
    inverse_w_mod_s = pow(w, -1, s)
    inverse_s_mod_w = pow(s, -1, modulus_w)
    left = Fraction(-n * inverse_w_mod_s, s)
    right = (
        Fraction(sign_w * n * inverse_s_mod_w, modulus_w)
        - Fraction(sign_w * n, modulus_w * s)
    )
    return (left - right).denominator == 1


def transition_nonzero_gamma_shell_audit(
    box: ExponentBox,
    *,
    distance: Fraction,
    b_exponent: Fraction,
    determinant_exponent: Fraction,
    s_gcd_exponent: Fraction,
    a_gcd_exponent: Fraction,
) -> TransitionNonzeroGammaShellAudit:
    """Record the exact final nonzero-Gamma factor-square shell.

    Here Gamma=a1*s2-a2*s1 and w_i=a_i*b-k*s_i.  The two equations
    imply a2*w1-a1*w2=k*Gamma.  Both gcds divide Gamma.  At fixed
    a1,a2,Gamma, the s-solutions form the primitive affine orbit with
    step (a1/d_a,a2/d_a); the two w windows shorten its parameter
    length to D/(A/d_a).

    The baseline square exponent is the square of the proved
    reciprocity-cluster bound, divided by the Cauchy length B.  The
    returned positive gap is the additional joint saving required from
    the nonzero determinant average; it is not asserted to be proved.
    """
    distance = F(distance)
    b_exponent = F(b_exponent)
    determinant_exponent = F(determinant_exponent)
    s_gcd_exponent = F(s_gcd_exponent)
    a_gcd_exponent = F(a_gcd_exponent)
    factor = transition_far_shell_factor_box_audit(
        box,
        distance=distance,
        b_exponent=b_exponent,
    )
    determinant_max = factor.a_exponent + distance
    if determinant_exponent < 0 or determinant_exponent > determinant_max:
        raise ValueError("determinant shell exceeds the exact support")
    if s_gcd_exponent < 0 or s_gcd_exponent > min(
        box.sigma,
        determinant_exponent,
    ):
        raise ValueError("s-gcd shell cannot divide the determinant")
    if a_gcd_exponent < 0 or a_gcd_exponent > min(
        factor.a_exponent,
        determinant_exponent,
    ):
        raise ValueError("a-gcd shell cannot divide the determinant")

    lcm_modulus = 2 * box.sigma - s_gcd_exponent
    b_dual = max(F(0), lcm_modulus - b_exponent)
    primitive_step = factor.a_exponent - a_gcd_exponent
    orbit_length = max(F(0), distance - primitive_step)
    cluster_square = (
        2 * factor.unsquared_cluster_bound_exponent - b_exponent
    )
    target = factor.type_ii_square_target_exponent

    return TransitionNonzeroGammaShellAudit(
        distance=distance,
        b_exponent=b_exponent,
        a_exponent=factor.a_exponent,
        determinant_exponent=determinant_exponent,
        determinant_exponent_range=(F(0), determinant_max),
        s_gcd_exponent=s_gcd_exponent,
        a_gcd_exponent=a_gcd_exponent,
        s_gcd_divides_determinant=True,
        a_gcd_divides_determinant=True,
        common_b_cross_relation_exact=True,
        lcm_modulus_exponent=lcm_modulus,
        b_completion_dual_exponent=b_dual,
        primitive_a_step_exponent=primitive_step,
        determinant_orbit_length_exponent=orbit_length,
        determinant_orbit_parametrization_exact=True,
        current_cluster_square_bound_exponent=cluster_square,
        cluster_square_bound_independently_proved=False,
        type_ii_square_target_exponent=target,
        required_joint_saving_exponent=cluster_square - target,
        reciprocity_modulus_exponent=distance,
        reciprocity_strictly_reduces_modulus=distance < box.sigma,
        both_s_mobius_weights_retained=True,
        product_frequency_pair_retained=True,
        coupled_kernel_retained=True,
        complete_nonzero_shell_estimate_required=True,
        complete_nonzero_shell_estimate_proved=False,
        published_coverage=False,
    )


def transition_gamma_graph_energy_audit(
    box: ExponentBox,
    *,
    distance: Fraction,
    b_exponent: Fraction,
    determinant_exponent: Fraction,
) -> TransitionGammaGraphEnergyAudit:
    """Close nonzero determinant shells by graph degree times cluster L2.

    For fixed b, make the factor pairs (a,s) vertices and join two
    vertices when their determinant lies in the selected dyadic shell.
    For fixed (a1,s1) and a2, the determinant window restricts s2 to
    length min(D,G/A).  Hence the maximum degree is

        A * (1 + min(D,G/A)).

    The elementary inequality for a graph of maximum degree Delta,
    sum_edges abs(z_x*z_y) <= Delta*sum_x abs(z_x)^2, then combines
    with the already proved reciprocal-cluster L2 energy.  No Mobius
    or inter-vertex phase cancellation is used.
    """
    distance = F(distance)
    b_exponent = F(b_exponent)
    determinant_exponent = F(determinant_exponent)
    factor = transition_far_shell_factor_box_audit(
        box,
        distance=distance,
        b_exponent=b_exponent,
    )
    determinant_max = factor.a_exponent + distance
    if determinant_exponent < 0 or determinant_exponent > determinant_max:
        raise ValueError("determinant shell exceeds the exact support")

    determinant_fiber = max(
        F(0),
        min(distance, determinant_exponent - factor.a_exponent),
    )
    maximum_degree = factor.a_exponent + determinant_fiber
    vertex_energy = box.rho + box.ell + box.h + distance
    graph_bound = vertex_energy + maximum_degree
    target = factor.type_ii_square_target_exponent
    margin = target - graph_bound
    coverage_lhs = distance + determinant_fiber
    coverage_threshold = F(1) - F(1, 250)

    return TransitionGammaGraphEnergyAudit(
        distance=distance,
        b_exponent=b_exponent,
        a_exponent=factor.a_exponent,
        determinant_exponent=determinant_exponent,
        determinant_max_exponent=determinant_max,
        determinant_fiber_exponent=determinant_fiber,
        maximum_graph_degree_exponent=maximum_degree,
        reciprocal_cluster_vertex_energy_exponent=vertex_energy,
        graph_energy_bound_exponent=graph_bound,
        type_ii_square_target_exponent=target,
        graph_energy_target_margin=margin,
        coverage_lhs=coverage_lhs,
        coverage_threshold=coverage_threshold,
        maximum_degree_energy_inequality_exact=True,
        product_frequency_cluster_l2_used=True,
        mobius_cancellation_used=False,
        phase_cancellation_between_distinct_vertices_used=False,
        shell_covered_unconditionally=margin >= 0,
        published_coverage=False,
    )


def transition_gamma_gcd_graph_energy_audit(
    box: ExponentBox,
    *,
    distance: Fraction,
    b_exponent: Fraction,
    determinant_exponent: Fraction,
    s_gcd_exponent: Fraction,
    a_gcd_exponent: Fraction,
) -> TransitionGammaGcdGraphEnergyAudit:
    """Sharpen the determinant graph degree on fixed gcd shells.

    For a fixed first vertex, d_a=(a1,a2) must be a divisor of a1 in
    the selected alpha shell, so a2 has only A/d_a candidates.  Likewise
    d_s=(s1,s2) is a divisor of s1, and the determinant interval for s2
    contains only 1+min(D,G/A)/d_s admissible multiples.  Divisor-shell
    choices cost T^epsilon and no cancellation.
    """
    distance = F(distance)
    b_exponent = F(b_exponent)
    determinant_exponent = F(determinant_exponent)
    s_gcd_exponent = F(s_gcd_exponent)
    a_gcd_exponent = F(a_gcd_exponent)
    shell = transition_nonzero_gamma_shell_audit(
        box,
        distance=distance,
        b_exponent=b_exponent,
        determinant_exponent=determinant_exponent,
        s_gcd_exponent=s_gcd_exponent,
        a_gcd_exponent=a_gcd_exponent,
    )

    raw_fiber = max(
        F(0),
        min(distance, determinant_exponent - shell.a_exponent),
    )
    reduced_fiber = max(F(0), raw_fiber - s_gcd_exponent)
    maximum_degree = (
        shell.a_exponent - a_gcd_exponent + reduced_fiber
    )
    vertex_energy = box.rho + box.ell + box.h + distance
    graph_bound = vertex_energy + maximum_degree
    target = shell.type_ii_square_target_exponent
    margin = target - graph_bound
    coverage_lhs = distance - a_gcd_exponent + reduced_fiber
    coverage_threshold = F(1) - F(1, 250)

    return TransitionGammaGcdGraphEnergyAudit(
        distance=distance,
        b_exponent=b_exponent,
        a_exponent=shell.a_exponent,
        determinant_exponent=determinant_exponent,
        s_gcd_exponent=s_gcd_exponent,
        a_gcd_exponent=a_gcd_exponent,
        raw_determinant_fiber_exponent=raw_fiber,
        gcd_reduced_fiber_exponent=reduced_fiber,
        maximum_graph_degree_exponent=maximum_degree,
        reciprocal_cluster_vertex_energy_exponent=vertex_energy,
        graph_energy_bound_exponent=graph_bound,
        type_ii_square_target_exponent=target,
        graph_energy_target_margin=margin,
        coverage_lhs=coverage_lhs,
        coverage_threshold=coverage_threshold,
        a_gcd_candidate_reduction_exact=True,
        s_gcd_fiber_reduction_exact=True,
        product_frequency_cluster_l2_used=True,
        mobius_cancellation_used=False,
        shell_covered_unconditionally=margin >= 0,
        published_coverage=False,
    )


def factor_cross_determinant_identity(
    *,
    a1: int,
    a2: int,
    s1: int,
    s2: int,
    b: int,
    k: int,
) -> dict[str, int | bool]:
    """Verify the exact (a,w) determinant and its bounded entry gcds."""
    if min(a1, a2, s1, s2, b) <= 0 or k == 0:
        raise ValueError("factor variables must be positive and k nonzero")
    if gcd(a1, s1) != 1 or gcd(a2, s2) != 1:
        raise ValueError("the factor entries must be primitive")
    w1 = a1 * b - k * s1
    w2 = a2 * b - k * s2
    gamma = a1 * s2 - a2 * s1
    cross = a2 * w1 - a1 * w2
    return {
        "w1": w1,
        "w2": w2,
        "gamma": gamma,
        "cross": cross,
        "cross_relation_exact": cross == k * gamma,
        "first_entry_gcd_divides_k": k % gcd(a1, abs(w1)) == 0,
        "second_entry_gcd_divides_k": k % gcd(a2, abs(w2)) == 0,
    }


def transition_cross_determinant_lattice_audit(
    box: ExponentBox,
    *,
    distance: Fraction,
    b_exponent: Fraction,
    determinant_exponent: Fraction,
) -> TransitionCrossDeterminantLatticeAudit:
    """Use the primitive (a,w) lattice to remove the rounding loss.

    The exact relation is a2*w1-a1*w2=k*Gamma.  Since
    gcd(a_i,w_i)=gcd(a_i,k*s_i) divides the fixed slope k, the linear
    form in (a2,w2) has bounded content.  Its intersection with the
    dyadic factor/shift rectangle has O_k(1) points for each fixed
    determinant value.  A Gamma shell of length T^xi therefore has
    maximum graph degree T^(xi+epsilon), including xi below A.
    """
    distance = F(distance)
    b_exponent = F(b_exponent)
    determinant_exponent = F(determinant_exponent)
    factor = transition_far_shell_factor_box_audit(
        box,
        distance=distance,
        b_exponent=b_exponent,
    )
    determinant_max = factor.a_exponent + distance
    if determinant_exponent < 0 or determinant_exponent > determinant_max:
        raise ValueError("determinant shell exceeds the exact support")

    degree = determinant_exponent
    vertex_energy = box.rho + box.ell + box.h + distance
    graph_bound = vertex_energy + degree
    target = factor.type_ii_square_target_exponent
    margin = target - graph_bound
    coverage_lhs = distance + determinant_exponent
    coverage_threshold = F(2) - b_exponent - F(1, 250)

    return TransitionCrossDeterminantLatticeAudit(
        distance=distance,
        b_exponent=b_exponent,
        a_exponent=factor.a_exponent,
        determinant_exponent=determinant_exponent,
        maximum_graph_degree_exponent=degree,
        reciprocal_cluster_vertex_energy_exponent=vertex_energy,
        graph_energy_bound_exponent=graph_bound,
        type_ii_square_target_exponent=target,
        graph_energy_target_margin=margin,
        coverage_lhs=coverage_lhs,
        coverage_threshold=coverage_threshold,
        cross_determinant_relation_exact=True,
        entry_gcd_bounded_by_fixed_slope=True,
        fixed_value_fiber_has_bounded_cardinality=True,
        product_frequency_cluster_l2_used=True,
        mobius_cancellation_used=False,
        shell_covered_unconditionally=margin >= 0,
        published_coverage=False,
    )


def factor_farey_hecke_orbit_identity(
    *,
    a1: int,
    a2: int,
    s1: int,
    s2: int,
    b: int,
    k: int,
    n1: int,
    n2: int,
) -> dict[str, int | bool]:
    """Verify the signed determinant orbit and the complete square phase."""
    if min(a1, a2, s1, s2, b) <= 0 or k == 0:
        raise ValueError("factor variables must be positive and k nonzero")
    w1 = a1 * b - k * s1
    w2 = a2 * b - k * s2
    if w1 == 0 or w2 == 0:
        raise ValueError("the far-shell shifts must be nonzero")
    if gcd(s1, abs(w1)) != 1 or gcd(s2, abs(w2)) != 1:
        raise ValueError("reciprocity requires primitive entry pairs")

    epsilon1 = 1 if w1 > 0 else -1
    epsilon2 = 1 if w2 > 0 else -1
    modulus1 = abs(w1)
    modulus2 = abs(w2)
    x1 = epsilon1 * s1
    x2 = epsilon2 * s2
    gamma = a1 * s2 - a2 * s1
    hecke_determinant = x1 * modulus2 - x2 * modulus1
    expected_determinant = -epsilon1 * epsilon2 * b * gamma

    original_phase = (
        Fraction(-n1 * pow(w1, -1, s1), s1)
        + Fraction(n2 * pow(w2, -1, s2), s2)
    )
    reciprocal_phase = (
        Fraction(n1 * pow(x1, -1, modulus1), modulus1)
        - Fraction(n2 * pow(x2, -1, modulus2), modulus2)
        - Fraction(n1, s1 * w1)
        + Fraction(n2, s2 * w2)
    )
    cofactor1_numerator = epsilon1 * (modulus1 + k * x1)
    cofactor2_numerator = epsilon2 * (modulus2 + k * x2)

    return {
        "w1": w1,
        "w2": w2,
        "x1": x1,
        "x2": x2,
        "hecke_determinant": hecke_determinant,
        "expected_determinant": expected_determinant,
        "hecke_determinant_exact": (
            hecke_determinant == expected_determinant
        ),
        "reciprocal_square_phase_exact": (
            (original_phase - reciprocal_phase).denominator == 1
        ),
        "first_affine_cofactor_exact": (
            cofactor1_numerator == a1 * b
        ),
        "second_affine_cofactor_exact": (
            cofactor2_numerator == a2 * b
        ),
    }


def transition_farey_hecke_orbit_audit(
    box: ExponentBox,
    *,
    distance: Fraction,
    b_exponent: Fraction,
    determinant_exponent: Fraction,
) -> TransitionFareyHeckeOrbitAudit:
    """Record the exact generalized Kloosterman orbit of the residual.

    With W_i=abs(w_i) and x_i=sgn(w_i)*s_i, the determinant is
    -sgn(w1*w2)*b*Gamma and the reciprocal phases have moduli W_i.
    The Cauchy step changes mu(b) to mu(b)^2, so the Hecke index has no
    Mobius weight.  The two surviving Mobius weights are on the residue
    entries x_i, while c_U(a_i) depends jointly on
    a_i=sgn(w_i)*(W_i+k*x_i)/b.  This is not a classical free
    Kuznetsov coefficient family.
    """
    distance = F(distance)
    b_exponent = F(b_exponent)
    determinant_exponent = F(determinant_exponent)
    shell = transition_nonzero_gamma_shell_audit(
        box,
        distance=distance,
        b_exponent=b_exponent,
        determinant_exponent=determinant_exponent,
        s_gcd_exponent=F(0),
        a_gcd_exponent=F(0),
    )

    return TransitionFareyHeckeOrbitAudit(
        distance=distance,
        b_exponent=b_exponent,
        determinant_exponent=determinant_exponent,
        hecke_index_exponent=b_exponent + determinant_exponent,
        entry_exponent=box.sigma,
        modulus_exponent=distance,
        product_frequency_exponent=box.ell + box.h,
        type_ii_square_target_exponent=(
            shell.type_ii_square_target_exponent
        ),
        signed_entry_determinant_exact=True,
        reciprocal_square_phase_exact=True,
        hecke_index_contains_common_b=True,
        common_b_weight_is_mobius_squared=True,
        hecke_index_has_mobius_weight=False,
        both_entry_mobius_weights_retained=True,
        affine_cofactor_weights_joint_in_entry_and_modulus=True,
        archimedean_reciprocity_correction_retained=True,
        coupled_kernel_retained=True,
        classical_kuznetsov_adapter_verified=False,
        new_entry_weighted_hecke_estimate_required=True,
        new_entry_weighted_hecke_estimate_proved=False,
        published_coverage=False,
    )


def entry_double_reciprocity_identity(
    *,
    c: int,
    d: int,
    modulus: int,
    epsilon: int,
    n: int,
) -> bool:
    """Verify cancellation of the first reciprocity correction."""
    if min(c, d, modulus) <= 0 or epsilon not in (-1, 1):
        raise ValueError("positive factors and a sign are required")
    entry = c * d
    if gcd(entry, modulus) != 1:
        raise ValueError("double reciprocity requires coprime entries")
    farey_phase = (
        Fraction(
            epsilon * n * pow(entry, -1, modulus),
            modulus,
        )
        - Fraction(epsilon * n, entry * modulus)
    )
    fixed_factor_phase = Fraction(
        -epsilon * n * pow(modulus, -1, entry),
        entry,
    )
    return (farey_phase - fixed_factor_phase).denominator == 1


def transition_entry_mobius_factorization_audit(
    box: ExponentBox,
    *,
    distance: Fraction,
    b_exponent: Fraction,
    entry_short_factor_exponent: Fraction,
) -> TransitionEntryMobiusFactorizationAudit:
    """Audit a second Type-I/II split on one residue-entry Mobius weight.

    Write abs(x)=c*d with d of exponent eta and c of exponent 1-eta.
    Double reciprocity turns the Farey phase into one with modulus c*d
    and fixed factor c.  The optimistic Wright ledger includes the
    outer trivial c-sum.  The actual affine cofactor and shifted window
    remain joint, so even a favorable exponent would not by itself be
    an application.
    """
    distance = F(distance)
    b_exponent = F(b_exponent)
    eta = F(entry_short_factor_exponent)
    cutoff = box.sigma / 3
    if eta < 0 or eta > 2 * box.sigma / 3:
        raise ValueError("entry short factor lies outside the exact split")
    long_factor = box.sigma - eta
    wright_box = ExponentBox(
        box.sigma,
        distance,
        box.m,
        box.k,
        box.ell,
        box.h,
        box.kappa,
    )
    wright = wright_type_i_adapter(
        wright_box,
        a_factor=long_factor,
        b_factor=eta,
    )
    assert wright.saving is not None
    target_saving = F(1, 500)
    deficit = target_saving - wright.saving

    return TransitionEntryMobiusFactorizationAudit(
        distance=distance,
        b_exponent=b_exponent,
        entry_cutoff_exponent=cutoff,
        entry_long_factor_exponent=long_factor,
        entry_short_factor_exponent=eta,
        fixed_denominator_factor_exponent=long_factor,
        wright_size_hypothesis_holds=distance <= 2 * eta,
        optimistic_wright_saving_exponent=wright.saving,
        factor_box_target_saving_exponent=target_saving,
        optimistic_wright_deficit=deficit,
        mobius_factorization_exact=True,
        double_reciprocity_cancels_archimedean_term=True,
        affine_cofactor_remains_joint=True,
        shift_window_remains_joint=True,
        coupled_kernel_remains_joint=True,
        actual_wright_coefficient_hypotheses_verified=False,
        two_entry_type_ii_estimate_required=True,
        two_entry_type_ii_estimate_proved=False,
        published_coverage=False,
    )


def factor_cross_gcd_divisibility(
    *,
    a1: int,
    a2: int,
    s1: int,
    s2: int,
    b: int,
    k: int,
) -> dict[str, int | bool]:
    """Verify the combined a- and w-gcd divisor of k*Gamma."""
    if min(a1, a2, s1, s2, b) <= 0 or k == 0:
        raise ValueError("factor variables must be positive and k nonzero")
    if gcd(a1, s1) != 1 or gcd(a2, s2) != 1:
        raise ValueError("the factor entries must be primitive")
    w1 = a1 * b - k * s1
    w2 = a2 * b - k * s2
    if w1 == 0 or w2 == 0:
        raise ValueError("the far-shell shifts must be nonzero")
    gamma = a1 * s2 - a2 * s1
    a_gcd = gcd(a1, a2)
    w_gcd = gcd(abs(w1), abs(w2))
    common = gcd(a_gcd, w_gcd)
    combined = a_gcd * w_gcd // common
    return {
        "a_gcd": a_gcd,
        "w_gcd": w_gcd,
        "a_w_common_gcd": common,
        "combined_gcd": combined,
        "gamma": gamma,
        "a_w_common_gcd_divides_k": k % common == 0,
        "combined_gcd_divides_k_gamma": (
            (k * gamma) % combined == 0
        ),
    }


def transition_cross_gcd_lattice_audit(
    box: ExponentBox,
    *,
    distance: Fraction,
    b_exponent: Fraction,
    determinant_exponent: Fraction,
    a_gcd_exponent: Fraction,
    w_gcd_exponent: Fraction,
) -> TransitionCrossGcdLatticeAudit:
    """Sharpen the primitive cross lattice by both pairwise gcd shells.

    The gcds d_a=(a1,a2) and d_w=(w1,w2) both divide k*Gamma.  Their
    common gcd divides gcd(a1,w1), hence the fixed slope k.  Up to this
    bounded content, d_a*d_w divides k*Gamma.  The number of determinant
    values in a T^xi shell is therefore T^((xi-alpha-omega)_+).
    Each fixed value still has O_k(1) points in the dyadic rectangle.
    """
    distance = F(distance)
    b_exponent = F(b_exponent)
    determinant_exponent = F(determinant_exponent)
    a_gcd_exponent = F(a_gcd_exponent)
    w_gcd_exponent = F(w_gcd_exponent)
    factor = transition_far_shell_factor_box_audit(
        box,
        distance=distance,
        b_exponent=b_exponent,
    )
    determinant_max = factor.a_exponent + distance
    if determinant_exponent < 0 or determinant_exponent > determinant_max:
        raise ValueError("determinant shell exceeds the exact support")
    if a_gcd_exponent < 0 or a_gcd_exponent > factor.a_exponent:
        raise ValueError("a-gcd shell exceeds the factor length")
    if w_gcd_exponent < 0 or w_gcd_exponent > distance:
        raise ValueError("w-gcd shell exceeds the shift length")
    if a_gcd_exponent + w_gcd_exponent > determinant_exponent:
        raise ValueError("combined gcd cannot divide the determinant shell")

    reduced_values = max(
        F(0),
        determinant_exponent - a_gcd_exponent - w_gcd_exponent,
    )
    vertex_energy = box.rho + box.ell + box.h + distance
    graph_bound = vertex_energy + reduced_values
    target = factor.type_ii_square_target_exponent
    margin = target - graph_bound
    coverage_lhs = distance + reduced_values
    coverage_threshold = F(2) - b_exponent - F(1, 250)

    return TransitionCrossGcdLatticeAudit(
        distance=distance,
        b_exponent=b_exponent,
        determinant_exponent=determinant_exponent,
        a_gcd_exponent=a_gcd_exponent,
        w_gcd_exponent=w_gcd_exponent,
        reduced_determinant_value_exponent=reduced_values,
        maximum_graph_degree_exponent=reduced_values,
        reciprocal_cluster_vertex_energy_exponent=vertex_energy,
        graph_energy_bound_exponent=graph_bound,
        type_ii_square_target_exponent=target,
        graph_energy_target_margin=margin,
        coverage_lhs=coverage_lhs,
        coverage_threshold=coverage_threshold,
        a_w_common_gcd_is_slope_bounded=True,
        combined_gcd_divides_determinant=True,
        fixed_value_fiber_has_bounded_cardinality=True,
        product_frequency_cluster_l2_used=True,
        mobius_cancellation_used=False,
        shell_covered_unconditionally=margin >= 0,
        published_coverage=False,
    )


def factor_triple_gcd_divisibility(
    *,
    a1: int,
    a2: int,
    s1: int,
    s2: int,
    b: int,
    k: int,
) -> dict[str, int | bool]:
    """Verify the combined a-, s-, and w-gcd divisor of k*Gamma."""
    if min(a1, a2, s1, s2, b) <= 0 or k == 0:
        raise ValueError("factor variables must be positive and k nonzero")
    if gcd(a1, s1) != 1 or gcd(a2, s2) != 1:
        raise ValueError("the factor entries must be primitive")
    w1 = a1 * b - k * s1
    w2 = a2 * b - k * s2
    if w1 == 0 or w2 == 0:
        raise ValueError("the far-shell shifts must be nonzero")
    if gcd(s1, abs(w1)) != 1 or gcd(s2, abs(w2)) != 1:
        raise ValueError("the shifted entry pairs must be primitive")
    gamma = a1 * s2 - a2 * s1
    a_gcd = gcd(a1, a2)
    s_gcd = gcd(s1, s2)
    w_gcd = gcd(abs(w1), abs(w2))
    a_w_common = gcd(a_gcd, w_gcd)
    combined = a_gcd * s_gcd * w_gcd // a_w_common
    return {
        "a_gcd": a_gcd,
        "s_gcd": s_gcd,
        "w_gcd": w_gcd,
        "combined_gcd": combined,
        "gamma": gamma,
        "a_s_gcds_coprime": gcd(a_gcd, s_gcd) == 1,
        "s_w_gcds_coprime": gcd(s_gcd, w_gcd) == 1,
        "a_w_common_gcd_divides_k": k % a_w_common == 0,
        "triple_gcd_divides_k_gamma": (
            (k * gamma) % combined == 0
        ),
    }


def transition_triple_gcd_lattice_audit(
    box: ExponentBox,
    *,
    distance: Fraction,
    b_exponent: Fraction,
    determinant_exponent: Fraction,
    a_gcd_exponent: Fraction,
    s_gcd_exponent: Fraction,
    w_gcd_exponent: Fraction,
) -> TransitionTripleGcdLatticeAudit:
    """Combine every pairwise gcd available in the determinant lattice."""
    distance = F(distance)
    b_exponent = F(b_exponent)
    determinant_exponent = F(determinant_exponent)
    a_gcd_exponent = F(a_gcd_exponent)
    s_gcd_exponent = F(s_gcd_exponent)
    w_gcd_exponent = F(w_gcd_exponent)
    factor = transition_far_shell_factor_box_audit(
        box,
        distance=distance,
        b_exponent=b_exponent,
    )
    determinant_max = factor.a_exponent + distance
    if determinant_exponent < 0 or determinant_exponent > determinant_max:
        raise ValueError("determinant shell exceeds the exact support")
    if a_gcd_exponent < 0 or a_gcd_exponent > factor.a_exponent:
        raise ValueError("a-gcd shell exceeds the factor length")
    if s_gcd_exponent < 0 or s_gcd_exponent > box.sigma:
        raise ValueError("s-gcd shell exceeds the entry length")
    if w_gcd_exponent < 0 or w_gcd_exponent > distance:
        raise ValueError("w-gcd shell exceeds the shift length")
    gcd_total = (
        a_gcd_exponent + s_gcd_exponent + w_gcd_exponent
    )
    if gcd_total > determinant_exponent:
        raise ValueError("triple gcd cannot divide the determinant shell")

    reduced_values = max(F(0), determinant_exponent - gcd_total)
    vertex_energy = box.rho + box.ell + box.h + distance
    graph_bound = vertex_energy + reduced_values
    target = factor.type_ii_square_target_exponent
    margin = target - graph_bound
    coverage_lhs = distance + reduced_values
    coverage_threshold = F(2) - b_exponent - F(1, 250)

    return TransitionTripleGcdLatticeAudit(
        distance=distance,
        b_exponent=b_exponent,
        determinant_exponent=determinant_exponent,
        a_gcd_exponent=a_gcd_exponent,
        s_gcd_exponent=s_gcd_exponent,
        w_gcd_exponent=w_gcd_exponent,
        reduced_determinant_value_exponent=reduced_values,
        maximum_graph_degree_exponent=reduced_values,
        reciprocal_cluster_vertex_energy_exponent=vertex_energy,
        graph_energy_bound_exponent=graph_bound,
        type_ii_square_target_exponent=target,
        graph_energy_target_margin=margin,
        coverage_lhs=coverage_lhs,
        coverage_threshold=coverage_threshold,
        a_s_gcds_coprime=True,
        s_w_gcds_coprime=True,
        a_w_common_gcd_is_slope_bounded=True,
        triple_gcd_divides_determinant=True,
        product_frequency_cluster_l2_used=True,
        mobius_cancellation_used=False,
        shell_covered_unconditionally=margin >= 0,
        published_coverage=False,
    )


def transition_final_two_entry_gate_audit(
    box: ExponentBox,
    *,
    distance: Fraction,
    b_exponent: Fraction,
    determinant_exponent: Fraction,
    a_gcd_exponent: Fraction,
    s_gcd_exponent: Fraction,
    w_gcd_exponent: Fraction,
) -> TransitionFinalTwoEntryGateAudit:
    """Normalize the residual to one full two-entry square-root estimate.

    The triple-gcd graph bound has exponent 2+theta+rho_Gamma.  Saving
    one full power of T corresponds to square-root cancellation in each
    of the two length-T Mobius residue entries.  The resulting exponent
    is at most the raw Type-II square target 4-beta.  Equality occurs
    only at theta=1, maximal determinant, and zero total gcd exponent.

    On that face the four squared endpoint tapers save log^4, the
    product-frequency energy loses log^1, Cauchy halves the remaining
    log^3, and the beta-box union loses one log.  The net log saving is
    therefore 1/2, provided the new arithmetic estimate has no fixed
    positive log-power loss.
    """
    distance = F(distance)
    b_exponent = F(b_exponent)
    determinant_exponent = F(determinant_exponent)
    a_gcd_exponent = F(a_gcd_exponent)
    s_gcd_exponent = F(s_gcd_exponent)
    w_gcd_exponent = F(w_gcd_exponent)
    factor = transition_far_shell_factor_box_audit(
        box,
        distance=distance,
        b_exponent=b_exponent,
    )
    determinant_max = factor.a_exponent + distance
    if determinant_exponent < 0 or determinant_exponent > determinant_max:
        raise ValueError("determinant shell exceeds the exact support")
    total_gcd = (
        a_gcd_exponent + s_gcd_exponent + w_gcd_exponent
    )
    if min(a_gcd_exponent, s_gcd_exponent, w_gcd_exponent) < 0:
        raise ValueError("gcd exponents must be nonnegative")
    if total_gcd > determinant_exponent:
        raise ValueError("triple gcd cannot divide the determinant shell")

    reduced = determinant_exponent - total_gcd
    graph_bound = F(2) + distance + reduced
    square_root_saving = F(1)
    required_bound = graph_bound - square_root_saving
    raw_target = F(4) - b_exponent
    margin = raw_target - required_bound
    expected_margin = (
        2 * (F(1) - distance)
        + (F(1) - b_exponent + distance - determinant_exponent)
        + total_gcd
    )
    critical = (
        distance == F(1)
        and determinant_exponent == determinant_max
        and total_gcd == 0
    )
    taper_log = F(4)
    product_log = F(1)
    post_cauchy_log = (taper_log - product_log) / 2
    beta_union_log = F(1)
    global_net_log = post_cauchy_log - beta_union_log

    return TransitionFinalTwoEntryGateAudit(
        distance=distance,
        b_exponent=b_exponent,
        determinant_exponent=determinant_exponent,
        total_gcd_exponent=total_gcd,
        reduced_determinant_exponent=reduced,
        current_graph_bound_exponent=graph_bound,
        two_entry_square_root_saving_exponent=square_root_saving,
        required_two_entry_bound_exponent=required_bound,
        raw_type_ii_square_target_exponent=raw_target,
        power_margin=margin,
        margin_identity_exact=margin == expected_margin,
        is_unique_power_critical_face=critical,
        endpoint_taper_square_log_saving=taper_log,
        product_energy_log_loss=product_log,
        post_cauchy_log_saving=post_cauchy_log,
        beta_box_union_log_loss=beta_union_log,
        global_net_log_saving=global_net_log,
        global_remainder_power_exponent=F(1),
        two_entry_square_root_gate_required=True,
        two_entry_square_root_gate_proved=False,
        whole_transition_face_covered=False,
    )


def transition_h_poisson_line_identity(
    *,
    k: int,
    v0: int,
    j0: int,
    x: int,
    y: int,
    delta0: int,
    n: int,
) -> dict[str, int | bool]:
    """Verify the exact determinant line after Poisson summation in h.

    The primitive dual slope satisfies ``x*v0+y*j0=1``.  All solutions
    of ``w*v0-j0*s=delta0`` are

    ``w=x*delta0+j0*n`` and ``s=-y*delta0+v0*n``.

    With ``r=k*s+w``, the coefficient matrix carrying ``(delta0,n)``
    to the two Mobius entries ``(s,r)`` has determinant exactly ``-1``.
    """
    if k == 0 or v0 == 0 or j0 == 0:
        raise ValueError("the far-shell slope and primitive duals are nonzero")
    bezout = x * v0 + y * j0
    if bezout != 1:
        raise ValueError("x*v0+y*j0 must equal one")
    w = x * delta0 + j0 * n
    s = -y * delta0 + v0 * n
    r = k * s + w
    determinant = (-y) * (j0 + k * v0) - v0 * (x - k * y)
    return {
        "w": w,
        "s": s,
        "r": r,
        "bezout_identity_exact": bezout == 1,
        "determinant_equation_exact": w * v0 - j0 * s == delta0,
        "mobius_entry_matrix_determinant": determinant,
        "mobius_entry_change_is_unimodular": determinant == -1,
    }


def transition_h_poisson_line_audit(
    *,
    distance: Fraction,
    gcd_exponent: Fraction,
) -> TransitionHPoissonLineAudit:
    """Audit the determinant line obtained by exact h-Poisson summation.

    On a far shell ``w=T^theta`` with ``1/2 < theta <= 1``, Poisson in
    ``h=T^(1/2)`` gives ``v=T^(1/2)``, ``j=T^(theta-1/2)`` and
    ``w*v-j*s=delta`` with ``delta=T^(1/2)``.  On
    ``g=gcd(|v|,|j|)=T^gamma``, divide by ``g`` and use the exact
    determinant-line parametrization.  Its ``(delta0,n)`` area is
    always ``T`` and the map to the two Mobius entries is unimodular.

    The returned square-root estimate remains a theorem interface.  It
    has positive power slack off ``theta=1,gamma=0`` but is not marked
    as proved.  At the maximal gcd ``gamma=theta-1/2`` the absolute
    count itself reaches the power target; the two existing endpoint
    mollifier tapers then close that single layer logarithmically.
    """
    distance = F(distance)
    gcd_exponent = F(gcd_exponent)
    if distance <= F(1, 2) or distance > F(1):
        raise ValueError("distance must lie on the transition far shell")
    dual_v = F(1, 2)
    dual_j = distance - F(1, 2)
    gcd_max = min(dual_v, dual_j, F(1, 2))
    if gcd_exponent < 0 or gcd_exponent > gcd_max:
        raise ValueError("common gcd exceeds the transition dual ranges")

    primitive_v = dual_v - gcd_exponent
    primitive_j = dual_j - gcd_exponent
    shift_quotient = F(1, 2) - gcd_exponent
    line_parameter = F(1, 2) + gcd_exponent
    inner_area = shift_quotient + line_parameter
    outer_family = gcd_exponent + primitive_v + primitive_j
    pre_poisson = outer_family + inner_area
    poisson_factor = F(1, 2)
    absolute_post_poisson = poisson_factor + pre_poisson
    target = F(2)
    required_saving = _positive_part(absolute_post_poisson - target)
    square_root_saving = inner_area / 2
    square_root_margin = square_root_saving - required_saving
    critical = distance == F(1) and gcd_exponent == 0
    absolute_reaches = absolute_post_poisson <= target
    maximal_gcd = gcd_exponent == gcd_max

    return TransitionHPoissonLineAudit(
        distance=distance,
        common_gcd_exponent=gcd_exponent,
        h_poisson_factor_exponent=poisson_factor,
        dual_v_exponent=dual_v,
        dual_j_exponent=dual_j,
        primitive_v_exponent=primitive_v,
        primitive_j_exponent=primitive_j,
        shift_quotient_exponent=shift_quotient,
        line_parameter_exponent=line_parameter,
        inner_delta_n_area_exponent=inner_area,
        outer_slope_family_exponent=outer_family,
        pre_poisson_layer_cardinality_exponent=pre_poisson,
        absolute_post_poisson_exponent=absolute_post_poisson,
        asymptotic_local_target_exponent=target,
        required_inner_saving_exponent=required_saving,
        inner_square_root_saving_exponent=square_root_saving,
        square_root_power_margin=square_root_margin,
        determinant_line_parametrization_exact=True,
        mobius_entry_change_is_unimodular=True,
        is_unique_power_critical_layer=critical,
        absolute_count_reaches_power_target=absolute_reaches,
        maximal_gcd_layer_closes_with_endpoint_tapers=(
            maximal_gcd and absolute_reaches
        ),
        fixed_slope_square_root_proved=False,
        averaged_slope_square_function_proved=False,
        whole_far_shell_covered=False,
    )


def transition_h_poisson_square_cramer_identity(
    *,
    k: int,
    s1: int,
    w1: int,
    s2: int,
    w2: int,
    v: int,
    j: int,
) -> dict[str, int | bool]:
    """Verify Cramer recovery in the critical h-Poisson square."""
    if min(s1, s2) <= 0 or k == 0:
        raise ValueError("transition denominators and slope must be nonzero")
    if gcd(s1, abs(w1)) != 1 or gcd(s2, abs(w2)) != 1:
        raise ValueError("the two determinant rows must be primitive")
    r1 = k * s1 + w1
    r2 = k * s2 + w2
    delta1 = w1 * v - j * s1
    delta2 = w2 * v - j * s2
    cross = r1 * s2 - r2 * s1
    coefficient_determinant = s1 * w2 - w1 * s2
    if cross == 0:
        raise ValueError("Cramer recovery requires nonzero cross determinant")
    v_numerator = s2 * delta1 - s1 * delta2
    j_numerator = w2 * delta1 - w1 * delta2
    return {
        "r1": r1,
        "r2": r2,
        "delta1": delta1,
        "delta2": delta2,
        "cross_determinant": cross,
        "coefficient_determinant": coefficient_determinant,
        "recovered_v": v_numerator // cross,
        "recovered_j": j_numerator // cross,
        "cramer_divisibilities_exact": (
            v_numerator % cross == 0 and j_numerator % cross == 0
        ),
        "dual_slope_recovered_exactly": (
            v_numerator == cross * v and j_numerator == cross * j
        ),
    }


def transition_h_poisson_square_offdiagonal_audit(
) -> TransitionHPoissonSquareOffdiagonalAudit:
    """Specialize the cross-determinant square to theta=1 and g=1.

    The primitive slope pair has cardinality ``T`` and each inner
    determinant line has area ``T``.  Its expanded square therefore has
    exponent three, while the identity diagonal and desired square
    function both have exponent two.  The fraction collar forces
    ``Delta=r1*s2-r2*s1`` to have exponent at most one.  On the top
    determinant shell, Smith normal form gives one cyclic character
    family of size ``T``.  A character square root saves ``T^(1/2)``;
    the remaining ``T^(1/2)`` must come from the four Mobius-weighted
    Hecke matrix entries and the coupled kernel.
    """
    transition_box = ExponentBox(
        F(1), F(1), F(1, 2), F(1, 2),
        F(1, 2), F(1, 2), F(2),
    )
    offdiagonal = endpoint_slope_offdiagonal_audit(
        transition_box,
        gcd_exponent=F(0),
    )
    cokernel = endpoint_cokernel_character_audit(
        transition_box,
        gcd_exponent=F(0),
        determinant_exponent=F(1),
    )
    return TransitionHPoissonSquareOffdiagonalAudit(
        primitive_slope_pair_exponent=(
            offdiagonal.primitive_slope_pair_exponent
        ),
        inner_area_exponent=offdiagonal.inner_delta_n_area_exponent,
        expanded_square_cardinality_exponent=(
            offdiagonal.expanded_offdiagonal_cardinality_exponent
        ),
        identity_diagonal_exponent=offdiagonal.raw_identity_diagonal_exponent,
        square_function_target_exponent=(
            offdiagonal.coarse_endpoint_target_exponent
        ),
        required_offdiagonal_saving_exponent=(
            offdiagonal.required_offdiagonal_saving
        ),
        cross_determinant_max_exponent=(
            offdiagonal.cross_determinant_max_exponent
        ),
        top_cokernel_character_exponent=(
            cokernel.cokernel_character_family_exponent
        ),
        character_square_root_saving_exponent=(
            cokernel.character_square_root_saving
        ),
        remaining_mobius_entry_saving_exponent=(
            cokernel.remaining_saving_after_character_square_root
        ),
        zero_cross_determinant_is_identity_diagonal=(
            offdiagonal.zero_cross_determinant_is_identity_diagonal
        ),
        nonzero_cross_determinant_recovers_unique_slope=(
            offdiagonal.nonzero_cross_determinant_recovers_unique_slope
        ),
        cokernel_is_one_cyclic_character_family=(
            cokernel.single_finite_character_family_is_exact
        ),
        signed_four_mobius_hecke_sum_required=True,
        hybrid_mobius_hecke_estimate_proved=False,
        critical_square_function_proved=False,
    )


def transition_published_kloosterman_entry_audit(
) -> TransitionPublishedKloostermanEntryAudit:
    """Compare 2025--2026 Kloosterman bounds with the critical entry gate.

    On the top cross-determinant shell the modulus is ``c=T`` and both
    recovered shift intervals have length ``N=T^(1/2)``.  Blomer--
    Pascadi Theorem 1.1 saves ``c^(1/32)`` uniformly for arbitrary
    coefficient sequences in this square-root range.  Milicevic--Qin--
    Wu Theorem 1.1 saves ``c^(1/100)`` uniformly.  Pascadi's earlier
    non-abelian result can save ``c^(1/12)`` for favorable composite
    moduli but is not uniform near primes.

    The transition square still needs ``T^(1/2)`` after the cokernel
    character square root.  Moreover its recovered kernel and weights
    depend jointly on the four matrix entries, so they are not literally
    a fixed-modulus bilinear form with two entry-independent sequences.
    The numerical comparison is therefore optimistic and still fails.
    """
    modulus = F(1)
    interval = F(1, 2)
    required = F(1, 2)
    bp = F(1, 32)
    mqw = F(1, 100)
    pascadi = F(1, 12)
    four_bp = 4 * bp
    return TransitionPublishedKloostermanEntryAudit(
        modulus_exponent=modulus,
        delta_interval_exponent=interval,
        required_mobius_entry_saving_exponent=required,
        bp_uniform_saving_exponent=bp,
        bp_uniform_deficit=required - bp,
        mqw_uniform_saving_exponent=mqw,
        mqw_uniform_deficit=required - mqw,
        pascadi_factorable_saving_exponent=pascadi,
        pascadi_factorable_deficit=required - pascadi,
        optimistic_four_bp_applications_saving_exponent=four_bp,
        optimistic_four_bp_deficit=required - four_bp,
        bp_square_root_length_condition_holds=(2 * interval == modulus),
        bp_arbitrary_sequences_allowed=True,
        standard_kloosterman_kernel_verified=False,
        coefficients_separate_from_matrix_entries=False,
        fixed_modulus_before_entry_sum_verified=False,
        pascadi_uniform_for_all_moduli=False,
        published_coverage=False,
        bp_source=(
            "Blomer--Pascadi, arXiv:2607.24311v1, Theorem 1.1"
        ),
        mqw_source=(
            "Milicevic--Qin--Wu, arXiv:2511.07550v1, Theorem 1.1"
        ),
        pascadi_source=(
            "Pascadi, arXiv:2511.08445v1, square-root range"
        ),
    )


def transition_delta_lattice_dual_identity(
    *,
    s1: int,
    w1: int,
    s2: int,
    w2: int,
    v: int,
    j: int,
    m1: int,
    m2: int,
) -> dict[str, int | bool]:
    """Check the exact primal/dual lattices in the critical square.

    Put ``B=((w1,-s1),(w2,-s2))``.  The recovered shifts are
    ``delta=B(v,j)^t`` and the dual lattice is ``B^(-t) Z^2``.  This
    helper keeps the adjugate numerators integral and verifies
    ``<Bz,B^(-t)m>=<z,m>`` without floating-point arithmetic.
    """
    if min(s1, s2) <= 0:
        raise ValueError("transition denominators must be positive")
    if gcd(s1, abs(w1)) != 1 or gcd(s2, abs(w2)) != 1:
        raise ValueError("the two determinant rows must be primitive")
    coefficient_determinant = s1 * w2 - w1 * s2
    if coefficient_determinant == 0:
        raise ValueError("the delta-lattice Poisson step is offdiagonal")
    cross = -coefficient_determinant
    delta1 = w1 * v - s1 * j
    delta2 = w2 * v - s2 * j
    dual_numerator_1 = -s2 * m1 - w2 * m2
    dual_numerator_2 = s1 * m1 + w1 * m2
    pairing_numerator = (
        delta1 * dual_numerator_1 + delta2 * dual_numerator_2
    )
    expected_pairing = v * m1 + j * m2
    return {
        "cross_determinant": cross,
        "coefficient_determinant": coefficient_determinant,
        "delta1": delta1,
        "delta2": delta2,
        "dual_numerator_1": dual_numerator_1,
        "dual_numerator_2": dual_numerator_2,
        "scaled_dual_pairing_numerator": pairing_numerator,
        "dual_pairing_integer": pairing_numerator // coefficient_determinant,
        "poisson_covolume_exact": (
            abs(coefficient_determinant) == abs(cross)
        ),
        "dual_pairing_exact": (
            pairing_numerator
            == coefficient_determinant * expected_pairing
        ),
    }


def transition_delta_lattice_poisson_audit(
    *,
    determinant_exponent: Fraction,
    primitive_divisor_exponent: Fraction = F(0),
) -> TransitionDeltaLatticePoissonAudit:
    """Audit two-dimensional Poisson on the critical shift lattice.

    For entry rows of length ``T`` and determinant ``D=T^kappa``, the
    shift lattice has covolume ``D``.  Its ``T^(1/2)`` square has area
    ``T``, so the zero mode has density ``T/D``.  There are
    ``T^(2+kappa)`` entry pairs on the determinant shell; hence the
    absolute zero mode is always ``T^3``, independently of ``kappa``.

    Primitivity is retained by ``1_(v,j)=1=sum_{d|v,j}mu(d)``.  On a
    layer ``d=T^eta``, Poisson on ``d*B Z^2`` contributes ``d^(-2)``.
    The two singular scales of the primal matrix are ``T`` and
    ``D/T``.  After multiplying dual frequencies by the shift length
    and dividing by ``d``, their spacings are ``T^(-1/2-eta)`` and
    ``T^(3/2-kappa-eta)``.  The weighted number of longitudinal modes
    is ``T^(1/2-eta)``, so no primitive-divisor layer is worse than
    ``d=1``.  The recovered slope support makes
    ``d<=C_W*T^(1/2)``.  Thus the exact zero-mode coefficient is the
    corresponding truncated sum of ``mu(d)/d^2``; its difference from
    ``1/zeta(2)`` has exponent ``-1/2`` by the absolutely convergent
    tail.  The integral still depends jointly on the entry matrix, so
    this audit does not assert coefficient separation.
    """
    determinant = F(determinant_exponent)
    primitive_divisor = F(primitive_divisor_exponent)
    if determinant <= 0 or determinant > F(1):
        raise ValueError("determinant exponent must lie in (0,1]")
    if primitive_divisor < 0 or primitive_divisor > F(1, 2):
        raise ValueError("primitive divisor exceeds the recovered slope range")
    delta_length = F(1, 2)
    delta_area = 2 * delta_length
    zero_density = delta_area - determinant
    entry_pairs = F(2) + determinant
    zero_absolute = entry_pairs + zero_density
    target = F(2)
    divisor_weight = -2 * primitive_divisor
    longitudinal_spacing = delta_length - F(1) - primitive_divisor
    transverse_spacing = (
        delta_length + F(1) - determinant - primitive_divisor
    )
    active_longitudinal = -longitudinal_spacing
    active_transverse = _positive_part(-transverse_spacing)
    weighted_active = divisor_weight + active_longitudinal
    return TransitionDeltaLatticePoissonAudit(
        determinant_exponent=determinant,
        delta_length_exponent=delta_length,
        delta_box_area_exponent=delta_area,
        primitive_divisor_exponent=primitive_divisor,
        primitive_divisor_weight_exponent=divisor_weight,
        lattice_covolume_exponent=determinant,
        zero_mode_density_exponent=zero_density,
        entry_pair_shell_exponent=entry_pairs,
        zero_mode_absolute_exponent=zero_absolute,
        square_function_target_exponent=target,
        required_zero_mode_saving_exponent=zero_absolute - target,
        longitudinal_dual_spacing_exponent=longitudinal_spacing,
        transverse_dual_spacing_exponent=transverse_spacing,
        active_longitudinal_frequency_exponent=active_longitudinal,
        active_transverse_frequency_exponent=active_transverse,
        weighted_active_longitudinal_exponent=weighted_active,
        primitive_zero_mode_coefficient=(
            "sum_{d<=C_W*T^(1/2)} mu(d)/d^2"
        ),
        primitive_euler_factor_tail_exponent=F(-1, 2),
        primitive_mobius_inversion_exact=True,
        primitive_divisor_layers_do_not_worsen=(weighted_active <= F(1, 2)),
        zero_mode_obstruction_independent_of_determinant_shell=(
            zero_absolute == F(3)
        ),
        zero_mode_covolume_jacobian_cancels_exactly=True,
        zero_mode_is_continuous_slope_gram=True,
        full_zero_mode_gram_positive_semidefinite=True,
        offdiagonal_is_full_gram_minus_identity_diagonal=True,
        kernel_alone_annihilates_zero_mode=False,
        square_function_route_is_only_sufficient=True,
        zero_mode_weight_separates_in_the_entries=False,
        zero_mode_mobius_variance_proved=False,
        whole_delta_lattice_covered=False,
    )


def transition_denominator_gcd_line_identity(
    *,
    g: int,
    a: int,
    b: int,
    r1_base: int,
    r2_base: int,
    n: int,
) -> dict[str, int | bool]:
    """Verify the exact line parametrization after extracting ``(s1,s2)``.

    With ``s1=g*a``, ``s2=g*b`` and ``(a,b)=1``, put
    ``h=b*r1_base-a*r2_base``.  Every translate
    ``r1=r1_base+a*n``, ``r2=r2_base+b*n`` then satisfies
    ``r1*s2-r2*s1=g*h``.
    """
    if min(g, a, b) <= 0:
        raise ValueError("g and the primitive denominator pair are positive")
    if gcd(a, b) != 1:
        raise ValueError("a and b must be coprime")
    s1 = g * a
    s2 = g * b
    r1 = r1_base + a * n
    r2 = r2_base + b * n
    h = b * r1_base - a * r2_base
    cross = r1 * s2 - r2 * s1
    return {
        "s1": s1,
        "s2": s2,
        "r1": r1,
        "r2": r2,
        "h": h,
        "cross_determinant": cross,
        "denominator_gcd_exact": gcd(s1, s2) == g,
        "primitive_denominator_pair": gcd(a, b) == 1,
        "line_equation_exact": cross == g * h,
    }


def transition_denominator_gcd_line_audit(
    *,
    determinant_exponent: Fraction,
    denominator_gcd_exponent: Fraction,
) -> TransitionDenominatorGcdLineAudit:
    """Reduce a determinant shell to one two-Mobius line-family gate.

    Write ``D=T^kappa``, ``g=(s1,s2)=T^gamma`` and
    ``s1=g*a,s2=g*b``.  The dyadic denominator-pair family has exponent
    ``2-gamma`` (including the choices of ``g``), the quotient
    ``h=Delta/g`` has exponent ``kappa-gamma``, and the solution-line
    parameter has exponent ``gamma``.  The raw exponent is therefore
    ``2+kappa-gamma``.

    On the support of the four Mobius weights, ``g,a,b`` are pairwise
    coprime and squarefree where needed, so
    ``mu(g*a)mu(g*b)=mu(a)mu(b)`` exactly.  Square-root cancellation in
    the two cofactor variables, each of length ``T^(1-gamma)``, saves
    ``T^(1-gamma)`` and leaves exponent ``1+kappa``.  This has margin
    ``1-kappa`` and is critical only on the top determinant face.
    """
    determinant = F(determinant_exponent)
    common_gcd = F(denominator_gcd_exponent)
    if determinant <= 0 or determinant > F(1):
        raise ValueError("determinant exponent must lie in (0,1]")
    if common_gcd < 0 or common_gcd > determinant:
        raise ValueError("the denominator gcd must divide the determinant")
    cofactor = F(1) - common_gcd
    denominator_pairs = F(2) - common_gcd
    determinant_quotient = determinant - common_gcd
    line_parameter = common_gcd
    raw = denominator_pairs + determinant_quotient + line_parameter
    target = F(2)
    required = _positive_part(raw - target)
    two_mobius_length = 2 * cofactor
    square_root_saving = two_mobius_length / 2
    post_square_root = raw - square_root_saving
    margin = square_root_saving - required
    absolute_reaches = raw <= target
    return TransitionDenominatorGcdLineAudit(
        determinant_exponent=determinant,
        denominator_gcd_exponent=common_gcd,
        denominator_cofactor_exponent=cofactor,
        denominator_pair_exponent=denominator_pairs,
        determinant_quotient_exponent=determinant_quotient,
        line_parameter_exponent=line_parameter,
        raw_line_family_exponent=raw,
        square_function_target_exponent=target,
        required_saving_exponent=required,
        two_denominator_mobius_length_exponent=two_mobius_length,
        two_denominator_square_root_saving_exponent=square_root_saving,
        post_square_root_exponent=post_square_root,
        square_root_power_margin=margin,
        mobius_product_reduction_exact=True,
        top_determinant_is_unique_critical_face=(determinant == F(1)),
        absolute_count_reaches_target=absolute_reaches,
        two_mobius_line_square_root_proved=False,
        shell_covered=absolute_reaches,
    )


def transition_denominator_mobius_type_ii_audit(
    *,
    determinant_exponent: Fraction,
    denominator_gcd_exponent: Fraction,
    left_short_mobius_exponent: Fraction,
    left_cutoff_divisor_exponent: Fraction,
    right_short_mobius_exponent: Fraction,
    right_cutoff_divisor_exponent: Fraction,
) -> TransitionDenominatorMobiusTypeIIAudit:
    """Exact half-cutoff Type-I/II ledger for the line-family gate.

    Put ``A=T^alpha`` with ``alpha=1-gamma`` and choose
    ``U=V=A^(1/2)`` in the exact identity

    ``mu(a)=-sum_(xy=a,x>U)c_U(x)mu(y)``.

    Expanding ``c_U(x)`` as ``x=d*e`` gives one signed cutoff divisor
    ``d``, one unsigned cofactor ``e``, and the signed short factor
    ``y`` on each side.  Their exponents satisfy
    ``pi+epsilon+beta=alpha``.  The square root in the four signed
    Mobius atoms saves half their total volume.  The remaining saving
    is exactly half the two unsigned cofactor volumes minus the
    off-top margin ``1-kappa``.  No analytic estimate is asserted.
    """
    determinant = F(determinant_exponent)
    common_gcd = F(denominator_gcd_exponent)
    if determinant <= 0 or determinant > F(1):
        raise ValueError("determinant exponent must lie in (0,1]")
    if common_gcd < 0 or common_gcd > determinant:
        raise ValueError("the denominator gcd must divide the determinant")
    alpha = F(1) - common_gcd
    cutoff = alpha / 2
    left_short = F(left_short_mobius_exponent)
    left_divisor = F(left_cutoff_divisor_exponent)
    right_short = F(right_short_mobius_exponent)
    right_divisor = F(right_cutoff_divisor_exponent)
    for name, value in (
        ("left short factor", left_short),
        ("left cutoff divisor", left_divisor),
        ("right short factor", right_short),
        ("right cutoff divisor", right_divisor),
    ):
        if value < 0 or value > cutoff:
            raise ValueError(f"{name} lies outside the half-cutoff polytope")
    if left_short + left_divisor > alpha:
        raise ValueError("left signed factors exceed the cofactor length")
    if right_short + right_divisor > alpha:
        raise ValueError("right signed factors exceed the cofactor length")

    left_unsigned = alpha - left_short - left_divisor
    right_unsigned = alpha - right_short - right_divisor
    signed_volume = (
        left_short + left_divisor + right_short + right_divisor
    )
    signed_square_root = signed_volume / 2
    required = determinant - common_gcd
    unsigned_half = (left_unsigned + right_unsigned) / 2
    off_top_margin = F(1) - determinant
    signed_deficit = required - signed_square_root
    remaining_completion = _positive_part(signed_deficit)
    endpoint_power_closed = required == 0
    return TransitionDenominatorMobiusTypeIIAudit(
        determinant_exponent=determinant,
        denominator_gcd_exponent=common_gcd,
        denominator_cofactor_exponent=alpha,
        cutoff_exponent=cutoff,
        left_short_mobius_exponent=left_short,
        left_cutoff_divisor_exponent=left_divisor,
        left_unsigned_cofactor_exponent=left_unsigned,
        right_short_mobius_exponent=right_short,
        right_cutoff_divisor_exponent=right_divisor,
        right_unsigned_cofactor_exponent=right_unsigned,
        signed_mobius_atom_volume_exponent=signed_volume,
        signed_atom_square_root_saving_exponent=signed_square_root,
        required_total_saving_exponent=required,
        top_face_unsigned_half_volume_exponent=unsigned_half,
        off_top_power_margin_exponent=off_top_margin,
        remaining_completion_saving_exponent=remaining_completion,
        left_type_ii_boundary=(left_short == cutoff),
        right_type_ii_boundary=(right_short == cutoff),
        exact_c_u_factorization_used=True,
        top_face_deficit_identity_exact=(
            determinant == F(1)
            and remaining_completion == unsigned_half
        ),
        general_deficit_identity_exact=(
            signed_deficit == unsigned_half - off_top_margin
        ),
        no_unsigned_completion_needed=(remaining_completion == 0),
        signed_atom_square_root_proved=False,
        unsigned_cofactor_completion_proved=False,
        cell_closed_by_registered_bounds=endpoint_power_closed,
    )


def transition_bourgain_garaev_multilinear_audit(
) -> TransitionBourgainGaraevMultilinearAudit:
    """Test Bourgain--Garaev against the balanced all-signed cell.

    In the balanced top cell the four new Mobius atoms have length
    ``p^(1/4)`` at determinant conductor ``p=T``.  Grouping them into
    two product sequences of length ``p^(1/2)``, Theorem 9 saves
    ``p^(1/16)`` and Theorem 10 with ``k1=k2=2`` saves ``p^(1/24)``.
    Theorem 11 needs at least seven variables.  Section 10.4 proves
    Theorem 12 using ``C=9*c^(-2)`` with ``c<=1/4``, hence ``C>=144``,
    but Remark 3 states the stronger published constant ``C=4``.  At
    ``n=4`` that published threshold is the strict inequality
    ``N>p^(1/4)``, whereas this cell has equality.  Theorem 13 does meet
    its formal product-length condition, but states only an unspecified
    positive saving and therefore does not certify the required
    ``p^(-1/2)`` saving.

    These numerical comparisons are optimistic: all cited theorems use
    a fixed prime modulus and the reciprocal-product phase, neither of
    which has been derived for the varying determinant kernel.
    """
    required = F(1, 2)
    theorem9 = F(1, 16)
    theorem10 = F(1, 24)
    atom_length = F(1, 4)
    variables = 4
    section10_4_constant_lower_bound = 144
    published_constant = 4
    theorem12_threshold = F(published_constant, variables * variables)
    theorem13_product = variables * atom_length
    theorem13_threshold = F(1, 2)
    return TransitionBourgainGaraevMultilinearAudit(
        modulus_exponent=F(1),
        atom_interval_exponent=atom_length,
        actual_multilinear_variable_count=variables,
        required_saving_exponent=required,
        theorem9_grouped_interval_exponent=F(1, 2),
        theorem9_saving_exponent=theorem9,
        theorem9_deficit=required - theorem9,
        theorem10_k2_saving_exponent=theorem10,
        theorem10_k2_deficit=required - theorem10,
        theorem11_minimum_variable_count=7,
        theorem11_product_length_condition_holds=(
            variables * atom_length > F(1, 3)
        ),
        theorem11_variable_count_condition_holds=(variables >= 7),
        theorem12_section10_4_proof_constant_lower_bound=(
            section10_4_constant_lower_bound
        ),
        theorem12_published_constant=published_constant,
        theorem12_n4_threshold_exponent=theorem12_threshold,
        theorem12_length_condition_holds=(
            atom_length > theorem12_threshold
        ),
        theorem13_product_interval_exponent=theorem13_product,
        theorem13_threshold_exponent=theorem13_threshold,
        theorem13_available_epsilon_margin=(
            theorem13_product - theorem13_threshold
        ),
        theorem13_product_condition_holds=(
            theorem13_product > theorem13_threshold
        ),
        theorem13_saving_exponent_is_explicit=False,
        theorem13_required_half_power_saving_certified=False,
        theorems_require_prime_modulus=True,
        actual_determinant_moduli_all_prime=False,
        grouped_product_sets_are_intervals=False,
        actual_four_atom_weights_separate=False,
        reciprocal_product_phase_verified=False,
        published_coverage=False,
        source=(
            "Bourgain--Garaev, arXiv:1211.4184v1, "
            "Theorems 9--13, Remark 3, and Sections 10.4--10.5"
        ),
    )


def transition_bourgain_garaev_iterated_factorization_audit(
) -> TransitionBourgainGaraevIteratedFactorizationAudit:
    """Reject the formal eight-variable split of the balanced cell.

    Splitting each of the four ``p^(1/4)`` atoms into two formal
    ``p^(1/8)`` atoms would satisfy the numerical hypotheses of
    Bourgain--Garaev Theorem 11.  The approved finite Mobius identity
    does not force such a split: on a prime input its only long factor
    remains the prime itself and the other factors are units.  Moreover,
    the exact line Fourier phase is a difference of direct product
    monomials, not the reciprocal-product phase of Theorems 11--13.
    """
    original_atom = F(1, 4)
    subatom_count = 2
    subatom = original_atom / subatom_count
    original_variables = 4
    formal_variables = original_variables * subatom_count
    theorem11_minimum = 7
    return TransitionBourgainGaraevIteratedFactorizationAudit(
        original_atom_exponent=original_atom,
        desired_equal_subatom_count=subatom_count,
        desired_subatom_exponent=subatom,
        formal_total_variable_count=formal_variables,
        theorem11_minimum_variable_count=theorem11_minimum,
        formal_theorem11_count_condition_holds=(
            formal_variables >= theorem11_minimum
        ),
        formal_theorem11_product_condition_holds=(
            formal_variables * subatom > F(1, 3)
        ),
        theorem11_required_half_power_saving_certified=False,
        prime_atom_has_balanced_two_factor_decomposition=False,
        iterated_identity_forces_seven_positive_length_variables=False,
        actual_phase_is_reciprocal_product=False,
        actual_moduli_all_prime=False,
        published_coverage=False,
    )


def mobius_hecke_local_k_coefficients(
    *,
    hecke_lambda: Fraction,
    degree: int,
) -> tuple[Fraction, ...]:
    """Return the local correction in the exact Möbius--Hecke factor.

    If ``x=p^(-s)`` and ``lambda=lambda_f(p)``, define ``K_p`` by

    ``1-lambda*x = (1-lambda*x+x^2) * (1-x^2) * K_p(x)``.

    The recurrence below performs exact formal power-series division.
    """
    if degree < 0:
        raise ValueError("degree must be nonnegative")
    coefficients: list[Fraction] = []

    def previous(index: int) -> Fraction:
        return coefficients[index] if index >= 0 else F(0)

    for index in range(degree + 1):
        target = F(1) if index == 0 else (-hecke_lambda if index == 1 else F(0))
        coefficient = (
            target
            + hecke_lambda * previous(index - 1)
            - hecke_lambda * previous(index - 3)
            + previous(index - 4)
        )
        coefficients.append(coefficient)
    return tuple(coefficients)


def balanced_mobius_hecke_local_k_coefficients(
    *,
    hecke_lambda: Fraction,
    left_twist: Fraction,
    right_twist: Fraction,
    degree: int,
) -> tuple[Fraction, ...]:
    """Return the exact local correction for the balanced convolution.

    The numerator is

    ``1-lambda*(u+v)*x+(lambda^2-1)*u*v*x^2``.

    The denominator before the correction is the product of the two
    inverse Hecke factors and the three inverse zeta factors with
    twists ``u^2``, ``v^2``, and ``u*v``.
    """
    if degree < 0:
        raise ValueError("degree must be nonnegative")

    def multiply(
        left: list[Fraction],
        right: list[Fraction],
    ) -> list[Fraction]:
        product = [F(0) for _ in range(degree + 1)]
        for left_index, left_value in enumerate(left):
            for right_index, right_value in enumerate(right):
                index = left_index + right_index
                if index <= degree:
                    product[index] += left_value * right_value
        return product

    u = left_twist
    v = right_twist
    lam = hecke_lambda
    denominator = [F(1)] + [F(0) for _ in range(degree)]
    for factor in (
        [F(1), -lam * u, u * u],
        [F(1), -lam * v, v * v],
        [F(1), F(0), -(u * u)],
        [F(1), F(0), -(v * v)],
        [F(1), F(0), -(u * v)],
    ):
        denominator = multiply(denominator, factor)

    numerator = [
        F(1),
        -lam * (u + v),
        (lam * lam - 1) * u * v,
    ]
    numerator.extend(F(0) for _ in range(max(0, degree + 1 - len(numerator))))
    numerator = numerator[: degree + 1]

    correction: list[Fraction] = []
    for index in range(degree + 1):
        coefficient = numerator[index]
        for denominator_index in range(1, index + 1):
            coefficient -= (
                denominator[denominator_index]
                * correction[index - denominator_index]
            )
        correction.append(coefficient)
    return tuple(correction)


def transition_mobius_hecke_reciprocal_l_audit(
) -> TransitionMobiusHeckeReciprocalLAudit:
    """Record the exact Euler product and the remaining spectral gate.

    The local identity implies

    ``sum mu(n)lambda_f(n)n^-s = K_f(s)/(zeta(2s)L(s,f))``.

    Since ``K_p=1-lambda_f(p)p^(-3s)+O(p^(-4s+2theta))``, the
    Kim--Sarnak exponent ``theta=7/64`` gives absolute convergence of
    ``K_f`` on ``Re(s)=1/2``.  No current adapter derives the actual
    Kuznetsov transform or supplies the required negative moment of
    ``L(s,f)`` with a half-power saving.
    """
    coefficients = mobius_hecke_local_k_coefficients(
        hecke_lambda=F(3),
        degree=4,
    )
    balanced_coefficients = balanced_mobius_hecke_local_k_coefficients(
        hecke_lambda=F(3),
        left_twist=F(2),
        right_twist=F(5),
        degree=4,
    )
    return TransitionMobiusHeckeReciprocalLAudit(
        physical_spectral_line=F(1, 2),
        required_mobius_saving_exponent=F(1, 2),
        k_local_first_nontrivial_degree=next(
            index
            for index, coefficient in enumerate(coefficients[1:], start=1)
            if coefficient != 0
        ),
        local_factorization_exact=True,
        k_euler_product_absolutely_convergent_at_half=True,
        balanced_two_factor_local_factorization_exact=True,
        balanced_reciprocal_l_factor_count=2,
        balanced_zeta_factor_count=3,
        balanced_k_local_first_nontrivial_degree=next(
            index
            for index, coefficient in enumerate(
                balanced_coefficients[1:],
                start=1,
            )
            if coefficient != 0
        ),
        classical_kuznetsov_hecke_index_is_shift=True,
        mobius_entries_are_not_classical_hecke_indices=True,
        balanced_factor_is_conditional_spectral_diagnostic=True,
        actual_kuznetsov_reduction_derived=False,
        reciprocal_l_negative_moment_proved=False,
        required_half_power_saving_certified=False,
        whole_line_family_covered=False,
    )


def transition_entry_weighted_relative_trace_audit(
    *,
    prime_bound: int,
) -> TransitionEntryWeightedRelativeTraceAudit:
    """Record the conductor cost of exact Möbius matrix-entry weights.

    A spherical local test is constant on primitive columns.  The local
    factor of ``mu(r)mu(s)`` is not: it is ``+1`` when both entries are
    units and ``-1`` when exactly one is divisible by ``p``.  Therefore
    every prime which can divide an entry requires a nonspherical local
    type of level at least ``p``.  Their global level is bounded below
    by the corresponding primorial.  Distinguishing valuation one from
    valuation at least two requires depth two at the smaller primes and
    can only increase this lower bound.
    """
    if prime_bound < 2:
        raise ValueError("prime_bound must be at least 2")
    sieve = [True] * (prime_bound + 1)
    sieve[0] = sieve[1] = False
    for prime in range(2, isqrt(prime_bound) + 1):
        if sieve[prime]:
            for multiple in range(prime * prime, prime_bound + 1, prime):
                sieve[multiple] = False
    primes = tuple(index for index, is_prime in enumerate(sieve) if is_prime)
    primorial = 1
    for prime in primes:
        primorial *= prime
    return TransitionEntryWeightedRelativeTraceAudit(
        required_nonspherical_primes=primes,
        minimum_global_level=primorial,
        asymptotic_log_level_scale=F(1),
        minimum_global_level_is_primorial=True,
        local_spherical_vector_is_constant_on_primitive_columns=True,
        primitive_entry_weight_is_not_k_invariant=True,
        exact_squarefree_weight_needs_depth_two_for_small_primes=True,
        hecke_index_is_shift_not_entry=True,
        polynomial_conductor_preserved=False,
        published_entry_weighted_adapter=False,
        whole_line_family_covered=False,
    )


def transition_small_prime_spectral_hybrid_audit(
    *,
    fixed_rough_factor_cap: int,
    polynomial_level_exponent: Fraction,
) -> TransitionSmallPrimeSpectralHybridAudit:
    """Compare polynomial local level with a fixed rough factor count.

    A cutoff ``z=C log T`` has primorial ``exp(theta(z))=T^(C+o(1))``
    but permits ``log T/log z`` rough prime factors.  To force at most
    ``K`` prime factors in an integer up to ``T`` one needs the boundary
    ``z=T^(1/(K+1))``; its primorial is
    ``exp(T^(1/(K+1)+o(1)))`` and is superpolynomial.  Sieve density at
    the logarithmic cutoff gives no positive power of ``T``.
    """
    if fixed_rough_factor_cap < 1:
        raise ValueError("fixed_rough_factor_cap must be positive")
    if polynomial_level_exponent <= 0:
        raise ValueError("polynomial_level_exponent must be positive")
    required = F(1, 2)
    rough_power = F(0)
    return TransitionSmallPrimeSpectralHybridAudit(
        fixed_rough_factor_cap=fixed_rough_factor_cap,
        fixed_cap_cutoff_exponent=F(1, fixed_rough_factor_cap + 1),
        polynomial_level_exponent=polynomial_level_exponent,
        required_saving_exponent=required,
        rough_density_power_saving_exponent=rough_power,
        residual_power_deficit=required - rough_power,
        logarithmic_cutoff_keeps_polynomial_level=True,
        logarithmic_cutoff_forces_fixed_factor_count=False,
        fixed_factor_cutoff_has_superpolynomial_level=True,
        published_rough_cofactor_half_power_bound=False,
        whole_line_family_covered=False,
    )


def transition_general_cutoff_line_gate_audit(
    *,
    determinant_exponent: Fraction,
    denominator_gcd_exponent: Fraction,
    cutoff_ratio: Fraction,
    type_split_ratio: Fraction,
    left_cutoff_divisor_exponent: Fraction,
    left_short_mobius_exponent: Fraction,
    right_cutoff_divisor_exponent: Fraction,
    right_short_mobius_exponent: Fraction,
) -> TransitionGeneralCutoffLineGateAudit:
    """Audit an arbitrary ``U=A^u, V=A^v`` line-gate cell.

    Each factorization ``a=d*e*y`` has exponent identity
    ``pi+epsilon+beta=alpha``.  Consequently square roots in all signed
    and unsigned factor volumes save exactly ``alpha=1-gamma``.  On the
    top determinant face this equals, but never exceeds, the required
    saving.  The cutoff only redistributes the same critical volume.
    """
    kappa = F(determinant_exponent)
    gamma = F(denominator_gcd_exponent)
    u = F(cutoff_ratio)
    v = F(type_split_ratio)
    if not (F(0) <= gamma <= kappa <= F(1)):
        raise ValueError("require 0 <= gamma <= kappa <= 1")
    if not (F(0) < u < F(1)):
        raise ValueError("cutoff_ratio must lie in (0,1)")
    if not (F(0) <= v <= F(1) - u):
        raise ValueError("type_split_ratio must lie in [0,1-u]")
    alpha = F(1) - gamma
    cutoff = u * alpha
    split = v * alpha
    left_divisor = F(left_cutoff_divisor_exponent)
    left_short = F(left_short_mobius_exponent)
    right_divisor = F(right_cutoff_divisor_exponent)
    right_short = F(right_short_mobius_exponent)
    for name, divisor, short in (
        ("left", left_divisor, left_short),
        ("right", right_divisor, right_short),
    ):
        if not (F(0) <= divisor <= cutoff):
            raise ValueError(f"{name} divisor lies outside cutoff")
        if not (F(0) <= short < alpha - cutoff):
            raise ValueError(f"{name} short factor violates de>U")
    left_unsigned = alpha - left_divisor - left_short
    right_unsigned = alpha - right_divisor - right_short
    signed_saving = (
        left_divisor + left_short + right_divisor + right_short
    ) / 2
    unsigned_saving = (left_unsigned + right_unsigned) / 2
    required = kappa - gamma
    total = signed_saving + unsigned_saving
    margin = total - required
    return TransitionGeneralCutoffLineGateAudit(
        determinant_exponent=kappa,
        denominator_gcd_exponent=gamma,
        cofactor_exponent=alpha,
        cutoff_ratio=u,
        type_split_ratio=v,
        cutoff_exponent=cutoff,
        type_split_exponent=split,
        left_unsigned_exponent=left_unsigned,
        right_unsigned_exponent=right_unsigned,
        signed_square_root_saving=signed_saving,
        unsigned_completion_saving=unsigned_saving,
        required_saving=required,
        total_hypothetical_saving=total,
        top_face_power_margin=margin,
        cutoff_independent_deficit_identity=(
            required - signed_saving
            == unsigned_saving - (F(1) - kappa)
        ),
        cutoff_choice_creates_positive_power_slack=(margin > F(1) - kappa),
        cell_closed_by_registered_bounds=False,
    )


def transition_bblr_quadratic_divisor_audit(
    *,
    denominator_gcd_exponent: Fraction,
    left_signed_outer_exponent: Fraction,
    right_signed_outer_exponent: Fraction,
) -> TransitionBBLRQuadraticDivisorAudit:
    """Map the joint line gate to BBLR's quadratic-divisor theorem.

    Factor both Möbius-bearing variables on each side.  Their signed
    atoms must all be convolved into BBLR's one arbitrary outer
    coefficient; the two unsigned cofactors occupy m1,m2.  If a side
    has product exponent P=2-gamma, signed exponent s_i, and unsigned
    exponent P-s_i, then BBLR's parameters are

    A=T^s1, B=T^s2, X=T^(P-(s1+s2)/2), H=T^(1-gamma), Z=T.

    The sharp Proposition 3.1 error is available only when
    s1+s2 >= 2*(1-gamma).  Otherwise the unconditional error (12) must
    be used.  The theorem also produces four main terms; no cell is
    covered until their exact recombination under the Möbius identity
    has been controlled.
    """
    gamma = F(denominator_gcd_exponent)
    if gamma < F(0) or gamma > F(1):
        raise ValueError("denominator gcd exponent must lie in [0,1]")
    alpha = F(1) - gamma
    product = F(1) + alpha
    left_signed = F(left_signed_outer_exponent)
    right_signed = F(right_signed_outer_exponent)
    if not (F(0) <= left_signed <= product):
        raise ValueError("left signed outer exponent lies outside its side")
    if not (F(0) <= right_signed <= product):
        raise ValueError("right signed outer exponent lies outside its side")

    signed_sum = left_signed + right_signed
    signed_max = max(left_signed, right_signed)
    unsigned_parameter = product - signed_sum / 2
    sharp_applicable = signed_sum >= 2 * alpha

    # BBLR Proposition 3.1's sharp error after exact substitution.
    sharp_ab = F(1, 2) + alpha + signed_sum
    sharp_watt = F(3, 4) + F(3, 2) * alpha + signed_max / 2
    sharp_error = max(sharp_ab, sharp_watt)

    # BBLR Proposition 3.1, equation (12), valid without that condition.
    general_first = (
        F(3, 4)
        + F(7, 4) * alpha
        + signed_sum / 4
        + F(5, 4) * signed_max
    )
    general_h_squared = 2 * alpha
    general_error = max(general_first, general_h_squared)

    best_error = (
        min(sharp_error, general_error)
        if sharp_applicable
        else general_error
    )
    target = product
    return TransitionBBLRQuadraticDivisorAudit(
        denominator_gcd_exponent=gamma,
        cofactor_exponent=alpha,
        side_product_exponent=product,
        left_signed_outer_exponent=left_signed,
        right_signed_outer_exponent=right_signed,
        total_signed_outer_exponent=signed_sum,
        maximum_signed_outer_exponent=signed_max,
        unsigned_pair_parameter_exponent=unsigned_parameter,
        shift_exponent=alpha,
        frequency_parameter_exponent=F(1),
        sharp_error_formula_applicable=sharp_applicable,
        sharp_error_ab_exponent=sharp_ab,
        sharp_error_watt_exponent=sharp_watt,
        sharp_error_exponent=sharp_error,
        general_error_first_exponent=general_first,
        general_error_h_squared_exponent=general_h_squared,
        general_error_exponent=general_error,
        target_exponent=target,
        best_error_exponent=best_error,
        best_error_power_margin=target - best_error,
        hard_face_global_best_power_margin=F(-1, 2),
        outer_slots_absorb_all_signed_atoms=True,
        remaining_slots_are_two_unsigned_factors_per_side=True,
        arbitrary_coefficients_allowed_only_in_outer_slots=True,
        independent_internal_smooth_weights_supported=True,
        side_product_balance_verified=True,
        outer_coefficient_divisor_bound_verified=True,
        proposition_3_1_hypotheses_verified=True,
        four_main_terms_cancelled_after_mobius_recombination=False,
        published_theorem_closes_cell=False,
        source=(
            "Bettin--Bui--Li--Radziwill, arXiv:1609.02539v1, "
            "Proposition 3.1 and equation (12)"
        ),
    )


def transition_bblr_hard_unsigned_cell_audit(
    *,
    poisson_gcd_exponent: Fraction,
) -> TransitionBBLRHardUnsignedCellAudit:
    """Retain BBLR Lemma 3.1's scale dependence in the worst hard cell.

    The all-unsigned term in four exact Möbius decompositions has
    ``A=B=1``, ``M1=M2=N1=N2=T`` and ``H=T``.  In equation (15), on
    ``d=T^eta``, the bound for ``Z_d`` has exponent
    ``5/2-(7/2)eta``.  Its x-interval and the number of d in the dyadic
    layer each have exponent ``eta``.  The layer is therefore
    ``5/2-(3/2)eta`` and the d=1 layer reproduces Proposition 3.1's
    ``T^(5/2)`` error exactly.
    """
    eta = F(poisson_gcd_exponent)
    if eta < F(0) or eta > F(1):
        raise ValueError("Poisson gcd exponent must lie in [0,1]")
    z_exponent = F(5, 2) - F(7, 2) * eta
    x_exponent = eta
    d_count_exponent = eta
    layer_exponent = z_exponent + x_exponent + d_count_exponent
    global_error = F(5, 2)
    target = F(2)
    return TransitionBBLRHardUnsignedCellAudit(
        poisson_gcd_exponent=eta,
        outer_a_exponent=F(0),
        outer_b_exponent=F(0),
        m1_exponent=F(1),
        m2_exponent=F(1),
        n1_exponent=F(1),
        n2_exponent=F(1),
        shift_exponent=F(1),
        lemma_3_1_z_exponent=z_exponent,
        x_interval_exponent=x_exponent,
        poisson_gcd_count_exponent=d_count_exponent,
        dyadic_layer_exponent=layer_exponent,
        initial_h_squared_error_exponent=F(2),
        global_error_exponent=global_error,
        target_exponent=target,
        power_margin=target - global_error,
        one_mobius_pure_unsigned_coefficient=-1,
        four_mobius_pure_unsigned_coefficient=1,
        cellwise_mobius_cancellation_available=False,
        cross_outer_scale_recombination_required=True,
        uncompressed_lemma_improves_proposition_bound=False,
        source=(
            "Bettin--Bui--Li--Radziwill, arXiv:1609.02539v1, "
            "Proposition 3.1 equations (14)--(16)"
        ),
    )


def transition_banks_shparlinski_pre_cauchy_audit(
) -> TransitionBanksShparlinskiPreCauchyAudit:
    """Test the multiple-Mobius additive bound on the hard slope box.

    Before Cauchy, the hard transition equation is

        r v - (k v + j) s = delta,

    with ``r,s`` of exponent one and ``v,j,delta`` of exponent one
    half.  Banks--Shparlinski's Theorem 2.1 is ternary additive and
    puts a Mobius factor on all three summation variables.  Thus the
    two bilinear slope variables must first be fixed, while the
    original shift ``delta`` has no Mobius factor.  Divisor convolution
    can insert that missing factor algebraically, but cannot improve
    the length estimate.

    With lengths ``T,T,T^(1/2)``, the best assignment to the theorem's
    roles gives exponent ``3/2`` for a fixed slope.  Direct geometric
    counting is already exponent one, so the theorem is discarded.
    Restoring the ``(v,j)`` family and the h-Poisson factor gives
    ``1+1+1/2=5/2`` against target exponent two.  The short-interval
    theorem has threshold ``5/8``, whereas the actual short variable
    has exponent ``1/2``.
    """
    entry = F(1)
    dual_v = F(1, 2)
    dual_j = F(1, 2)
    slope_family = dual_v + dual_j
    shift = F(1, 2)
    geometric = F(1)
    theorem = F(3, 2)
    best_fixed = min(geometric, theorem)
    h_poisson = F(1, 2)
    aggregate = best_fixed + slope_family + h_poisson
    target = F(2)
    short_threshold = F(5, 8)
    short_actual = shift
    return TransitionBanksShparlinskiPreCauchyAudit(
        entry_scale_exponent=entry,
        dual_v_exponent=dual_v,
        dual_j_exponent=dual_j,
        fixed_slope_family_exponent=slope_family,
        shift_variable_exponent=shift,
        fixed_slope_geometric_count_exponent=geometric,
        best_theorem_role_bound_exponent=theorem,
        best_fixed_slope_bound_exponent=best_fixed,
        h_poisson_factor_exponent=h_poisson,
        aggregated_exponent=aggregate,
        target_exponent=target,
        power_margin=target - aggregate,
        short_interval_threshold_exponent=short_threshold,
        actual_short_interval_exponent=short_actual,
        short_interval_threshold_margin=short_actual - short_threshold,
        additive_theorem_requires_fixing_both_bilinear_slopes=True,
        original_shift_has_no_mobius_weight=True,
        divisor_convolution_can_insert_the_missing_mobius_weight=True,
        divisor_convolution_creates_power_saving=False,
        all_actual_kernel_hypotheses_verified=False,
        published_theorem_closes_pre_cauchy_sum=False,
        source=(
            "Banks--Shparlinski, arXiv:2506.08787v1, "
            "Theorems 2.1 and 2.4"
        ),
    )


def _is_prime_integer(n: int) -> bool:
    if n < 2:
        return False
    return all(n % divisor for divisor in range(2, isqrt(n) + 1))


def transition_ramare_squarefree_identity(
    *,
    n: int,
    prime_lower: int,
    prime_upper: int,
) -> dict[str, object]:
    """Evaluate Ramaré's exact prime extraction on squarefree support.

    If ``omega_P(n)`` counts prime divisors of ``n`` in the selected
    band and is nonzero, squarefreeness gives

        mu(n) = -omega_P(n)^(-1) sum_(p|n, p in P) mu(n/p).

    The identity is deliberately undefined when the band contains no
    prime divisor.  That exceptional sector has to be estimated rather
    than silently discarded.
    """
    if n < 1:
        raise ValueError("n must be positive")
    if prime_lower < 2 or prime_upper < prime_lower:
        raise ValueError("invalid prime band")
    mobius_value = _finite_mobius(n)
    if mobius_value == 0:
        raise ValueError("Ramaré extraction is restricted to squarefree n")
    band_primes = tuple(
        prime
        for prime in range(prime_lower, prime_upper + 1)
        if n % prime == 0 and _is_prime_integer(prime)
    )
    omega = len(band_primes)
    cofactor_sum = sum(_finite_mobius(n // prime) for prime in band_primes)
    ramare_value = F(-cofactor_sum, omega) if omega else None
    positive_factor_count = (
        min(1 + int(n // prime > 1) for prime in band_primes)
        if band_primes
        else 0
    )
    return {
        "mobius_value": mobius_value,
        "band_prime_divisors": band_primes,
        "band_prime_divisor_count": omega,
        "cofactor_mobius_sum": cofactor_sum,
        "ramare_value": ramare_value,
        "identity_applies": bool(omega),
        "identity_exact": bool(omega) and ramare_value == mobius_value,
        "minimum_positive_length_factor_count": positive_factor_count,
    }


def transition_ramare_medium_prime_audit(
    *,
    entry_exponent: Fraction,
    band_lower_exponent: Fraction,
    band_upper_exponent: Fraction,
) -> TransitionRamareMediumPrimeAudit:
    """Test whether a Ramaré prime band forces useful multilinearity.

    For entries of length ``A=T^alpha``, a proper band ending at
    ``T^nu`` with ``nu<alpha`` misses every prime entry ``p~A``.  The
    prime number theorem gives ``A/log A`` such entries, so this sector
    has exponent ``alpha`` and only one logarithm of density saving.

    Extending the band to ``nu=alpha`` includes those primes, but their
    exact Ramaré term is ``p=p*1``.  It has only one positive-length
    factor and therefore does not force a multilinear Kloosterman box.
    """
    alpha = F(entry_exponent)
    lower = F(band_lower_exponent)
    upper = F(band_upper_exponent)
    if alpha <= 0:
        raise ValueError("entry exponent must be positive")
    if lower <= 0 or lower > upper or upper > alpha:
        raise ValueError("prime-band exponents must satisfy 0<lower<=upper<=entry")
    reaches = upper == alpha
    power_saving = F(0)
    return TransitionRamareMediumPrimeAudit(
        entry_exponent=alpha,
        band_lower_exponent=lower,
        band_upper_exponent=upper,
        required_line_saving_exponent=alpha,
        prime_exceptional_set_exponent=F(0) if reaches else alpha,
        prime_exceptional_log_density_saving=F(0) if reaches else F(1),
        prime_exceptional_power_density_saving=power_saving,
        uncovered_power_deficit=alpha - power_saving,
        band_reaches_entry_scale=reaches,
        proper_band_leaves_prime_sector_exceptional=not reaches,
        prime_sector_is_in_ramare_sum=reaches,
        prime_sector_extracted_factor_exponent=alpha if reaches else F(0),
        prime_sector_cofactor_exponent=F(0),
        prime_sector_positive_length_factor_count=1 if reaches else 0,
        forces_two_positive_length_factors=False,
        ramare_decomposition_closes_line_gate=False,
        source="exact Ramaré identity and the prime number theorem",
    )


def transition_prime_kloosterman_audit(
) -> TransitionPrimeKloostermanAudit:
    """Compare prime-specific Kloosterman bounds at their best scale.

    Dunn--Zaharescu Theorem 1.1 gives ``q^(1/6) X^(7/9)``
    for all primes, while Theorem 1.2 gives
    ``q^(11/192) X^(15/16)`` for primes in a progression whose
    modulus is at most ``q^(1/100)``.  At the most favorable endpoint
    ``X=q=T`` these save ``T^(1/18)`` and ``T^(1/192)``.

    Even granting four independent applications, which the actual
    coupled determinant kernel does not permit, the savings remain
    below the required half power.  The actual determinant modulus is
    also moving and can be composite.
    """
    modulus = F(1)
    prime_interval = F(1)
    required = F(1, 2)
    unrestricted_bound = F(1, 6) + F(7, 9)
    progression_bound = F(11, 192) + F(15, 16)
    unrestricted_saving = F(1) - unrestricted_bound
    progression_saving = F(1) - progression_bound
    four_unrestricted = 4 * unrestricted_saving
    four_progression = 4 * progression_saving
    return TransitionPrimeKloostermanAudit(
        modulus_exponent=modulus,
        prime_interval_exponent=prime_interval,
        required_saving_exponent=required,
        unrestricted_prime_bound_exponent=unrestricted_bound,
        unrestricted_prime_saving_exponent=unrestricted_saving,
        progression_prime_bound_exponent=progression_bound,
        progression_prime_saving_exponent=progression_saving,
        progression_modulus_cap_exponent=F(1, 100),
        optimistic_four_unrestricted_saving_exponent=four_unrestricted,
        optimistic_four_unrestricted_deficit=required - four_unrestricted,
        optimistic_four_progression_saving_exponent=four_progression,
        optimistic_four_progression_deficit=required - four_progression,
        published_theorem_has_fixed_prime_modulus=True,
        actual_determinant_moduli_all_prime=False,
        standard_single_kloosterman_argument_verified=False,
        other_entry_weights_separate=False,
        published_theorem_closes_prime_sector=False,
        source=(
            "Dunn--Zaharescu, arXiv:1801.05880, "
            "Theorems 1.1 and 1.2"
        ),
    )


def poisson_exchange_reciprocity_identity(
    *,
    r: int,
    s: int,
    h: int,
    delta: int,
) -> dict[str, object]:
    """Check the exact phase correction in the swapped Poisson box.

    The original orientation Poisson-sums the variable ``x=m_2`` modulo
    ``s``.  Swapping ``(d,e,m_1,m_2)`` changes the modulus to ``r`` and,
    after ``y=(xr+delta)/s``, sends ``(delta,h)`` to
    ``(-delta,-h)``.  The transformed Fourier kernel contributes

        (r/s) e(h*delta/(r*s)) conjugate(K_{r,s}(delta,h)).

    Additive reciprocity then turns the swapped arithmetic phase into the
    conjugate of the original one.  This is a statement about the *full*
    Poisson term; the kernel by itself is not invariant.
    """
    if r <= 0 or s <= 0:
        raise ValueError("Poisson moduli must be positive")
    primitive = gcd(r, s) == 1
    if not primitive:
        raise ValueError("exchange reciprocity requires gcd(r,s)=1")
    r_inverse_mod_s = pow(r, -1, s)
    s_inverse_mod_r = pow(s, -1, r)
    swapped_with_kernel_correction = (
        -F(h * delta * s_inverse_mod_r, r)
        + F(h * delta, r * s)
    )
    conjugate_original = F(h * delta * r_inverse_mod_s, s)
    exact = (
        swapped_with_kernel_correction - conjugate_original
    ).denominator == 1
    return {
        "primitive_pair": primitive,
        "swapped_arithmetic_phase": -F(h * delta * s_inverse_mod_r, r),
        "kernel_reciprocity_correction": F(h * delta, r * s),
        "conjugate_original_phase": conjugate_original,
        "reciprocity_phase_exact": exact,
        "swapped_full_poisson_term_is_conjugate": exact,
    }


def centered_conjugate_pair_taylor_coefficients(
    *,
    real_part: Fraction,
    imaginary_part: Fraction,
) -> dict[str, Fraction | bool]:
    """Taylor ledger for a centered phase paired only by conjugation.

    With ``A=a+i*b`` and ``u=2*pi*x``, the exact paired expression is

        A (exp(iu)-1) + conjugate(A) (exp(-iu)-1)
        = 2*a*(cos(u)-1) - 2*b*sin(u).

    Its linear coefficient is therefore ``-2*b``.  Exchange symmetry
    supplies conjugation but does not force ``b=0``.
    """
    a = F(real_part)
    b = F(imaginary_part)
    return {
        "constant_coefficient": F(0),
        "linear_coefficient_in_2pi_x": -2 * b,
        "quadratic_coefficient_in_2pi_x": -a,
        "second_order_zero": b == 0,
    }


def poisson_exchange_second_order_audit() -> PoissonExchangeSecondOrderAudit:
    """Record why exact exchange symmetry does not square the collar gain."""
    return PoissonExchangeSecondOrderAudit(
        physical_shifted_sum_swap_is_conjugate=True,
        poisson_modulus_changes_under_swap=True,
        reciprocity_correction_retained=True,
        full_poisson_term_swap_is_conjugate=True,
        completed_coefficient_forced_real=False,
        imaginary_coefficient_has_linear_centered_term=True,
        second_order_bound_requires_real_coefficient=True,
        second_order_collar_unconditional=False,
    )


def common_modulus_degenerate_gauss_identity(
    *,
    r: int,
    s: int,
    c: int,
    v: int,
) -> dict[str, object]:
    """Evaluate the degenerate bilinear Gauss kernel modulo ``r*s``.

    Put ``Q=r*s``, ``u=inverse(r mod s)``, and ``A=r*u``.  Summing
    ``e((c*x+v*y-A*x*y)/Q)`` first over ``x`` forces
    ``c=A*y (mod Q)``.  This has solutions exactly when ``r|c``.  The
    resulting ``r`` values of ``y`` form one class modulo ``s``; their
    geometric character sum vanishes unless ``r|v``.  If
    ``c=r*c0`` and ``v=r*v0``, the exact value is

        Q*r*e(r*c0*v0/s).

    The helper verifies the congruence-orbit part with finite integers and
    records the character-orthogonality conclusion without floating point.
    """
    if r <= 0 or s <= 0:
        raise ValueError("common-modulus factors must be positive")
    if gcd(r, s) != 1:
        raise ValueError("common-modulus Gauss identity requires gcd(r,s)=1")
    modulus = r * s
    c_mod = c % modulus
    v_mod = v % modulus
    inverse_r_mod_s = pow(r, -1, s)
    bilinear_coefficient = r * inverse_r_mod_s
    qualifying_y = tuple(
        y
        for y in range(modulus)
        if (c_mod - bilinear_coefficient * y) % modulus == 0
    )
    r_divides_c = c_mod % r == 0
    r_divides_v = v_mod % r == 0
    if r_divides_c:
        c0 = c_mod // r
        y0 = (r * c0) % s
        expected_y = tuple(sorted((y0 + s * t) % modulus for t in range(r)))
    else:
        c0 = 0
        expected_y = ()
    orbit_exact = tuple(sorted(qualifying_y)) == expected_y

    if r_divides_c and r_divides_v:
        v0 = v_mod // r
        phase = F((r * c0 * v0) % s, s)
        amplitude = modulus * r
        character_exact = len({(v_mod * y) % modulus for y in qualifying_y}) == 1
    else:
        phase = None
        amplitude = 0
        # Once the exact y-orbit is known, finite character orthogonality
        # gives sum_(t mod r) e(v*t/r)=0 precisely when r does not divide v.
        character_exact = (not r_divides_c) or (not r_divides_v)
    return {
        "common_modulus": modulus,
        "bilinear_coefficient": bilinear_coefficient,
        "qualifying_y": qualifying_y,
        "r_divides_c": r_divides_c,
        "r_divides_v": r_divides_v,
        "r_divides_c_and_v": r_divides_c and r_divides_v,
        "gauss_support_requires_r_divides_c_and_v": True,
        "gauss_amplitude": amplitude,
        "gauss_phase": phase,
        "orthogonality_derivation_exact": orbit_exact and character_exact,
    }


def common_modulus_exchange_audit() -> CommonModulusExchangeAudit:
    """Audit lifting both Poisson orientations to the modulus ``r*s``.

    At the balanced hard box, ``r,s=T^3`` and ``H=L=T^(5/2)``.
    Raw common-modulus dual variables therefore have exponent ``7/2``.
    The degenerate Gauss identity forces both to be multiples of ``r``
    in the original orientation and of ``s`` after exchange, reducing
    each back to exponent ``1/2``.  Since ``gcd(r,s)=1``, the two
    sublattices meet modulo ``r*s`` only at zero, where the centered phase
    is zero.  No nonzero coefficient is paired with its conjugate.
    """
    common_modulus = F(6)
    raw_dual = common_modulus - F(5, 2)
    support_divisor = F(3)
    reduced_dual = raw_dual - support_divisor
    return CommonModulusExchangeAudit(
        common_modulus_exponent=common_modulus,
        raw_dual_c_exponent=raw_dual,
        raw_dual_v_exponent=raw_dual,
        original_gauss_support_divisor_exponent=support_divisor,
        swapped_gauss_support_divisor_exponent=support_divisor,
        reduced_dual_c_exponent=reduced_dual,
        reduced_dual_v_exponent=reduced_dual,
        original_frequency_sublattice_is_r_times_square=True,
        swapped_frequency_sublattice_is_s_times_square=True,
        nonzero_sublattice_intersection_empty_mod_rs=True,
        centered_zero_frequency_annihilated=True,
        common_modulus_forces_real_completed_coefficient=False,
        common_modulus_reduces_conductor=False,
        second_order_collar_unconditional=False,
    )


def midpoint_common_modulus_involution_identity(
    *,
    r: int,
    s: int,
    c: int,
    v: int,
) -> dict[str, object]:
    """Evaluate the midpoint-gauged Gauss kernel modulo ``2*r*s``.

    Put ``Q=2*r*s`` and ``A=2*r*inverse(r mod s)-1``.  Then ``A`` is a
    unit modulo ``Q``, ``A^2=1 (mod Q)``, and exchanging ``r,s`` replaces
    ``A`` by ``-A``.  Hence

        sum_(x,y mod Q) e((c*x+v*y-A*x*y)/Q) = Q e(A*c*v/Q),

    and the exchanged kernel has the conjugate phase at the same pair
    ``(c,v)``.  All claims returned here are checked by integer arithmetic.
    """
    if r <= 1 or s <= 1:
        raise ValueError("midpoint factors must exceed one")
    if gcd(r, s) != 1:
        raise ValueError("midpoint identity requires gcd(r,s)=1")
    modulus = 2 * r * s
    inverse_r_mod_s = pow(r, -1, s)
    inverse_s_mod_r = pow(s, -1, r)
    coefficient = (2 * r * inverse_r_mod_s - 1) % modulus
    swapped_coefficient = (2 * s * inverse_s_mod_r - 1) % modulus
    c_mod = c % modulus
    v_mod = v % modulus
    qualifying_y = tuple(
        y for y in range(modulus) if (c_mod - coefficient * y) % modulus == 0
    )
    expected_y = (coefficient * c_mod) % modulus
    phase_numerator = (coefficient * c_mod * v_mod) % modulus
    swapped_phase_numerator = (
        swapped_coefficient * c_mod * v_mod
    ) % modulus
    return {
        "common_modulus": modulus,
        "bilinear_coefficient": coefficient,
        "swapped_bilinear_coefficient": swapped_coefficient,
        "coefficient_is_unit": gcd(coefficient, modulus) == 1,
        "coefficient_is_involution": coefficient * coefficient % modulus == 1,
        "swap_negates_coefficient": (
            coefficient + swapped_coefficient
        ) % modulus == 0,
        "qualifying_y": qualifying_y,
        "unique_qualifying_y_is_Ac": qualifying_y == (expected_y,),
        "gauss_amplitude": modulus,
        "gauss_phase": F(phase_numerator, modulus),
        "swapped_gauss_phase": F(swapped_phase_numerator, modulus),
        "swap_phase_is_conjugate": (
            phase_numerator + swapped_phase_numerator
        ) % modulus == 0,
    }


def midpoint_hermitian_completion_audit() -> MidpointHermitianCompletionAudit:
    """Record the exact balanced-box ledger for midpoint completion.

    The common modulus ``2*r*s`` still has exponent six.  With
    ``H=L=T^(5/2)``, both raw dual windows have exponent ``7/2``.  The
    completed ambient cardinality is therefore ``T^13``.  The completion
    prefactor ``H*L/Q`` is ``T^-1``, so the local ``T^6 log^-B`` target
    becomes a ``T^7 log^-B`` Hermitian-sum gate.  This allows ``T^(1/2)``
    beyond square root and is not supplied by a verified published theorem.
    """
    modulus = F(6)
    raw_dual = modulus - F(5, 2)
    ambient = F(3) + F(3) + raw_dual + raw_dual
    prefactor = F(5, 2) + F(5, 2) - modulus
    gate_target = F(6) - prefactor
    square_root = ambient / 2
    return MidpointHermitianCompletionAudit(
        common_modulus_exponent=modulus,
        raw_dual_c_exponent=raw_dual,
        raw_dual_v_exponent=raw_dual,
        completed_ambient_exponent=ambient,
        completion_prefactor_exponent=prefactor,
        completed_gate_target_exponent=gate_target,
        square_root_ambient_exponent=square_root,
        allowance_beyond_square_root_exponent=gate_target - square_root,
        midpoint_coefficient_is_unit=True,
        midpoint_coefficient_is_involution=True,
        exchange_negates_midpoint_coefficient=True,
        same_frequency_swap_is_conjugate=True,
        centered_multiplier_zero_on_c_zero_row=True,
        centered_multiplier_zero_on_v_zero_column=True,
        modular_involution_phase_is_near_diagonal_small=False,
        published_bound_verified=False,
    )


def midpoint_salie_phase_identity(
    *,
    r: int,
    s: int,
    c: int,
    v: int,
) -> dict[str, Fraction | bool]:
    """Match the midpoint phase to an antisymmetric Hermitian fraction.

    For least positive inverses and coprime ``r,s>1``, one has
    ``r*rbar_s+s*sbar_r=1+r*s``.  Division by two therefore retains a
    parity correction:

        A*c*v/(2*r*s)
        = c*v/2 * (rbar_s/s-sbar_r/r) + c*v/2  (mod 1).

    The last term is ``0`` or ``1/2`` and can be absorbed into the dual
    frequency coefficient as ``(-1)^(c*v)``.
    """
    if r <= 1 or s <= 1:
        raise ValueError("Salié-phase factors must exceed one")
    if gcd(r, s) != 1:
        raise ValueError("Salié-phase identity requires gcd(r,s)=1")

    def mod_one(value: Fraction) -> Fraction:
        return F(value.numerator % value.denominator, value.denominator)

    modulus = 2 * r * s
    inverse_r_mod_s = pow(r, -1, s)
    inverse_s_mod_r = pow(s, -1, r)
    coefficient = (2 * r * inverse_r_mod_s - 1) % modulus
    midpoint = F((coefficient * c * v) % modulus, modulus)
    hermitian = mod_one(
        F(c * v, 2)
        * (F(inverse_r_mod_s, s) - F(inverse_s_mod_r, r))
    )
    parity = F((c * v) % 2, 2)
    return {
        "midpoint_phase": midpoint,
        "hermitian_phase": hermitian,
        "parity_correction": parity,
        "identity_exact_mod_one": midpoint == mod_one(hermitian + parity),
    }


def midpoint_published_hermitian_adapter_audit(
) -> MidpointPublishedHermitianAdapterAudit:
    """Compare the midpoint operator with the withdrawn Hermitian claim.

    The claimed Theorems 1.4 and 1.8 of arXiv:2601.00292v1 concern a
    fixed numerator and separated two-variable coefficients.  At
    ``r,s=T^3`` and the outer dual corner ``a=|c*v|=T^7``, their displayed
    claimed bound has exponent six after inserting the two L2 norms,
    exactly the trivial size of the ``r,s`` sum.  Even in the bulk
    ``a<=T^6`` it has exponent ``23/4`` and does not average the ``c,v``
    variables.  Version 2 withdraws the improvement because (2.53)
    missed an ``L^2`` factor, changing ``L^5`` to ``L^7``.
    """
    numerator = F(7)
    trivial = F(6)
    l2_norms = F(3)
    common_factors = F(1, 2) + F(1) - F(1, 4)
    outer = l2_norms + numerator / 4 + common_factors
    bulk = l2_norms + F(6, 4) + common_factors
    return MidpointPublishedHermitianAdapterAudit(
        numerator_exponent=numerator,
        rs_trivial_exponent=trivial,
        withdrawn_claimed_outer_inner_bound_exponent=outer,
        withdrawn_claimed_outer_inner_saving_exponent=trivial - outer,
        withdrawn_claimed_bulk_inner_bound_exponent=bulk,
        withdrawn_claimed_bulk_inner_saving_exponent=trivial - bulk,
        theorem_has_moving_numerator=False,
        theorem_accepts_joint_r_s_c_v_coefficient=False,
        theorem_supplies_c_v_frequency_average=False,
        claim_withdrawn_for_missing_l_squared_factor=True,
        corrected_argument_gives_claimed_improvement=False,
        withdrawn_claim_closes_midpoint_gate=False,
        source="arXiv:2601.00292v2 author comment; v1 Theorems 1.4 and 1.8",
    )


def midpoint_unitary_divisor_root_bijection(*, n: int) -> dict[str, object]:
    """Bijection squarefree factorizations ``n=r*s`` with roots mod ``2*n``.

    For an ordered coprime factorization, the midpoint coefficient

        A = 2*r*inverse(r mod s)-1  (mod 2*n)

    is a square root of one.  Odd prime factors are recovered from the
    signs of ``A`` modulo each prime.  If ``2|n``, the residue modulo four
    records whether the factor two lies in ``r`` or ``s``.  Non-squarefree
    inputs are returned with empty support because their Möbius weight is
    zero in the application.
    """
    if n <= 1:
        raise ValueError("unitary-divisor product must exceed one")

    remaining = n
    prime_factors: list[int] = []
    divisor = 2
    squarefree = True
    while divisor * divisor <= remaining:
        if remaining % divisor:
            divisor += 1
            continue
        remaining //= divisor
        prime_factors.append(divisor)
        if remaining % divisor == 0:
            squarefree = False
            break
        divisor += 1
    if squarefree and remaining > 1:
        prime_factors.append(remaining)
    if not squarefree:
        return {
            "squarefree": False,
            "ordered_factorization_count": 0,
            "root_count": 0,
            "expected_root_count": 0,
            "factorizations": (),
            "roots": (),
            "factorization_to_root_injective": False,
            "root_to_factorization_exact": False,
            "bijection_exact": False,
        }

    modulus = 2 * n
    odd_part = n // 2 if n % 2 == 0 else n
    factorizations: list[dict[str, int | bool]] = []
    for r in range(1, n + 1):
        if n % r:
            continue
        s = n // r
        if gcd(r, s) != 1:
            continue
        inverse_r_mod_s = pow(r, -1, s)
        coefficient = (2 * r * inverse_r_mod_s - 1) % modulus
        recovered_r_odd = gcd(coefficient + 1, odd_part)
        recovered_s_odd = gcd(coefficient - 1, odd_part)
        if n % 2:
            recovered_r = recovered_r_odd
            recovered_s = recovered_s_odd
        elif coefficient % 4 == 3:
            recovered_r = 2 * recovered_r_odd
            recovered_s = recovered_s_odd
        else:
            recovered_r = recovered_r_odd
            recovered_s = 2 * recovered_s_odd
        factorizations.append(
            {
                "r": r,
                "s": s,
                "coefficient": coefficient,
                "coefficient_squared_is_one": (
                    coefficient * coefficient % modulus == 1
                ),
                "recovered_r": recovered_r,
                "recovered_s": recovered_s,
            }
        )
    roots = tuple(
        residue
        for residue in range(modulus)
        if residue * residue % modulus == 1
    )
    coefficients = tuple(
        int(item["coefficient"]) for item in factorizations
    )
    recovery_exact = all(
        item["r"] == item["recovered_r"]
        and item["s"] == item["recovered_s"]
        for item in factorizations
    )
    expected_count = 2 ** len(prime_factors)
    return {
        "squarefree": True,
        "ordered_factorization_count": len(factorizations),
        "root_count": len(roots),
        "expected_root_count": expected_count,
        "factorizations": tuple(factorizations),
        "roots": roots,
        "factorization_to_root_injective": len(set(coefficients)) == len(coefficients),
        "root_to_factorization_exact": recovery_exact and set(coefficients) == set(roots),
        "bijection_exact": (
            len(factorizations) == len(roots) == expected_count
            and recovery_exact
            and set(coefficients) == set(roots)
        ),
    }


def midpoint_unitary_divisor_audit() -> MidpointUnitaryDivisorAudit:
    """Record the balanced-box ledger after ``n=r*s`` reindexing."""
    return MidpointUnitaryDivisorAudit(
        product_variable_exponent=F(6),
        root_modulus_exponent=F(6),
        physical_numerator_exponent=F(5),
        dual_numerator_exponent=F(7),
        factorization_root_bijection_exact=True,
        mobius_product_collapses_to_single_mobius=True,
        root_multiplicity_is_subpower=True,
        balanced_dyadic_condition_is_root_filter=True,
        root_trace_coefficient_remains_joint=True,
        unitary_root_trace_bound_verified=False,
    )


def midpoint_root_fraction_identity(*, r: int, s: int) -> dict[str, int | bool]:
    """Return and recover the reduced root fraction ``A/(2*r*s)``.

    Recovery of the ordered factorization from the root is asserted only
    on the squarefree support on which the Möbius product is nonzero.
    """
    if r <= 0 or s <= 0:
        raise ValueError("root-fraction factors must be positive")
    if gcd(r, s) != 1:
        raise ValueError("root-fraction factors must be coprime")
    product = r * s
    root_data = midpoint_unitary_divisor_root_bijection(n=product)
    if not root_data["squarefree"]:
        raise ValueError("root-fraction recovery is restricted to squarefree support")
    modulus = 2 * product
    coefficient = (2 * r * pow(r, -1, s) - 1) % modulus
    matching = tuple(
        item
        for item in root_data["factorizations"]
        if item["coefficient"] == coefficient
    )
    recovered_r = int(matching[0]["recovered_r"]) if len(matching) == 1 else 0
    recovered_s = int(matching[0]["recovered_s"]) if len(matching) == 1 else 0
    return {
        "numerator": coefficient,
        "denominator": modulus,
        "fraction_is_reduced": gcd(coefficient, modulus) == 1,
        "recovered_r": recovered_r,
        "recovered_s": recovered_s,
        "factorization_recovered_exactly": recovered_r == r and recovered_s == s,
    }


def midpoint_root_farey_large_sieve_audit(
) -> MidpointRootFareyLargeSieveAudit:
    """Audit the generic additive large sieve on root fractions.

    Reduced denominators have exponent six, hence reciprocal spacing has
    exponent twelve.  Cauchy over the ``T^6`` root points and the product
    energy of either numerator gauge leaves the same ``T^(11/2)`` deficit.
    The calculation optimistically assumes separation of the actual joint
    transform coefficient.
    """
    points = F(6)
    denominator = F(6)
    spacing_reciprocal = 2 * denominator
    physical_length = F(5)
    physical_energy = F(5)
    physical_second_moment = max(physical_length, spacing_reciprocal) + physical_energy
    physical_bound = points / 2 + physical_second_moment / 2
    physical_target = F(6)
    dual_length = F(7)
    dual_energy = F(7)
    dual_second_moment = max(dual_length, spacing_reciprocal) + dual_energy
    dual_bound = points / 2 + dual_second_moment / 2
    dual_target = F(7)
    return MidpointRootFareyLargeSieveAudit(
        root_point_count_exponent=points,
        denominator_exponent=denominator,
        reciprocal_spacing_exponent=spacing_reciprocal,
        physical_numerator_length_exponent=physical_length,
        physical_product_energy_exponent=physical_energy,
        physical_large_sieve_bound_exponent=physical_bound,
        physical_target_exponent=physical_target,
        physical_deficit_exponent=physical_bound - physical_target,
        dual_numerator_length_exponent=dual_length,
        dual_product_energy_exponent=dual_energy,
        dual_large_sieve_bound_exponent=dual_bound,
        dual_target_exponent=dual_target,
        dual_deficit_exponent=dual_bound - dual_target,
        root_fractions_injective=True,
        root_fractions_reduced=True,
        actual_joint_coefficient_is_separated=False,
        root_farey_large_sieve_closes_gate=False,
    )


def midpoint_root_crt_phase_identity(
    *,
    a: int,
    b: int,
    root_a: int,
    root_b: int,
    numerator: int,
) -> dict[str, Fraction | int | bool]:
    """Compose roots modulo ``2*a`` and ``2*b`` and split the phase.

    Since both roots are odd, put ``y_a=(root_a-1)/2`` and similarly for
    ``b``.  Ordinary CRT composes ``y`` modulo ``a*b``; then ``A=2*y+1``
    is the unique compatible root modulo ``2*a*b``.  Dividing the CRT
    identity by ``a*b`` gives two reciprocal phases plus the exact small
    correction ``numerator/(2*a*b)``.
    """
    if a <= 1 or b <= 1:
        raise ValueError("root CRT factors must exceed one")
    if gcd(a, b) != 1:
        raise ValueError("root CRT factors must be coprime")
    if root_a % 2 == 0 or root_b % 2 == 0:
        raise ValueError("roots modulo twice a factor must be odd")
    if root_a * root_a % (2 * a) != 1:
        raise ValueError("root_a is not a square root of one modulo 2*a")
    if root_b * root_b % (2 * b) != 1:
        raise ValueError("root_b is not a square root of one modulo 2*b")

    def mod_one(value: Fraction) -> Fraction:
        return F(value.numerator % value.denominator, value.denominator)

    y_a = ((root_a % (2 * a)) - 1) // 2
    y_b = ((root_b % (2 * b)) - 1) // 2
    inverse_b_mod_a = pow(b, -1, a)
    inverse_a_mod_b = pow(a, -1, b)
    product = a * b
    y = (
        y_a * b * inverse_b_mod_a
        + y_b * a * inverse_a_mod_b
    ) % product
    combined_root = 2 * y + 1
    combined_modulus = 2 * product
    full_phase = F((numerator * combined_root) % combined_modulus, combined_modulus)
    correction = mod_one(F(numerator, combined_modulus))
    left = mod_one(F(numerator * y_a * inverse_b_mod_a, a))
    right = mod_one(F(numerator * y_b * inverse_a_mod_b, b))
    return {
        "combined_root": combined_root,
        "combined_modulus": combined_modulus,
        "combined_root_squared_is_one": (
            combined_root * combined_root % combined_modulus == 1
        ),
        "combined_root_restricts_to_root_a": (
            combined_root - root_a
        ) % (2 * a) == 0,
        "combined_root_restricts_to_root_b": (
            combined_root - root_b
        ) % (2 * b) == 0,
        "full_phase": full_phase,
        "small_correction_phase": correction,
        "left_reciprocal_phase": left,
        "right_reciprocal_phase": right,
        "phase_split_exact_mod_one": full_phase == mod_one(correction + left + right),
    }


def midpoint_root_type_ii_audit() -> MidpointRootTypeIIAudit:
    """Record the balanced root-CRT Type-II interface."""
    return MidpointRootTypeIIAudit(
        product_exponent=F(6),
        left_factor_exponent=F(3),
        right_factor_exponent=F(3),
        physical_numerator_exponent=F(5),
        dual_numerator_exponent=F(7),
        generalized_crt_exact=True,
        reciprocal_phase_split_exact=True,
        left_factor_has_truncated_divisor_coefficient=True,
        right_factor_retains_mobius=True,
        root_fibers_are_subpower=True,
        completed_centering_exact=True,
        physical_zero_residue_vanishes=True,
        physical_centered_subtraction_present=False,
        published_hermitian_theorem_has_root_dependent_numerator=False,
        actual_transform_coefficient_remains_joint=True,
        root_type_ii_bound_verified=False,
    )


def midpoint_root_four_factor_phase_identity(
    *,
    d_r: int,
    d_s: int,
    e_r: int,
    e_s: int,
    numerator: int,
) -> dict[str, Fraction | int | bool]:
    """Unfold both root fibers into four coprime factor variables.

    The roots attached to ``d=d_r*d_s`` and ``e=e_r*e_s`` take sign
    ``-1`` on the ``r`` factors and sign ``+1`` on the ``s`` factors.
    Thus the combined root recovers ``r=d_r*e_r`` and ``s=d_s*e_s``.
    The two CRT reciprocal phases become classical Kloosterman fractions

        -k*inverse(d_s*e mod d_r)/d_r,
        -k*inverse(e_s*d mod e_r)/e_r.

    Denominator one contributes the zero phase.
    """
    factors = (d_r, d_s, e_r, e_s)
    if any(factor <= 0 for factor in factors):
        raise ValueError("root four-factor variables must be positive")
    pairwise_coprime = all(
        gcd(factors[i], factors[j]) == 1
        for i in range(len(factors))
        for j in range(i + 1, len(factors))
    )
    if not pairwise_coprime:
        raise ValueError("root four-factor variables must be pairwise coprime")

    d = d_r * d_s
    e = e_r * e_s
    if d <= 1 or e <= 1:
        raise ValueError("both Type-II products must exceed one")

    def mod_one(value: Fraction) -> Fraction:
        return F(value.numerator % value.denominator, value.denominator)

    def ordered_root(r_factor: int, s_factor: int) -> int:
        modulus = 2 * r_factor * s_factor
        inverse = pow(r_factor, -1, s_factor) if s_factor > 1 else 0
        return (2 * r_factor * inverse - 1) % modulus

    def negative_inverse_phase(value: int, modulus: int) -> Fraction:
        if modulus == 1:
            return F(0)
        return mod_one(F(-numerator * pow(value, -1, modulus), modulus))

    root_d = ordered_root(d_r, d_s)
    root_e = ordered_root(e_r, e_s)
    crt = midpoint_root_crt_phase_identity(
        a=d,
        b=e,
        root_a=root_d,
        root_b=root_e,
        numerator=numerator,
    )
    recovered_r = d_r * e_r
    recovered_s = d_s * e_s
    original_root = ordered_root(recovered_r, recovered_s)
    combined_modulus = 2 * d * e
    left_phase = negative_inverse_phase(d_s * e, d_r)
    right_phase = negative_inverse_phase(e_s * d, e_r)
    correction = mod_one(F(numerator, combined_modulus))
    four_factor_phase = mod_one(correction + left_phase + right_phase)
    full_phase = crt["full_phase"]
    phase_exact = full_phase == four_factor_phase
    root_recovers = int(crt["combined_root"]) == original_root
    extreme_sector = d_s == 1 and e_r == 1
    extreme_exact = (
        extreme_sector
        and recovered_r == d
        and recovered_s == e
        and phase_exact
    )
    return {
        "d": d,
        "e": e,
        "root_d": root_d,
        "root_e": root_e,
        "combined_root": int(crt["combined_root"]),
        "recovered_r": recovered_r,
        "recovered_s": recovered_s,
        "full_phase": full_phase,
        "small_correction_phase": correction,
        "left_kloosterman_phase": left_phase,
        "right_kloosterman_phase": right_phase,
        "four_factor_phase": four_factor_phase,
        "all_factors_pairwise_coprime": pairwise_coprime,
        "combined_root_recovers_original_factorization": root_recovers,
        "root_phase_equals_four_factor_phase": phase_exact,
        "extreme_sector_recovers_original_fraction": extreme_exact,
    }


def midpoint_root_four_factor_audit() -> MidpointRootFourFactorAudit:
    """Record the central four-factor Type-II interface and proof status."""
    return MidpointRootFourFactorAudit(
        left_product_exponent=F(3),
        right_product_exponent=F(3),
        physical_numerator_exponent=F(5),
        recovered_r_exponent=F(3),
        recovered_s_exponent=F(3),
        root_fibers_unfold_to_ordered_factorizations=True,
        four_factors_are_pairwise_coprime=True,
        truncated_divisor_coefficient_remains_on_left_product=True,
        mobius_splits_over_right_factors=True,
        kloosterman_phase_identity_exact=True,
        completed_centering_exact=True,
        physical_zero_residue_vanishes=True,
        physical_centered_subtraction_present=False,
        extreme_sector_recovers_hard_fraction=True,
        actual_smooth_weight_remains_joint=True,
        four_factor_type_ii_bound_verified=False,
    )


def midpoint_involution_resonance_lattice_identity(
    *,
    r: int,
    s: int,
    h: int,
    poisson_frequency: int,
) -> dict[str, int | bool]:
    """Convert a physical Poisson resonance into a two-variable lattice.

    For ``Q=2*r*s`` and ``A=2*r*inverse(r mod s)-1``, put
    ``u=A*h+v*Q``.  The involution signs give ``u=-h (mod 2r)`` and
    ``u=h (mod 2s)``.  Hence the integers

        a=(h+u)/(2r),  b=(h-u)/(2s)

    are well defined and satisfy ``h=r*a+s*b`` and ``u=r*a-s*b``.
    This is an exact bijection, including when one factor is even.
    """
    if r <= 1 or s <= 1:
        raise ValueError("midpoint resonance factors must exceed one")
    if gcd(r, s) != 1:
        raise ValueError("midpoint resonance factors must be coprime")
    modulus = 2 * r * s
    midpoint_root = (2 * r * pow(r, -1, s) - 1) % modulus
    resonance_integer = midpoint_root * h + poisson_frequency * modulus
    numerator_a = h + resonance_integer
    numerator_b = h - resonance_integer
    a_integral = numerator_a % (2 * r) == 0
    b_integral = numerator_b % (2 * s) == 0
    a = numerator_a // (2 * r) if a_integral else 0
    b = numerator_b // (2 * s) if b_integral else 0
    h_reconstructed = r * a + s * b
    u_reconstructed = r * a - s * b
    root_congruences = (
        (resonance_integer + h) % (2 * r) == 0
        and (resonance_integer - h) % (2 * s) == 0
    )
    return {
        "modulus": modulus,
        "midpoint_root": midpoint_root,
        "resonance_integer": resonance_integer,
        "a": a,
        "b": b,
        "h_equals_r_a_plus_s_b": h_reconstructed == h,
        "u_equals_r_a_minus_s_b": u_reconstructed == resonance_integer,
        "root_congruences_exact": root_congruences,
        "lattice_bijection_exact": (
            a_integral
            and b_integral
            and h_reconstructed == h
            and u_reconstructed == resonance_integer
        ),
    }


def midpoint_physical_poisson_audit() -> MidpointPhysicalPoissonAudit:
    """Record the central physical-Poisson resonance ledger."""
    modulus = F(6)
    h_length = F(5, 2)
    delta_length = F(5, 2)
    resonance = modulus - delta_length
    factor_length = F(3)
    lattice_parameter = resonance - factor_length
    pointwise = delta_length + lattice_parameter
    raw = h_length + delta_length
    outer_points = 2 * factor_length
    outer_target = F(6)
    required_outer_saving = outer_points + pointwise - outer_target
    return MidpointPhysicalPoissonAudit(
        modulus_exponent=modulus,
        h_exponent=h_length,
        delta_exponent=delta_length,
        resonance_window_exponent=resonance,
        lattice_parameter_exponent=lattice_parameter,
        pointwise_bilinear_bound_exponent=pointwise,
        raw_bilinear_exponent=raw,
        physical_oscillation_saving_exponent=raw - pointwise,
        outer_root_point_exponent=outer_points,
        outer_target_exponent=outer_target,
        required_outer_saving_exponent=required_outer_saving,
        resonance_lattice_bijection_exact=True,
        one_variable_poisson_exact=True,
        joint_weight_has_uniform_delta_derivatives=True,
        determinant_line_correspondence_exact=True,
        physical_poisson_route_is_independent=False,
        outer_mobius_square_root_verified=False,
    )


def odd_root_trace_salie_coefficient_identity(
    *,
    modulus: int,
    numerator: int,
) -> dict[str, object]:
    """Check the odd squarefree root-trace/Salié identity coefficientwise.

    Put ``b=numerator^2/4 (mod modulus)`` and let ``chi`` be the Jacobi
    symbol.  The exact group-ring identity is

        sum_x^* chi(x) [x+b*xbar]
        = (sum_y chi(y)[y]) (sum_{A^2=1}[numerator*A]).

    Evaluating the basis element ``[z]`` as ``e(z/modulus)`` gives
    ``T(1,b;modulus)=tau(chi) R_numerator(modulus)`` without numerical
    approximation.
    """
    if modulus <= 1 or modulus % 2 == 0:
        raise ValueError("Salié root-trace modulus must be odd and exceed one")
    if gcd(numerator, modulus) != 1:
        raise ValueError("Salié numerator must be coprime to the modulus")

    remaining = modulus
    prime_factors: list[int] = []
    prime = 3
    squarefree = True
    while prime * prime <= remaining:
        if remaining % prime:
            prime += 2
            continue
        remaining //= prime
        prime_factors.append(prime)
        if remaining % prime == 0:
            squarefree = False
            break
        prime += 2
    if squarefree and remaining > 1:
        prime_factors.append(remaining)
    if not squarefree:
        raise ValueError("Salié coefficient identity audit uses squarefree modulus")

    def jacobi_symbol(value: int, odd_modulus: int) -> int:
        value %= odd_modulus
        sign = 1
        while value:
            while value % 2 == 0:
                value //= 2
                if odd_modulus % 8 in (3, 5):
                    sign = -sign
            value, odd_modulus = odd_modulus, value
            if value % 4 == odd_modulus % 4 == 3:
                sign = -sign
            value %= odd_modulus
        return sign if odd_modulus == 1 else 0

    salie_parameter = (
        numerator * numerator * pow(4, -1, modulus)
    ) % modulus
    salie_coefficients = {residue: 0 for residue in range(modulus)}
    for x in range(modulus):
        if gcd(x, modulus) != 1:
            continue
        exponent = (
            x + salie_parameter * pow(x, -1, modulus)
        ) % modulus
        salie_coefficients[exponent] += jacobi_symbol(x, modulus)

    roots = tuple(
        residue
        for residue in range(modulus)
        if residue * residue % modulus == 1
    )
    gauss_root_coefficients = {residue: 0 for residue in range(modulus)}
    for y in range(modulus):
        coefficient = jacobi_symbol(y, modulus)
        if coefficient == 0:
            continue
        for root in roots:
            exponent = (y + numerator * root) % modulus
            gauss_root_coefficients[exponent] += coefficient
    return {
        "modulus": modulus,
        "numerator": numerator,
        "salie_parameter": salie_parameter,
        "prime_factors": tuple(prime_factors),
        "root_count": len(roots),
        "modulus_is_odd_squarefree": squarefree and modulus % 2 == 1,
        "numerator_is_coprime_to_modulus": gcd(numerator, modulus) == 1,
        "salie_coefficients": tuple(salie_coefficients.items()),
        "gauss_root_coefficients": tuple(gauss_root_coefficients.items()),
        "salie_coefficient_identity_exact": (
            salie_coefficients == gauss_root_coefficients
        ),
    }


def root_salie_adapter_audit() -> RootSalieAdapterAudit:
    """Audit DFI's fixed-numerator Salié modulus sum on the hard box."""
    modulus = F(6)
    numerator = F(5)
    # DFI Theorem 7.1 has x^(47/118+35/59)=x^(117/118)
    # when x dominates the fixed Salié parameter.
    fixed_bound = modulus * F(117, 118)
    absolute_k_sum = numerator + fixed_bound
    target = F(6)
    return RootSalieAdapterAudit(
        modulus_exponent=modulus,
        physical_numerator_exponent=numerator,
        fixed_numerator_bound_exponent=fixed_bound,
        fixed_numerator_saving_exponent=modulus - fixed_bound,
        absolute_numerator_sum_bound_exponent=absolute_k_sum,
        physical_target_exponent=target,
        absolute_numerator_sum_deficit_exponent=absolute_k_sum - target,
        odd_full_root_trace_identity_exact=True,
        even_midpoint_modulus_adapter_verified=False,
        theorem_accepts_balanced_root_filter=False,
        theorem_accepts_mobius_modulus_weight=False,
        theorem_accepts_moving_numerator=False,
        square_numerator_exception_covered=False,
        theorem_accepts_joint_transform_weight=False,
        salie_adapter_closes_root_gate=False,
    )


def square_product_common_kernel_identity(
    *,
    left: int,
    right: int,
) -> dict[str, int | bool]:
    """Parametrize ``left*right`` square by one squarefree kernel.

    Positive integers have square product exactly when their squarefree
    kernels agree.  In that case ``left=g*x^2`` and ``right=g*y^2``
    with one squarefree ``g`` and uniquely determined positive ``x,y``.
    """
    if left <= 0 or right <= 0:
        raise ValueError("square-product variables must be positive")

    def squarefree_kernel(value: int) -> int:
        kernel = 1
        prime = 2
        remaining = value
        while prime * prime <= remaining:
            parity = 0
            while remaining % prime == 0:
                remaining //= prime
                parity ^= 1
            if parity:
                kernel *= prime
            prime += 1
        if remaining > 1:
            kernel *= remaining
        return kernel

    left_kernel = squarefree_kernel(left)
    right_kernel = squarefree_kernel(right)
    common = left_kernel == right_kernel
    kernel = left_kernel if common else 0
    left_quotient = left // kernel if common else 0
    right_quotient = right // kernel if common else 0
    left_factor = isqrt(left_quotient) if common else 0
    right_factor = isqrt(right_quotient) if common else 0
    product_root = isqrt(left * right)
    product_square = product_root * product_root == left * right
    return {
        "left": left,
        "right": right,
        "left_squarefree_kernel": left_kernel,
        "right_squarefree_kernel": right_kernel,
        "common_kernel_exists": common,
        "common_squarefree_kernel": kernel,
        "left_square_factor": left_factor,
        "right_square_factor": right_factor,
        "product_is_square": product_square,
        "left_reconstruction_exact": (
            common and kernel * left_factor * left_factor == left
        ),
        "right_reconstruction_exact": (
            common and kernel * right_factor * right_factor == right
        ),
    }


def root_salie_joint_average_audit() -> RootSalieJointAverageAudit:
    """Match joint Salié averaging to the balanced BCR endpoint."""
    left = F(3)
    right = F(3)
    numerator = F(5)
    total = left + right + numerator
    term_1 = F(17, 20) * total + F(1, 4) * max(left, right)
    term_2 = (
        F(7, 8) * (left + right)
        + numerator
        + F(1, 8) * max(left, right)
    )
    bound = max(term_1, term_2)
    target = F(6)
    square_pairs = F(5, 2)
    # In DFI Theorem 4, with modulus length x=T^6 and square parameter
    # a=T^5, the exceptional main term comes from n <= y.  Their
    # choices (5.4), (5.14) give y=T^(7/5), z=T^(174/59).  The balanced
    # roots m,n=T^3 lie in S3, so that main term is absent here.
    short_factor_cutoff = min(
        -F(1, 5) * numerator + F(2, 5) * (left + right),
        -F(1, 2) * numerator + F(2, 3) * (left + right),
    )
    long_long_cutoff = (
        -F(6, 59) * max(numerator, left + right)
        + F(35, 59) * (left + right)
    )
    # DFI Theorem H, formula (1.5), for each fixed a=t^2:
    # ||alpha|| ||beta|| (a+MN)^(3/8) (M+N)^(11/48).
    fixed_square_hermitian = (
        F(1, 2) * (left + right)
        + F(3, 8) * max(numerator, left + right)
        + F(11, 48) * max(left, right)
    )
    absolute_square_family = square_pairs + fixed_square_hermitian
    return RootSalieJointAverageAudit(
        left_root_factor_exponent=left,
        right_root_factor_exponent=right,
        physical_numerator_exponent=numerator,
        bcr_term_1_exponent=term_1,
        bcr_term_2_exponent=term_2,
        bcr_bound_exponent=bound,
        physical_target_exponent=target,
        bcr_deficit_exponent=bound - target,
        square_product_pair_count_exponent=square_pairs,
        dfi_square_main_short_factor_cutoff_exponent=short_factor_cutoff,
        dfi_long_long_cutoff_exponent=long_long_cutoff,
        balanced_root_factor_exponent=min(left, right),
        fixed_square_hermitian_bound_exponent=fixed_square_hermitian,
        absolute_square_family_bound_exponent=absolute_square_family,
        absolute_square_family_deficit_exponent=(
            absolute_square_family - target
        ),
        salie_factorization_matches_midpoint_phase=True,
        joint_average_is_existing_bcr_endpoint=True,
        bcr_accepts_mobius_coefficients=True,
        bcr_uses_mobius_beyond_l2=False,
        balanced_root_filter_excludes_dfi_square_main=(
            min(left, right) > long_long_cutoff > short_factor_cutoff
        ),
        joint_salie_route_closes_root_gate=False,
    )


def square_salie_double_gauss_identity(
    *,
    r: int,
    s: int,
    square_root: int,
) -> dict[str, object]:
    """Linearize a square Salié numerator by two quadratic Gauss sums.

    Coefficient tables modulo ``r*s`` verify

        G(-2r;s) G(2s;r) e(2t^2(rbar/s-sbar/r))
        = sum_{x mod s,y mod r}
          e((-2r*x^2+4t*x)/s + (2s*y^2+4t*y)/r).

    The exponent on the right is also exactly
    ``2*z*(w+2*t)/(r*s)`` for ``z=r*x+s*y`` and ``w=s*y-r*x``.
    """
    if r <= 1 or s <= 1 or r % 2 == 0 or s % 2 == 0:
        raise ValueError("double-Gauss factors must be odd and exceed one")
    if gcd(r, s) != 1:
        raise ValueError("double-Gauss factors must be coprime")
    modulus = r * s
    inverse_r_mod_s = pow(r, -1, s)
    inverse_s_mod_r = pow(s, -1, r)
    target_numerator = (
        2
        * square_root
        * square_root
        * (r * inverse_r_mod_s - s * inverse_s_mod_r)
    ) % modulus

    left_coefficients = {residue: 0 for residue in range(modulus)}
    for u in range(s):
        for v in range(r):
            exponent = (
                -2 * r * r * u * u
                + 2 * s * s * v * v
                + target_numerator
            ) % modulus
            left_coefficients[exponent] += 1

    right_coefficients = {residue: 0 for residue in range(modulus)}
    factorized_coefficients = {residue: 0 for residue in range(modulus)}
    phase_factorization = True
    for x in range(s):
        for y in range(r):
            exponent = (
                -2 * r * r * x * x
                + 4 * square_root * r * x
                + 2 * s * s * y * y
                + 4 * square_root * s * y
            ) % modulus
            z = r * x + s * y
            w = s * y - r * x
            factorized = (2 * z * (w + 2 * square_root)) % modulus
            right_coefficients[exponent] += 1
            factorized_coefficients[factorized] += 1
            phase_factorization = phase_factorization and exponent == factorized

    def jacobi_symbol(value: int, odd_modulus: int) -> int:
        value %= odd_modulus
        sign = 1
        while value:
            while value % 2 == 0:
                value //= 2
                if odd_modulus % 8 in (3, 5):
                    sign = -sign
            value, odd_modulus = odd_modulus, value
            if value % 4 == odd_modulus % 4 == 3:
                sign = -sign
            value %= odd_modulus
        return sign if odd_modulus == 1 else 0

    direct_character = jacobi_symbol(-2 * r, s) * jacobi_symbol(2 * s, r)
    minus_one_s = -1 if s % 4 == 3 else 1
    two_s = -1 if s % 8 in (3, 5) else 1
    two_r = -1 if r % 8 in (3, 5) else 1
    reciprocity = -1 if r % 4 == s % 4 == 3 else 1
    mod8_character = minus_one_s * two_s * two_r * reciprocity
    return {
        "r": r,
        "s": s,
        "square_root": square_root,
        "modulus": modulus,
        "target_phase_numerator": target_numerator,
        "factors_are_odd_coprime": r % 2 == s % 2 == 1 and gcd(r, s) == 1,
        "left_coefficients": tuple(left_coefficients.items()),
        "right_coefficients": tuple(right_coefficients.items()),
        "quadratic_completion_identity_exact": (
            left_coefficients == right_coefficients
        ),
        "combined_phase_factorization_exact": (
            phase_factorization and right_coefficients == factorized_coefficients
        ),
        "gauss_product_character": direct_character,
        "mod8_character": mod8_character,
        "gauss_product_character_is_mod8_local": (
            direct_character == mod8_character
        ),
    }


def square_salie_gauss_completion_audit() -> SquareSalieGaussCompletionAudit:
    """Record the hard-box ledger after double quadratic completion."""
    r = F(3)
    s = F(3)
    square_root = F(5, 2)
    x = s
    y = r
    normalization = -F(1, 2) * (r + s)
    resonance = r + s - square_root
    localized_pointwise = square_root + resonance + normalization
    direct_square = square_root
    return SquareSalieGaussCompletionAudit(
        r_exponent=r,
        s_exponent=s,
        square_root_exponent=square_root,
        x_exponent=x,
        y_exponent=y,
        gauss_normalization_exponent=normalization,
        t_poisson_resonance_exponent=resonance,
        localized_pointwise_exponent=localized_pointwise,
        direct_square_sector_pointwise_exponent=direct_square,
        double_gauss_identity_exact=True,
        cross_character_depends_only_on_mod8=True,
        square_root_variable_is_linearized=True,
        remaining_quadratic_weight_is_joint=True,
        gauss_completion_improves_square_sector=(
            localized_pointwise < direct_square
        ),
        square_salie_gauss_route_closes_gate=False,
    )


def balanced_product_diagonal_parameterization(
    *,
    a: int,
    b: int,
    c: int,
    d: int,
) -> dict[str, int | bool]:
    """Parameterize the multiplicative diagonal ``a*b=c*d`` exactly.

    If ``g=(a,c)``, ``a=g*x`` and ``c=g*y``, then ``(x,y)=1``.
    Equality of the two products forces ``b=y*k`` and ``d=x*k``.
    This is the standard parameterization behind the logarithmic, rather
    than positive-power, cost of the balanced product diagonal.
    """
    if min(a, b, c, d) <= 0:
        raise ValueError("balanced-product variables must be positive")
    left_product = a * b
    right_product = c * d
    product_shift = left_product - right_product
    common = gcd(a, c)
    x = a // common
    y = c // common
    products_equal = product_shift == 0
    y_divides_b = products_equal and b % y == 0
    x_divides_d = products_equal and d % x == 0
    k_left = b // y if y_divides_b else 0
    k_right = d // x if x_divides_d else 0
    k = k_left if k_left == k_right else 0
    return {
        "a": a,
        "b": b,
        "c": c,
        "d": d,
        "left_product": left_product,
        "right_product": right_product,
        "product_shift": product_shift,
        "products_equal": products_equal,
        "common_factor": common,
        "left_primitive": x,
        "right_primitive": y,
        "complementary_factor": k,
        "primitive_pair_coprime": gcd(x, y) == 1,
        "left_reconstruction_exact": common * x == a,
        "right_reconstruction_exact": common * y == c,
        "complementary_reconstruction_exact": (
            products_equal
            and y_divides_b
            and x_divides_d
            and k > 0
            and y * k == b
            and x * k == d
        ),
    }


def mobius_product_shifted_variance_audit(
) -> MobiusProductShiftedVarianceAudit:
    """Reduce the separated top Möbius fourth moment to one shift gate."""
    factor = F(1)
    product = 2 * factor
    transform_shift = product - factor
    raw_offdiagonal = 3 * factor
    target = 2 * factor
    return MobiusProductShiftedVarianceAudit(
        factor_length_exponent=factor,
        product_length_exponent=product,
        transform_shift_exponent=transform_shift,
        diagonal_power_exponent=F(0),
        diagonal_logarithmic_exponent=F(1),
        raw_shifted_determinant_exponent=raw_offdiagonal,
        shifted_determinant_target_exponent=target,
        required_shifted_determinant_saving_exponent=(
            raw_offdiagonal - target
        ),
        product_convolution_identity_exact=True,
        diagonal_parameterization_exact=True,
        schwartz_tail_is_power_negligible=True,
        polylogarithmic_transition_collar_retained=True,
        equivalent_to_separated_mixed_fourth_moment_gate=True,
        shifted_mobius_determinant_bound_proved=False,
        original_signed_kernel_requires_component_gate=False,
        route_closes_mwkf_gate=False,
    )


def ganguly_guria_determinant_audit() -> GangulyGuriaDeterminantAudit:
    """Test the 2026 smooth determinant theorem at the critical collar.

    Ganguly--Guria Theorem 1.1 proves, for an unweighted smooth count on
    ``ad-bc=r`` with four variables of size ``X``, the pointwise error
    ``O_eps(|r|^theta X^(1+eps))``.  At ``X=T`` and ``|r|<=T^(1+o(1))``
    the current ``theta=7/64`` leaves exactly ``T^(7/64)`` after an
    absolute sum over the shifts.  Its published statement accepts no
    arithmetic coefficients and gives no uniform coefficient dependence
    for the extension mentioned in Remark 1.4.
    """
    variable = F(1)
    shift = F(1)
    theta = F(7, 64)
    fixed_error = variable + shift * theta
    aggregate_error = shift + fixed_error
    target = F(2)
    fixed_main = F(2) * variable
    aggregate_main = shift + fixed_main
    return GangulyGuriaDeterminantAudit(
        variable_length_exponent=variable,
        shift_range_exponent=shift,
        ramanujan_exponent=theta,
        fixed_shift_error_exponent=fixed_error,
        absolute_shift_sum_error_exponent=aggregate_error,
        shifted_determinant_target_exponent=target,
        absolute_shift_sum_power_deficit=aggregate_error - target,
        fixed_shift_main_exponent=fixed_main,
        absolute_shift_sum_main_exponent=aggregate_main,
        smooth_unweighted_fixed_shift_theorem_proved=True,
        distinct_tensor_weights_accepted_as_stated=False,
        arithmetic_coefficients_accepted=False,
        coefficient_form_uniformity_quantified=False,
        mobius_type_i_ii_adapter_proved=False,
        ramanujan_conjecture_removes_power_deficit=True,
        ramanujan_conjecture_supplies_logarithmic_saving=False,
        mobius_main_term_cancellation_proved=False,
        ganguly_guria_route_closes_mobius_gate=False,
    )


def mobius_triple_convolution_prime_power_coefficients(
) -> tuple[int, int, int, int, int]:
    """Return coefficients of ``(1-X)^3`` through ``X^4``.

    If ``f=1*h`` were the full convolution ``mu*mu``, then the local
    Dirichlet series of ``h`` would have to be ``(1-X)^3``.  The last
    zero makes the finite support explicit.
    """
    return (1, -3, 3, -1, 0)


def darbar_das_short_variance_audit() -> DarbarDasShortVarianceAudit:
    """Check the published variance class against ``mu*mu`` and ``C_U``.

    The critical product variable has size ``X=T^2`` and its natural
    short window has length ``H=T``.  Square-root variance is ``XH``
    (T-exponent 3), while the absolute/generic ledger is ``XH^2``
    (T-exponent 4).  Darbar--Das treat functions ``f=1 *_k h`` with
    ``h`` in two specified local classes.  For ``k=1`` and
    ``f=mu*mu``, one needs ``h=mu*mu*mu``: its local coefficients
    ``1,-3,3,-1`` are neither squarefree-supported nor completely
    multiplicative.  The dyadically restricted ``C_U`` is not a
    multiplicative function at all.
    """
    ambient = F(2)
    window = F(1)
    generic = ambient + F(2) * window
    target = ambient + window
    local = mobius_triple_convolution_prime_power_coefficients()
    return DarbarDasShortVarianceAudit(
        ambient_length_exponent=ambient,
        short_window_exponent=window,
        generic_short_variance_exponent=generic,
        required_short_variance_exponent=target,
        required_variance_saving_exponent=generic - target,
        full_mobius_convolution_zeta_power=-2,
        required_auxiliary_zeta_power=-3,
        required_auxiliary_prime_coefficient=local[1],
        required_auxiliary_prime_square_coefficient=local[2],
        required_auxiliary_prime_cube_coefficient=local[3],
        auxiliary_fits_squarefree_m_class=False,
        auxiliary_fits_completely_multiplicative_g_class=False,
        restricted_convolution_is_multiplicative=False,
        published_theorem_covers_full_mobius_convolution=False,
        published_theorem_covers_restricted_convolution=False,
        darbar_das_route_closes_mobius_gate=False,
    )


def restricted_product_ratio_coordinates(
    *,
    a: int,
    b: int,
    scale: int,
) -> dict[str, Fraction | bool]:
    """Verify the algebraic coordinates used in ratio Mellin inversion.

    With ``q=ab/scale^2`` and ``rho=a/b``, the formal coordinates
    ``sqrt(q)*sqrt(rho)`` and ``sqrt(q)/sqrt(rho)`` reconstruct
    ``a/scale`` and ``b/scale``.  Squaring avoids any floating-point
    square roots and checks the identities over exact rationals.
    """
    if min(a, b, scale) <= 0:
        raise ValueError("factors and scale must be positive")
    product_coordinate = F(a * b, scale * scale)
    factor_ratio = F(a, b)
    left_squared = product_coordinate * factor_ratio
    right_squared = product_coordinate / factor_ratio
    expected_left = F(a * a, scale * scale)
    expected_right = F(b * b, scale * scale)
    return {
        "product_coordinate": product_coordinate,
        "factor_ratio": factor_ratio,
        "left_coordinate_squared": left_squared,
        "right_coordinate_squared": right_squared,
        "left_reconstruction_squared_exact": left_squared == expected_left,
        "right_reconstruction_squared_exact": right_squared == expected_right,
    }


def mobius_square_convolution_second_moment_local_factor(
) -> tuple[int, ...]:
    """Return the Euler remainder after extracting zeta(s)^4.

    For ``f=mu*mu`` the local square series is ``1+4*z+z^2``.
    Multiplication by ``(1-z)^4`` removes the fourth-order zeta pole.
    The missing linear term proves absolute Euler convergence for
    ``Re(s)>1/2``.
    """
    zeta_inverse_fourth = (1, -4, 6, -4, 1)
    local_square = (1, 4, 1)
    product = [0] * (len(zeta_inverse_fourth) + len(local_square) - 1)
    for i, left in enumerate(zeta_inverse_fourth):
        for j, right in enumerate(local_square):
            product[i + j] += left * right
    return tuple(product)


def restricted_mobius_ratio_mellin_audit(
) -> RestrictedMobiusRatioMellinAudit:
    """Remove the dyadic divisor restriction by ratio Fourier inversion.

    For each ratio frequency ``tau``, the coefficient is the convolution
    of ``mu(n)n^(i tau/2)`` and ``mu(n)n^(-i tau/2)``.  It is
    multiplicative with Dirichlet series
    ``1/(zeta(s-i tau/2) zeta(s+i tau/2))``.  Rapid decay of the smooth
    ratio transform makes a uniform single-``tau`` variance estimate
    sufficient after Cauchy in the transform variable.
    """
    factor = F(1)
    product = F(2)
    window = F(1)
    return RestrictedMobiusRatioMellinAudit(
        factor_length_exponent=factor,
        product_length_exponent=product,
        short_window_exponent=window,
        required_short_variance_exponent=product + window,
        ratio_coordinate_identity_exact=True,
        ratio_fourier_inversion_exact=True,
        integrand_coefficient_is_multiplicative=True,
        shifted_inverse_zeta_dirichlet_series_exact=True,
        product_coordinate_weight_is_smooth=True,
        ratio_transform_is_rapidly_decaying=True,
        uniform_single_tau_variance_is_sufficient=True,
        tau_zero_is_full_mobius_convolution=True,
        tau_zero_square_dirichlet_series_zeta_pole_order=4,
        tau_zero_diagonal_log_exponent=3,
        required_diagonal_log_exponent=1,
        tau_zero_euler_remainder_has_no_prime_term=True,
        tau_zero_euler_remainder_converges_for_real_part_gt_half=True,
        tau_zero_formal_diagonal_log_excess=2,
        tau_zero_diagonal_excess_requires_offdiagonal_cancellation=True,
        diagonal_term_is_not_lower_bound_for_full_variance=True,
        tau_zero_diagonal_alone_disproves_uniform_gate=False,
        joint_ratio_recombination_has_restricted_diagonal_log_order_one=True,
        optimistic_mangerel_variance_exponent=product + F(2) * window,
        mangerel_power_deficit=window,
        mangerel_only_supplies_logarithmic_saving=True,
        uniform_tau_mangerel_hypotheses_verified=False,
        shifted_inverse_zeta_variance_proved=False,
        ratio_mellin_route_closes_mobius_gate=False,
    )


def basak_robles_zaharescu_mobius_convolution_audit(
) -> BasakRoblesZaharescuMobiusConvolutionAudit:
    """Test the published ``mu*mu`` additive-twist bound at ``H=sqrt(X)``.

    Basak--Robles--Zaharescu, Corollary 7.1, gives three terms
    ``X^(16/17)``, ``X q^(-1/6)``, and ``X^(7/8)q^(1/8)``.
    The local variance arc has length ``1/H`` and the squared Dirichlet
    kernel has size ``H^2`` there.  Hence a pointwise exponent ``sigma``
    contributes exponent ``1/2 + 2 sigma`` when ``H=X^(1/2)``.
    This adapter tests only the theorem as stated; it does not rule out a
    new proof-level local-L2 refinement of their Type I/II decomposition.
    """
    ambient = F(1)
    window = F(1, 2)
    critical_q = F(1, 2)
    term1 = F(16, 17)
    term2 = ambient - critical_q * F(1, 6)
    term3 = F(7, 8) + critical_q * F(1, 8)
    best = max(term1, term2, term3)
    required_pointwise = F(1, 2)
    local_variance = window + F(2) * best
    target_variance = ambient + window
    major_variance = F(2)
    return BasakRoblesZaharescuMobiusConvolutionAudit(
        ambient_length_exponent=ambient,
        short_window_exponent=window,
        critical_denominator_exponent=critical_q,
        first_pointwise_term_exponent=term1,
        second_pointwise_term_exponent=term2,
        third_pointwise_term_exponent=term3,
        best_published_pointwise_exponent=best,
        required_pointwise_exponent=required_pointwise,
        pointwise_exponent_deficit=best - required_pointwise,
        direct_local_arc_variance_exponent=local_variance,
        required_local_variance_exponent=target_variance,
        local_arc_variance_deficit=local_variance - target_variance,
        major_arc_direct_variance_exponent=major_variance,
        major_arc_power_deficit=major_variance - target_variance,
        published_full_mobius_convolution_pointwise_bound=True,
        published_ratio_twisted_family_bound=False,
        published_local_l2_bound=False,
        brz_direct_pointwise_route_closes_variance_gate=False,
    )


def inverse_zeta_variance_zero_free_audit(
) -> InverseZetaVarianceZeroFreeAudit:
    """Record the zero-free consequence of the strong sufficient gate.

    Integrating a smoothed short sum over its center ``x`` contributes
    exactly ``H * integral(phi)`` per coefficient.  Cauchy applied to a
    variance bound ``X H`` over an ``x``-interval of length ``X`` gives
    a dyadic coefficient sum of size ``X / sqrt(H)``.  At
    ``H=sqrt(X)`` this is ``X^(3/4)``.  Smooth dyadic summation, including
    any fixed vertical twist in the test weight, then continues
    ``sum (mu*mu)(n)n^(-s)=1/zeta(s)^2`` holomorphically to
    ``Re(s)>3/4``.  This is a consequence of the sufficient variance
    gate, not a claimed consequence of the original MWKF asymptotic.
    """
    ambient = F(1)
    window = F(1, 2)
    variance = ambient + window
    block = ambient - window / 2
    return InverseZetaVarianceZeroFreeAudit(
        ambient_length_exponent=ambient,
        short_window_exponent=window,
        variance_bound_exponent=variance,
        dyadic_coefficient_block_exponent=block,
        implied_dyadic_convergence_abscissa=block,
        x_integration_identity_exact=True,
        cauchy_schwarz_exponent_exact=True,
        dyadic_continuation_argument_exact=True,
        implies_zeta_zero_free_real_part_gt_three_quarters=True,
        original_mwkf_asymptotic_requires_this_gate=False,
        inverse_zeta_variance_gate_available_unconditionally=False,
    )


def bblr_h_poisson_inverse_removal(
    *,
    m: int,
    n: int,
    ell: int,
    dual_frequency: int,
) -> dict[str, int | bool]:
    """Check the exact inverse removal after Poisson summation in ``h``.

    For ``r = inverse(m) mod n`` and ``j = k*n + ell*r``, the inverse
    phase condition ``j == ell*r (mod n)`` is equivalent to the linear
    congruence ``m*j == ell (mod n)``.  The integer ``k`` parametrizes
    every representative of the first congruence exactly once.
    """
    if min(m, n) <= 0:
        raise ValueError("m and n must be positive")
    if gcd(m, n) != 1:
        raise ValueError("m and n must be coprime")
    inverse = pow(m, -1, n)
    numerator = dual_frequency * n + ell * inverse
    inverse_phase = (ell * inverse) % n
    linear_left = (m * numerator) % n
    linear_right = ell % n
    return {
        "inverse_residue": inverse,
        "poisson_numerator": numerator,
        "poisson_residue": numerator % n,
        "inverse_phase_congruence": inverse_phase,
        "linear_congruence_left": linear_left,
        "linear_congruence_right": linear_right,
        "inverse_removed_exactly": (
            numerator % n == inverse_phase
            and linear_left == linear_right
        ),
    }


def bblr_h_poisson_unsigned_hard_box_audit(
) -> BBLRHPoissonUnsignedHardBoxAudit:
    """Close the power ledger of BBLR's all-unsigned ``d=1`` box.

    In the forced box ``A=B=1`` and ``M_i=N_i=H=T``.  A second
    Poisson summation in ``h`` changes the Kloosterman inverse into
    ``m*j == ell (mod n)``.  The two transform variables have rapidly
    decaying weights.  For fixed nonzero ``j``, the number of ``m`` in
    a length-``T`` interval is bounded by ``O((j,n))`` and
    ``sum_(n~T) (j,n) <= T*tau(|j|)+sigma(|j|)``.  Hence the inner
    transformed count is ``T`` and the outside Poisson factor is ``T``.
    When the original gcd layer has positive exponent, the remaining
    Fourier transform has physical length ``d`` and every nonzero
    ``ell`` is power-negligible by repeated integration by parts.
    """
    old = F(5, 2)
    new = F(2)
    target = F(2)
    return BBLRHPoissonUnsignedHardBoxAudit(
        old_weil_bound_exponent=old,
        h_poisson_bound_exponent=new,
        local_target_exponent=target,
        recovered_power_saving=old - new,
        h_length_matches_reduced_modulus=True,
        h_poisson_identity_exact=True,
        inverse_fraction_becomes_linear_congruence=True,
        weighted_gcd_sum_is_diagonal_scale=True,
        positive_gcd_layers_are_power_negligible=True,
        approximation_error_exponent=F(2),
        all_unsigned_hard_box_power_closed=True,
        global_logarithmic_little_o_closed=False,
        whole_signed_hard_face_covered=False,
    )


def bblr_h_poisson_signed_cell_audit(
    *,
    outer_scale_exponent: Fraction,
) -> BBLRHPoissonSignedCellAudit:
    """Audit the second-BBLR ledger on one signed outer-scale cell.

    Put ``A=B=T^s`` after reducing dyadic cross terms to diagonal norms.
    The first BBLR step followed by Poisson summation in ``h`` gives the
    exact transformed equation ``a*m*j - b*n*k = ell`` at scales

    ``a,b=T^s``, ``m,n=T^(1-s/2)``, ``j,k=T^(s/2)``, ``ell=T^s``.

    BBLR Proposition 3.1 is sharp here: its transformed shift equals
    ``sqrt(A*B)``.  Its two error terms, after restoring the first
    h-Poisson prefactor ``T^(1-s)``, have exponents ``3/2+2s`` and
    ``7/4+s``.  Both are below the global exponent two exactly when
    ``s<1/4``.  The endpoint has no logarithmic little-oh in the cited
    estimate, so it remains residual.
    """
    s = outer_scale_exponent
    if s < 0 or s > 1:
        raise ValueError("outer_scale_exponent must lie in [0, 1]")

    large_inner = F(1) - s / 2
    small_inner = s / 2
    shift = s
    side_product = F(1) + s
    raw_count = F(1) + 2 * s
    required_bound = F(1) + s
    prefactor = F(1) - s
    first_total_error = F(3, 2) + 2 * s
    second_total_error = F(7, 4) + s
    target = F(2)
    margin = min(
        target - first_total_error,
        target - second_total_error,
    )
    published_upper = F(1, 4)

    return BBLRHPoissonSignedCellAudit(
        outer_scale_exponent=s,
        large_inner_factor_exponent=large_inner,
        small_inner_factor_exponent=small_inner,
        transformed_shift_exponent=shift,
        transformed_side_product_exponent=side_product,
        transformed_raw_count_exponent=raw_count,
        transformed_required_bound_exponent=required_bound,
        required_outer_mobius_saving=raw_count - required_bound,
        h_poisson_prefactor_exponent=prefactor,
        first_total_bblr_error_exponent=first_total_error,
        second_total_bblr_error_exponent=second_total_error,
        global_target_exponent=target,
        power_margin=margin,
        dyadic_cross_terms_reduce_to_diagonal_norms=True,
        transformed_bblr_sharp_condition_holds=(shift == s),
        published_bblr_power_covers_cell=(s < published_upper),
        boundary_logarithmic_little_o_closed=False,
        published_bblr_power_coverage_upper=published_upper,
        signed_residual_lower_exponent=published_upper,
        signed_residual_upper_exponent=F(1),
        whole_signed_hard_face_covered=False,
    )


def truncated_signed_dual_convolution_identity(
    *,
    cutoff: int,
    cofactor: int,
    product: int,
) -> dict[str, int | bool]:
    """Verify the finite signed-atom/dual convolution collapse.

    For fixed unsigned cofactor ``e``, define

    ``lambda_e(u) = -sum_(d*y=u, d<=U<d*e) mu(d)mu(y)``.

    Convolution with the unsigned h-Poisson dual variable ``j`` is
    exact:

    ``sum_(u*j=c) lambda_e(u) = -mu(c) 1_(c<=U<c*e)``.

    Indeed, after writing ``u=d*y``, the inner sum over ``y*j=c/d``
    is ``(mu*1)(c/d)`` and vanishes unless ``d=c``.  This is a finite
    reindexing; no analytic estimate or asymptotic is used.
    """
    if min(cutoff, cofactor, product) <= 0:
        raise ValueError("cutoff, cofactor, and product must be positive")

    def divisors(n: int) -> tuple[int, ...]:
        return tuple(d for d in range(1, n + 1) if n % d == 0)

    def signed_atom_coefficient(u: int) -> int:
        return -sum(
            _finite_mobius(d) * _finite_mobius(u // d)
            for d in divisors(u)
            if d <= cutoff < d * cofactor
        )

    convolution = sum(
        signed_atom_coefficient(product // dual)
        for dual in divisors(product)
    )
    collapsed = (
        -_finite_mobius(product)
        if product <= cutoff < product * cofactor
        else 0
    )
    return {
        "cutoff": cutoff,
        "cofactor": cofactor,
        "product": product,
        "weighted_convolution": convolution,
        "collapsed_value": collapsed,
        "finite_reindexing_exact": convolution == collapsed,
    }


def signed_dual_convolution_audit(
    *,
    outer_atom_exponent: Fraction,
) -> SignedDualConvolutionAudit:
    """Record what the exact finite collapse does and does not prove.

    On a diagonal signed cell, one of the two signed-atom products and
    the second h-Poisson dual both have exponent ``s/2``.  Their product
    has exponent ``s``.  The finite identity above collapses the two
    Möbius atoms to one Möbius coefficient only when the remaining test
    weight depends on ``u`` and ``j`` through ``u*j``.  The actual BBLR
    transform depends on them separately, so a coupled ratio-Mellin
    estimate is still required.
    """
    atom = outer_atom_exponent
    if atom < 0 or atom > F(1, 2):
        raise ValueError("outer_atom_exponent must lie in [0, 1/2]")
    return SignedDualConvolutionAudit(
        outer_atom_exponent=atom,
        h_poisson_dual_exponent=atom,
        product_variable_exponent=2 * atom,
        signed_atom_count=2,
        signed_dual_product_collapse_exact=True,
        collapsed_coefficient_is_one_mobius=True,
        cutoff_condition_retained_exactly=True,
        actual_transformed_weight_product_compatible=False,
        ratio_mellin_family_required=True,
        weighted_collapse_bound_proved=False,
        whole_signed_hard_face_covered=False,
    )


def coupled_ratio_mellin_type_ii_gate_audit(
    *,
    outer_scale_exponent: Fraction,
) -> CoupledRatioMellinTypeIIGateAudit:
    """Normalize the collapsed signed determinant model at scale ``s``.

    After the exact finite collapse and ratio-Mellin separation, the
    determinant has variables ``x,y=T`` and ``c,d=T^s`` with
    ``x*c-y*d=ell`` and ``ell=T^s``.  Its raw shifted count is
    ``T^(1+2s)`` and the required bound is ``T^(1+s)``.  Thus the two
    collapsed coefficient variables must jointly save exactly ``T^s``.

    The congruence modulus ``c=T^s`` lies at level ``s/(1+s)<=1/2``
    relative to the convolution length ``y*d=T^(1+s)``.  Ordinary
    Bombieri--Vinogradov still does not apply to the actual form because
    the quotient ``x=(y*d+ell)/c`` carries another Möbius coefficient,
    and summing fixed-shift absolute bounds loses the whole ``T^s``
    shift range.  In the actual primitive layer, ``gcd(X,Y)=1`` still
    depends on the pre-collapse divisors.  A prime-allocation expansion
    is required before this four-variable model becomes an exact gate.
    """
    s = outer_scale_exponent
    if s < 0 or s > 1:
        raise ValueError("outer_scale_exponent must lie in [0, 1]")
    ambient = F(1) + s
    raw = F(1) + 2 * s
    target = ambient
    required = raw - target
    square_root = s
    level = s / ambient
    return CoupledRatioMellinTypeIIGateAudit(
        outer_scale_exponent=s,
        long_mobius_variable_exponent=F(1),
        collapsed_product_variable_exponent=s,
        shift_exponent=s,
        convolution_ambient_exponent=ambient,
        progression_modulus_exponent=s,
        modulus_level_relative_to_ambient=level,
        raw_shifted_count_exponent=raw,
        required_inner_bound_exponent=target,
        required_cancellation_exponent=required,
        two_collapsed_coefficients_square_root_saving=square_root,
        square_root_power_margin=square_root - required,
        modulus_within_bombieri_vinogradov_level=(2 * s <= ambient),
        fixed_shift_dispersion_suffices_after_shift_sum=False,
        quotient_mobius_prevents_direct_bv=True,
        full_shift_average_must_remain_coupled=True,
        coprimality_prime_allocation_required=True,
        four_variable_reduction_exact=False,
        coupled_ratio_mellin_type_ii_bound_proved=False,
        whole_signed_hard_face_covered=False,
    )


def collapsed_cross_coprimality_identity(
    *,
    x: int,
    u: int,
    y: int,
    v: int,
) -> dict[str, int | bool]:
    """Expand ``gcd(x*u,y*v)=1`` into four finite Möbius sums.

    The product gcd is one exactly when the four cross gcds
    ``(x,y)``, ``(x,v)``, ``(u,y)``, and ``(u,v)`` are one.  Applying
    ``1_(gcd(a,b)=1)=sum_(r|a,r|b) mu(r)`` to each pair gives an exact
    four-divisor allocation, even when primes occur in several pairs.
    """
    if min(x, u, y, v) <= 0:
        raise ValueError("product factors must be positive")

    cross_gcds = (
        gcd(x, y),
        gcd(x, v),
        gcd(u, y),
        gcd(u, v),
    )

    def mobius_gcd_indicator(common: int) -> int:
        return sum(
            _finite_mobius(divisor)
            for divisor in range(1, common + 1)
            if common % divisor == 0
        )

    primitive = int(gcd(x * u, y * v) == 1)
    cross_indicator = int(all(common == 1 for common in cross_gcds))
    allocation = 1
    for common in cross_gcds:
        allocation *= mobius_gcd_indicator(common)
    return {
        "primitive_product_indicator": primitive,
        "cross_coprimality_indicator": cross_indicator,
        "allocation_value": allocation,
        "four_cross_conditions_equivalent": primitive == cross_indicator,
        "mobius_allocation_identity_exact": primitive == allocation,
    }


def collapsed_coprimality_allocation_audit(
) -> CollapsedCoprimalityAllocationAudit:
    """Record the exact gcd allocation and the dependence it retains.

    Four finite Möbius inversions make the collapsed determinant an
    exact superposition.  For fixed allocation divisors, their
    restrictions separate between ``x``, ``y``, ``u``, and ``v``; the
    collapsed ``c,d`` coefficients are therefore independent of the
    long variables.  Exactness and coefficient separation are restored,
    but the quotient Möbius weight and coupled shift average still keep
    a standard Bombieri--Vinogradov theorem from being an adapter.
    """
    return CollapsedCoprimalityAllocationAudit(
        cross_coprimality_condition_count=4,
        mobius_allocation_divisor_count=4,
        product_gcd_factorization_exact=True,
        allocation_is_finite_reindexing=True,
        positive_power_loss_exponent=F(0),
        registered_logarithmic_loss=F(4),
        four_variable_superposition_exact=True,
        collapsed_coefficients_independent_of_long_variables=True,
        standard_bombieri_vinogradov_adapter_applies=False,
        coupled_ratio_mellin_type_ii_bound_proved=False,
        whole_signed_hard_face_covered=False,
    )


def collapsed_equal_product_chowla_identity(
    *,
    x: int,
    y: int,
    u: int,
    v: int,
    j: int,
    k: int,
) -> dict[str, int | bool]:
    """Exhibit the fixed-shift face inside the primitive collapsed model.

    Put ``c=u*j`` and ``d=v*k``.  When ``c=d`` the determinant equation
    ``x*c-y*d=ell`` becomes ``ell=(x-y)c``.  The primitive condition in
    the BBLR layer is ``gcd(x*u,y*v)=1``; it need not exclude this face.
    """
    if min(x, y, u, v, j, k) <= 0:
        raise ValueError("collapsed determinant factors must be positive")
    c = u * j
    d = v * k
    shift = x - y
    determinant = x * c - y * d
    equal_face = c == d
    expected = shift * c
    primitive = gcd(x * u, y * v) == 1
    return {
        "collapsed_left_product": c,
        "collapsed_right_product": d,
        "collapsed_products_equal": equal_face,
        "fixed_shift": shift,
        "determinant": determinant,
        "expected_equal_face_determinant": expected,
        "determinant_equals_collapsed_product": (
            equal_face and shift == 1 and determinant == c
        ),
        "primitive_product_condition_holds": primitive,
        "primitive_condition_does_not_exclude_face": equal_face and primitive,
    }


def collapsed_chowla_face_audit(
    *,
    outer_scale_exponent: Fraction,
) -> CollapsedChowlaFaceAudit:
    """Record the equal-product boundary of the coupled Type-II gate.

    At ``c=d`` and ``ell=k*c`` the long variables satisfy ``x-y=k``.
    At zero ratio frequency the exact collapsed coefficient is a single
    Möbius value, so the equal face contains an ordinary two-point
    Möbius correlation.  Its count already has the target exponent
    ``1+s``: no positive-power saving is missing, but a logarithmic
    little-oh is.  Consequently a pointwise-in-ratio-frequency triangle
    inequality would demand an unavailable ordinary Chowla estimate.
    This does not reject the original jointly integrated ratio-Mellin
    gate, where cancellation between the two frequencies is retained.
    """
    s = outer_scale_exponent
    if s < 0 or s > 1:
        raise ValueError("outer_scale_exponent must lie in [0, 1]")
    face = F(1) + s
    return CollapsedChowlaFaceAudit(
        outer_scale_exponent=s,
        long_mobius_variable_exponent=F(1),
        collapsed_product_variable_exponent=s,
        equal_face_raw_exponent=face,
        required_inner_bound_exponent=face,
        positive_power_margin=F(0),
        equal_collapsed_product_face_present=True,
        determinant_reduces_to_fixed_shift=True,
        primitive_gcd_excludes_face=False,
        pointwise_zero_ratio_coefficient_is_mobius=True,
        face_contains_two_point_chowla=True,
        ordinary_two_point_chowla_available_unconditionally=False,
        logarithmic_little_o_required=True,
        uniform_ratio_frequency_triangle_gate_admissible=False,
        joint_ratio_integral_must_remain_coupled=True,
        coupled_ratio_mellin_type_ii_bound_proved=False,
        whole_signed_hard_face_covered=False,
    )


def primitive_equal_face_divisor_coefficient(
    *,
    cutoff: int,
    left_cofactor: int,
    right_cofactor: int,
    collapsed_product: int,
    x: int,
    y: int,
    allowed_left_factors: tuple[int, ...],
    allowed_right_factors: tuple[int, ...],
) -> dict[str, int | bool | tuple[tuple[int, int], ...]]:
    """Recombine the two physical divisor kernels on ``c=d``.

    The hidden factors ``u,v`` retain the primitive restrictions
    ``(u,v)=(u,y)=(v,x)=1``.  The allowed-factor tuples model a fixed
    pair of smooth dyadic boxes; the complementary dual factors are
    forced to be ``j=c/u`` and ``k=c/v``.  This finite sum checks
    whether physical ratio-Mellin inversion itself kills the equal
    collapsed-product face.
    """
    if min(
        cutoff,
        left_cofactor,
        right_cofactor,
        collapsed_product,
        x,
        y,
    ) <= 0:
        raise ValueError(
            "cutoffs, factors, products, and long variables must be positive"
        )

    def divisors(n: int) -> tuple[int, ...]:
        return tuple(d for d in range(1, n + 1) if n % d == 0)

    def signed_atom(u: int, cofactor: int) -> int:
        return -sum(
            _finite_mobius(d) * _finite_mobius(u // d)
            for d in divisors(u)
            if d <= cutoff < d * cofactor
        )

    left = set(allowed_left_factors)
    right = set(allowed_right_factors)
    terms: list[tuple[int, int, int]] = []
    for u in divisors(collapsed_product):
        if u not in left:
            continue
        for v in divisors(collapsed_product):
            if v not in right:
                continue
            if gcd(u, v) != 1 or gcd(u, y) != 1 or gcd(v, x) != 1:
                continue
            value = signed_atom(u, left_cofactor) * signed_atom(
                v,
                right_cofactor,
            )
            if value:
                terms.append((u, v, value))
    coefficient = sum(value for _, _, value in terms)
    pairs = tuple((u, v) for u, v, _ in terms)
    return {
        "fixed_shift": x - y,
        "coefficient": coefficient,
        "contributing_factor_pairs": pairs,
        "primitive_terms_only": all(
            gcd(u, v) == gcd(u, y) == gcd(v, x) == 1
            for u, v, _ in terms
        ),
        "nonzero_primitive_equal_face_coefficient": coefficient != 0,
    }


def physical_joint_ratio_recombination_audit(
) -> PhysicalJointRatioRecombinationAudit:
    """Record the exact physical-kernel obstruction after Mellin inversion.

    Recombining the two ratio integrals restores a finite sum over the
    hidden divisor factors.  The primitive restrictions couple those
    factors, but the coupled coefficient need not vanish: the exact
    fixture ``U=5, e=e'=10, c=35, x=12, y=11`` and balanced factors
    ``u,v in {5,7}`` has coefficient four.  Thus neither joint Mellin
    inversion nor primitive gcd recombination universally removes the
    fixed-shift face.  A proof must use the exact sum over all outer
    scales and the inherited kernel, rather than enlarge it to arbitrary
    smooth tensors and estimate allocation cells separately.
    """
    witness = primitive_equal_face_divisor_coefficient(
        cutoff=5,
        left_cofactor=10,
        right_cofactor=10,
        collapsed_product=35,
        x=12,
        y=11,
        allowed_left_factors=(5, 7),
        allowed_right_factors=(5, 7),
    )
    coefficient = int(witness["coefficient"])
    if coefficient != 4:
        raise AssertionError("primitive equal-face witness changed")
    return PhysicalJointRatioRecombinationAudit(
        ratio_mellin_recombines_to_finite_divisor_kernel=True,
        primitive_equal_face_coefficient_can_be_nonzero=True,
        witness_equal_face_coefficient=coefficient,
        joint_ratio_integration_alone_annihilates_chowla_face=False,
        arbitrary_smooth_weight_enlargement_admissible=False,
        allocationwise_triangle_inequality_admissible=False,
        equal_face_separate_bound_available_unconditionally=False,
        full_outer_scale_and_kernel_sum_must_remain_coupled=True,
        centered_coupled_dispersion_bound_proved=False,
        whole_signed_hard_face_covered=False,
    )


def collapsed_gcd_layer_parameterization(
    *,
    c: int,
    d: int,
    shift: int,
    x: int,
    y: int,
) -> dict[str, int | bool]:
    """Extract the exact primitive determinant after ``gcd(c,d)``.

    The original equation ``c*x-d*y=shift`` can hold only when the
    common gcd divides ``shift``.  On that support, writing
    ``c=g*a``, ``d=g*b``, and ``shift=g*h`` gives the equivalent
    primitive equation ``a*x-b*y=h`` with ``gcd(a,b)=1``.
    """
    if min(c, d, x, y) <= 0:
        raise ValueError("c, d, x, and y must be positive")
    common = gcd(c, d)
    if shift == 0 or shift % common != 0:
        raise ValueError("the nonzero shift must be divisible by gcd(c,d)")
    left = c // common
    right = d // common
    primitive_shift = shift // common
    original_determinant = c * x - d * y
    primitive_determinant = left * x - right * y
    return {
        "common_gcd": common,
        "primitive_left": left,
        "primitive_right": right,
        "primitive_shift": primitive_shift,
        "primitive_coprime": gcd(left, right) == 1,
        "original_determinant": original_determinant,
        "primitive_determinant": primitive_determinant,
        "equation_equivalent": (
            original_determinant == common * primitive_determinant
            and (original_determinant == shift)
            == (primitive_determinant == primitive_shift)
        ),
    }


def collapsed_gcd_layer_centered_kernel_audit(
    *,
    collapsed_exponent: Fraction,
    gcd_exponent: Fraction,
) -> CollapsedGcdLayerCenteredKernelAudit:
    """Record the exact power ledger after the collapsed gcd split.

    Put ``C=T^s``, ``G=T^gamma``, and ``A=C/G``.  A dyadic gcd layer
    has raw cardinal exponent ``1+2*s-gamma``.  The global inner target
    is ``1+s``, so the precise required saving is ``s-gamma``.  Fourier
    inversion of a nonzero-shift weight contributes the outside factor
    ``A``; its coupled inner integral must therefore have exponent at
    most ``1+gamma``.

    The inherited outer-scale and ratio kernels remain inside the sum.
    No pointwise affine-Chowla estimate or published averaged-Chowla
    adapter is asserted.
    """
    s = Fraction(collapsed_exponent)
    gamma = Fraction(gcd_exponent)
    if s < 0 or s > 1:
        raise ValueError("collapsed_exponent must lie in [0,1]")
    if gamma < 0 or gamma > s:
        raise ValueError("gcd_exponent must lie in [0, collapsed_exponent]")
    cofactor = s - gamma
    raw = 1 + 2 * s - gamma
    target = 1 + s
    top = cofactor == 0
    return CollapsedGcdLayerCenteredKernelAudit(
        collapsed_exponent=s,
        gcd_exponent=gamma,
        cofactor_exponent=cofactor,
        product_length_exponent=1 + cofactor,
        primitive_shift_exponent=cofactor,
        raw_dyadic_layer_exponent=raw,
        global_target_exponent=target,
        required_saving_exponent=raw - target,
        fourier_inner_target_exponent=target - cofactor,
        shift_weight_vanishes_near_zero=True,
        product_diagonal_annihilated_exactly=True,
        constant_fourier_mode_centered_exactly=True,
        full_g_sum_retained=True,
        full_allocation_and_ratio_sum_retained=True,
        top_equal_product_face=top,
        fixed_affine_chowla_must_remain_inside_g_sum=top,
        pointwise_fixed_affine_chowla_bound_assumed=False,
        published_averaged_chowla_adapter_applies=False,
        centered_coupled_dispersion_bound_proved=False,
        whole_signed_hard_face_covered=False,
    )


def primitive_equal_product_factorization(
    *,
    u: int,
    v: int,
    j: int,
    k: int,
) -> dict[str, int | bool]:
    """Parameterize ``u*j=v*k`` when ``gcd(u,v)=1``.

    Euclid's lemma gives the unique positive integer ``q`` with
    ``j=v*q`` and ``k=u*q``.  The helper records the exact finite
    identity used on the primitive equal-product face.
    """
    if min(u, v, j, k) <= 0:
        raise ValueError("u, v, j, and k must be positive")
    primitive = gcd(u, v) == 1
    equal = u * j == v * k
    quotient = j // v if primitive and equal and j % v == 0 else 0
    j_identity = quotient > 0 and j == v * quotient
    k_identity = quotient > 0 and k == u * quotient
    return {
        "primitive_coprime": primitive,
        "equal_product": equal,
        "quotient": quotient,
        "j_equals_vq": j_identity,
        "k_equals_uq": k_identity,
        "collapsed_product": u * j,
        "factorization_exact": (
            primitive and equal and j_identity and k_identity
        ),
    }


def truncated_signed_atom_interval_convolution(
    *,
    cutoff: int,
    cofactor: int,
    atom: int,
) -> dict[str, int | bool]:
    """Check ``lambda_(U,e)=-(mu 1_(U/e<d<=U))*mu`` finitely."""
    if min(cutoff, cofactor, atom) <= 0:
        raise ValueError("cutoff, cofactor, and atom must be positive")
    divisors = tuple(d for d in range(1, atom + 1) if atom % d == 0)
    direct = -sum(
        _finite_mobius(d) * _finite_mobius(atom // d)
        for d in divisors
        if d <= cutoff < d * cofactor
    )
    interval = -sum(
        _finite_mobius(d) * _finite_mobius(atom // d)
        for d in divisors
        if d <= cutoff and cutoff < d * cofactor
    )
    return {
        "cutoff": cutoff,
        "cofactor": cofactor,
        "atom": atom,
        "lower_strict_numerator": cutoff,
        "lower_strict_denominator": cofactor,
        "direct_coefficient": direct,
        "interval_convolution": interval,
        "interval_convolution_exact": direct == interval,
    }


def top_equal_product_outer_pnt_audit() -> TopEqualProductOuterPntAudit:
    """Close the balanced primitive equal-product face by outer PNT.

    At ``s=1`` the signed atom, its unsigned cofactor, and the second
    Poisson dual all have scale ``T^(1/2)`` under the exact half cutoff.
    Primitive equality gives ``j=v*q`` and ``k=u*q`` with bounded ``q``.
    The signed coefficient is a truncated ``mu*mu`` convolution.  After
    writing it as the full convolution minus the bounded lower and upper
    tails, the classical zero-free region gives arbitrary logarithmic
    saving in a smooth ``u``-sum, uniformly under a coprimality condition;
    the removed Euler factors cost only powers of ``log log``.

    Consequently the long fixed-shift Mobius correlation is used only
    with its trivial length-``T`` bound.  This closes this one face, not
    the remaining ``0<A<T`` centered dispersion layers.
    """
    atom = F(1, 2)
    outer = 2 * atom
    long = F(1)
    raw = outer + long
    target = F(2)
    return TopEqualProductOuterPntAudit(
        signed_atom_exponent=atom,
        poisson_quotient_exponent=F(0),
        outer_pair_raw_exponent=outer,
        long_correlation_trivial_exponent=long,
        face_raw_exponent=raw,
        face_target_exponent=target,
        power_margin=target - raw,
        primitive_equal_product_factorization_exact=True,
        signed_atom_interval_convolution_exact=True,
        balanced_cutoff_ratios_verified=True,
        uniform_coprime_pnt_log_saving_available=True,
        coprime_euler_factor_loss_only_polylogarithmic=True,
        long_mobius_correlation_used_only_trivially=True,
        fixed_affine_chowla_estimate_required=False,
        top_equal_product_face_closed_unconditionally=True,
        whole_signed_hard_face_covered=False,
    )


def primitive_unequal_product_factorization(
    *,
    a: int,
    b: int,
    u: int,
    v: int,
    j: int,
    k: int,
) -> dict[str, int | bool]:
    """Refactor ``b*u*j=a*v*k`` under the two primitive conditions."""
    if min(a, b, u, v, j, k) <= 0:
        raise ValueError("a, b, u, v, j, and k must be positive")
    primitive_slopes = gcd(a, b) == 1
    primitive_hidden = gcd(u, v) == 1
    equal = b * u * j == a * v * k
    left_cross = gcd(a, u)
    right_cross = gcd(b, v)
    cross = left_cross * right_cross
    direct_cross = gcd(b * u, a * v)
    cross_identity = (
        primitive_slopes
        and primitive_hidden
        and direct_cross == cross
    )
    reduced_left = (b * u) // direct_cross
    reduced_right = (a * v) // direct_cross
    quotient = (
        j // reduced_right
        if equal and j % reduced_right == 0
        else 0
    )
    j_formula = reduced_right * quotient
    k_formula = reduced_left * quotient
    common_gcd = (
        u * v * quotient // direct_cross
        if quotient > 0 and (u * v * quotient) % direct_cross == 0
        else 0
    )
    left_product = common_gcd * a
    right_product = common_gcd * b
    return {
        "primitive_slopes": primitive_slopes,
        "primitive_hidden_factors": primitive_hidden,
        "equal_weighted_product": equal,
        "left_cross_gcd": left_cross,
        "right_cross_gcd": right_cross,
        "cross_gcd_product": direct_cross,
        "cross_gcd_identity": cross_identity,
        "quotient": quotient,
        "j_formula": j_formula,
        "k_formula": k_formula,
        "common_collapsed_gcd": common_gcd,
        "left_collapsed_product": left_product,
        "right_collapsed_product": right_product,
        "factorization_exact": (
            primitive_slopes
            and primitive_hidden
            and equal
            and cross_identity
            and quotient > 0
            and j == j_formula
            and k == k_formula
            and u * j == left_product
            and v * k == right_product
        ),
    }


def polylog_gcd_collar_outer_pnt_audit(
    *,
    polylog_depth: int,
) -> PolylogGcdCollarOuterPntAudit:
    """Close ``C/G <= log(T)^K`` by the signed-atom PNT.

    The unequal-product factorization introduces only the primitive
    slopes ``a,b``, their two cross gcds, the primitive shift, and the
    quotient ``q``.  If ``A=C/G`` is at most a fixed power of ``log T``,
    all of them have power exponent zero.  The prescribed-divisibility
    version of the coprime signed-atom PNT has arbitrary logarithmic
    saving and absorbs their complete finite sums.  This does not cover
    a cell with ``A=T^delta`` for any fixed positive ``delta``.
    """
    if polylog_depth < 0:
        raise ValueError("polylog_depth must be nonnegative")
    zero = F(0)
    return PolylogGcdCollarOuterPntAudit(
        polylog_depth=polylog_depth,
        cofactor_power_exponent=zero,
        cross_gcd_power_exponent=zero,
        poisson_quotient_power_exponent=zero,
        required_power_saving_exponent=zero,
        primitive_unequal_product_factorization_exact=True,
        cross_gcd_product_identity_exact=True,
        prescribed_divisibility_coprime_pnt_available=True,
        arbitrary_log_saving_absorbs_polylog_variables=True,
        long_affine_mobius_sum_used_only_trivially=True,
        polylog_gcd_collar_closed_unconditionally=True,
        strict_positive_power_gcd_layers_covered=False,
        whole_signed_hard_face_covered=False,
    )


def strict_power_gcd_core_audit(
    *,
    collapsed_exponent: Fraction,
    cofactor_exponent: Fraction,
    quotient_exponent: Fraction,
    left_cross_gcd_exponent: Fraction,
) -> StrictPowerGcdCoreAudit:
    """Normalize the strict-power core after primitive refactorization.

    Write ``C=T^s``, ``A=C/G=T^delta``, ``q=T^theta`` and
    ``d_i=T^r_i``.  The identity ``Delta=d_1*d_2=A*q`` forces
    ``r_1+r_2=delta+theta``.  The reduced unsigned block
    ``(a_0,b_0,q)`` has total exponent exactly ``delta``, which is the
    complete gap between the raw core ``1+s+delta`` and target ``1+s``.
    """
    s = Fraction(collapsed_exponent)
    delta = Fraction(cofactor_exponent)
    theta = Fraction(quotient_exponent)
    r1 = Fraction(left_cross_gcd_exponent)
    if s <= 0 or s > 1:
        raise ValueError("collapsed_exponent must lie in (0,1]")
    if delta <= 0 or delta > s:
        raise ValueError("cofactor_exponent must lie in (0,s]")
    gamma = s - delta
    if theta < 0 or theta > min(delta, gamma):
        raise ValueError("quotient_exponent must lie in [0,min(delta,gamma)]")
    r2 = delta + theta - r1
    ceiling = min(delta, s / 2)
    feasible = 0 <= r1 <= ceiling and 0 <= r2 <= ceiling
    if not feasible:
        raise ValueError("cross-gcd exponents do not lie in the exact polytope")
    left_slope = delta - r1
    right_slope = delta - r2
    left_signed = s / 2 - r1
    right_signed = s / 2 - r2
    unsigned = left_slope + right_slope + theta
    signed = left_signed + right_signed
    reconstructed_gcd = signed + theta
    raw = 1 + s + delta
    target = 1 + s
    required = raw - target
    return StrictPowerGcdCoreAudit(
        collapsed_exponent=s,
        cofactor_exponent=delta,
        gcd_exponent=gamma,
        quotient_exponent=theta,
        left_cross_gcd_exponent=r1,
        right_cross_gcd_exponent=r2,
        left_reduced_slope_exponent=left_slope,
        right_reduced_slope_exponent=right_slope,
        left_reduced_signed_exponent=left_signed,
        right_reduced_signed_exponent=right_signed,
        unsigned_reduced_block_exponent=unsigned,
        signed_reduced_block_exponent=signed,
        reconstructed_gcd_exponent=reconstructed_gcd,
        raw_core_exponent=raw,
        target_core_exponent=target,
        required_saving_exponent=required,
        exponent_polytope_feasible=feasible,
        unsigned_block_equals_full_deficit=unsigned == required,
        all_allocations_and_ratio_integrals_retained=True,
        long_and_collapsed_arithmetic_weights_on_each_side=True,
        bblr_arbitrary_outer_coefficient_adapter_applies=True,
        centered_three_block_type_ii_required=True,
        centered_three_block_type_ii_proved=False,
        whole_signed_hard_face_covered=False,
    )


def strict_power_convolution_kloosterman_audit(
    *,
    collapsed_exponent: Fraction,
    cofactor_exponent: Fraction,
    quotient_exponent: Fraction,
    left_cross_gcd_exponent: Fraction,
) -> StrictPowerConvolutionKloostermanAudit:
    """Audit the first legal convolution of both arithmetic weights.

    For fixed ``u_0`` put

    ``alpha_r = sum_{d_1*x=r} lambda(d_1*u_0) * mu(x)``

    and define ``beta_s`` symmetrically.  These are divisor bounded, so
    they are legal arbitrary outer coefficients in BBLR after the exact
    ratio Mellin separations.  The determinant becomes

    ``r*a_0 - s*b_0 = h``.

    This adapter records the literal BBLR exponents, and then the
    Bettin--Chandee exponents after Poisson summation in ``a_0``.  It
    also distinguishes the original cross diagonal, which centering
    removes, from the positive self diagonal created by Cauchy.
    """
    core = strict_power_gcd_core_audit(
        collapsed_exponent=collapsed_exponent,
        cofactor_exponent=cofactor_exponent,
        quotient_exponent=quotient_exponent,
        left_cross_gcd_exponent=left_cross_gcd_exponent,
    )
    s = core.collapsed_exponent
    delta = core.cofactor_exponent
    gamma = core.gcd_exponent
    theta = core.quotient_exponent
    r1 = core.left_cross_gcd_exponent
    r2 = core.right_cross_gcd_exponent
    r_max = max(r1, r2)

    left_outer = 1 + r1
    right_outer = 1 + r2
    left_slope = delta - r1
    right_slope = delta - r2
    side_product = 1 + delta
    remaining_outer = gamma

    # BBLR Proposition 3.1.  Here ABMN has exponent 2+2*delta,
    # H has exponent delta, and AB has exponent 2+delta+theta.
    bblr_prefactor = F(1, 2) + delta
    bblr_ab = bblr_prefactor + 2 + delta + theta
    bblr_watt = (
        bblr_prefactor
        + delta / 4
        + (1 + r_max) / 2
        + (2 + 2 * delta) / 8
    )
    bblr_target = side_product
    bblr_ab_deficit = bblr_ab - bblr_target
    bblr_watt_deficit = bblr_watt - bblr_target

    # Poisson in a_0 modulo s.  The dual k has length s/a_0,
    # hence exponent 1+theta.  Combining k*h gives the BC numerator.
    poisson_dual = 1 + theta
    poisson_numerator = 1 + delta + theta
    poisson_normalization = -1 - theta

    norm_exponent = (
        left_outer + right_outer + poisson_numerator
    ) / 2
    bc_total_product = (
        left_outer + right_outer + poisson_numerator
    )
    bc_first_before_normalization = (
        norm_exponent
        + F(7, 20) * bc_total_product
        + F(1, 4) * (1 + r_max)
    )
    bc_second_before_normalization = (
        norm_exponent
        + F(3, 8) * bc_total_product
        + F(1, 8) * (poisson_numerator + 1 + r_max)
    )
    bc_first_total = (
        bc_first_before_normalization
        + poisson_normalization
        + remaining_outer
    )
    bc_second_total = (
        bc_second_before_normalization
        + poisson_normalization
        + remaining_outer
    )
    global_target = 1 + s
    bc_first_deficit = bc_first_total - global_target
    bc_second_deficit = bc_second_total - global_target

    # Restoring the outside A from Fourier inversion, identical tuples
    # alone have the first exponent below.  The u_0 and v_0 variables do
    # not enter the additive frequency.  They therefore square coherently
    # inside each grouped Fourier coefficient, taking the full Cauchy
    # diagonal back to the raw exponent 1+s+delta.
    cauchy_tuple_diagonal = 1 + (s + 3 * delta + theta) / 2
    cauchy_grouped_diagonal = core.raw_core_exponent
    cauchy_target = global_target
    cauchy_grouped_deficit = cauchy_grouped_diagonal - cauchy_target
    hard_vertex = (
        s == 1
        and delta == 1
        and theta == 0
        and r1 == F(1, 2)
        and r2 == F(1, 2)
    )

    return StrictPowerConvolutionKloostermanAudit(
        collapsed_exponent=s,
        cofactor_exponent=delta,
        gcd_exponent=gamma,
        quotient_exponent=theta,
        left_cross_gcd_exponent=r1,
        right_cross_gcd_exponent=r2,
        left_convolved_outer_exponent=left_outer,
        right_convolved_outer_exponent=right_outer,
        left_inner_slope_exponent=left_slope,
        right_inner_slope_exponent=right_slope,
        side_product_exponent=side_product,
        remaining_outer_exponent=remaining_outer,
        bblr_convolution_hypotheses_verified=True,
        bblr_ab_error_exponent=bblr_ab,
        bblr_watt_error_exponent=bblr_watt,
        bblr_inner_target_exponent=bblr_target,
        bblr_ab_deficit=bblr_ab_deficit,
        bblr_watt_deficit=bblr_watt_deficit,
        bblr_convolution_route_covered=(
            bblr_ab_deficit < 0 and bblr_watt_deficit < 0
        ),
        poisson_dual_exponent=poisson_dual,
        poisson_numerator_exponent=poisson_numerator,
        poisson_normalization_exponent=poisson_normalization,
        bc_poisson_hypotheses_verified=True,
        bc_first_total_exponent=bc_first_total,
        bc_second_total_exponent=bc_second_total,
        bc_first_deficit=bc_first_deficit,
        bc_second_deficit=bc_second_deficit,
        bc_poisson_route_covered=(
            bc_first_deficit < 0 and bc_second_deficit < 0
        ),
        original_cross_diagonal_removed_by_centering=True,
        cauchy_tuple_diagonal_exponent=cauchy_tuple_diagonal,
        cauchy_grouped_diagonal_exponent=cauchy_grouped_diagonal,
        cauchy_diagonal_target_exponent=cauchy_target,
        cauchy_grouped_diagonal_deficit=cauchy_grouped_deficit,
        cauchy_grouped_diagonal_is_raw_scale=(
            cauchy_grouped_diagonal == core.raw_core_exponent
        ),
        cauchy_grouped_diagonal_killed_by_centering=False,
        hard_vertex_inverse_zeta_square_variance=hard_vertex,
        near_frequency_type_ii_proved=False,
    )


def strict_power_ratio_mellin_bandwidth_audit(
    *,
    collapsed_exponent: Fraction,
    cofactor_exponent: Fraction,
    quotient_exponent: Fraction,
    left_cross_gcd_exponent: Fraction,
) -> StrictPowerRatioMellinBandwidthAudit:
    """Audit whether the inherited ratio kernel supplies power bandwidth.

    On the exact AFE core, with ``z=Delta/(m*r)``, the height phase obeys

    ``d/d(log r) [t*log(1+z)] = -t*z/(1+z)``.

    The retained shift condition gives ``|t*z| <= log(T)^B``.  Every
    higher logarithmic derivative has the same power exponent zero.
    The normalized dyadic ratio weights also have exponent-zero
    derivatives, so their Mellin transforms are rapidly decreasing once
    the Mellin frequency has any fixed positive power of ``T``.

    Resolving adjacent integers in a hidden fibre of length ``T^alpha``
    would require Mellin frequency ``T^alpha``.  Thus the ratio integral
    cannot de-cohere a positive-power hidden fibre.  If both fibres have
    exponent zero there is nothing to resolve, but the independent
    Cauchy deficit ``delta`` remains.
    """
    core = strict_power_gcd_core_audit(
        collapsed_exponent=collapsed_exponent,
        cofactor_exponent=cofactor_exponent,
        quotient_exponent=quotient_exponent,
        left_cross_gcd_exponent=left_cross_gcd_exponent,
    )
    left_hidden = core.left_reduced_signed_exponent
    right_hidden = core.right_reduced_signed_exponent
    hidden_total = left_hidden + right_hidden
    zero = F(0)
    no_positive_hidden_fibre = hidden_total == zero
    return StrictPowerRatioMellinBandwidthAudit(
        collapsed_exponent=core.collapsed_exponent,
        cofactor_exponent=core.cofactor_exponent,
        quotient_exponent=core.quotient_exponent,
        left_cross_gcd_exponent=core.left_cross_gcd_exponent,
        right_cross_gcd_exponent=core.right_cross_gcd_exponent,
        left_hidden_fibre_exponent=left_hidden,
        right_hidden_fibre_exponent=right_hidden,
        total_hidden_fibre_exponent=hidden_total,
        height_phase_log_derivative_power_exponent=zero,
        ratio_weight_log_derivative_power_exponent=zero,
        effective_mellin_frequency_power_exponent=zero,
        left_adjacent_resolution_frequency_exponent=left_hidden,
        right_adjacent_resolution_frequency_exponent=right_hidden,
        remaining_cauchy_deficit_exponent=core.required_saving_exponent,
        mellin_power_tail_is_rapid=True,
        scaled_T_tau_not_independent_bandwidth=True,
        height_phase_creates_second_power_coordinate=False,
        ratio_mellin_resolves_positive_hidden_fibres=(
            no_positive_hidden_fibre
        ),
        ratio_mellin_supplies_required_delta_saving=False,
        pre_cauchy_joint_kernel_still_required=True,
    )


def strict_power_double_poisson_resonance_audit(
    *,
    collapsed_exponent: Fraction,
    cofactor_exponent: Fraction,
    quotient_exponent: Fraction,
    left_cross_gcd_exponent: Fraction,
) -> StrictPowerDoublePoissonResonanceAudit:
    """Audit simultaneous Poisson summation in both reduced slopes.

    For the centered line ``r*a_0-t*b_0=h``, write the Fourier variable
    as ``eta/H`` with ``H=T^delta``.  Poisson summation localizes

    ``k = eta*r/H + O(A_0^-1)`` and
    ``l = eta*t/H + O(B_0^-1)``.

    Since ``r*A_0`` and ``t*B_0`` both have exponent ``1+delta``, the
    two transformed bumps overlap on an eta interval of exponent ``-1``.
    Clearing denominators gives the exact integer resonance coordinate

    ``n=k*t-l*r`` with ``|n| <= T^(1+theta)``.

    Taking absolute values on this transformed side loses
    ``T^(1-delta+theta)`` relative to the original inner cardinality.
    The route is therefore useful only if the signed resonance family is
    estimated before Cauchy or an absolute tuple sum.
    """
    core = strict_power_gcd_core_audit(
        collapsed_exponent=collapsed_exponent,
        cofactor_exponent=cofactor_exponent,
        quotient_exponent=quotient_exponent,
        left_cross_gcd_exponent=left_cross_gcd_exponent,
    )
    s = core.collapsed_exponent
    delta = core.cofactor_exponent
    gamma = core.gcd_exponent
    theta = core.quotient_exponent
    r1 = core.left_cross_gcd_exponent
    r2 = core.right_cross_gcd_exponent
    left_slope = core.left_reduced_slope_exponent
    right_slope = core.right_reduced_slope_exponent
    left_modulus = 1 + r1
    right_modulus = 1 + r2
    left_dual = left_modulus - delta
    right_dual = right_modulus - delta
    dual_product = left_dual + right_modulus
    resonance_shift = 1 + theta
    poisson_amplitude = left_slope + right_slope
    overlap_integral = F(-1)

    # The d_1,d_2,k,l,r,t tuple count, the two Poisson amplitudes, and
    # the common eta-overlap width combine to the following exponent.
    transformed_inner = 2 + delta + theta
    original_inner = 1 + 2 * delta
    transform_loss = transformed_inner - original_inner
    transformed_global = transformed_inner + gamma
    target = 1 + s
    required = transformed_global - target

    # Reinsert the transformed variables into the sharp form of BBLR
    # Proposition 3.1.  Its outer variables are r,t, its two nontrivial
    # inner variables are l,k, and its shift has exponent 1+theta.
    # The sharp-range condition is
    #
    #   (1+r1)+(1+r2) >= 2*(1+theta),
    #
    # which is exactly delta >= theta.
    bblr_outer_sum = left_modulus + right_modulus
    bblr_outer_max = max(left_modulus, right_modulus)
    bblr_ab_before = F(1, 2) + resonance_shift + bblr_outer_sum
    bblr_watt_before = (
        F(3, 4)
        + F(3, 2) * resonance_shift
        + bblr_outer_max / 2
    )
    transform_normalization = poisson_amplitude + overlap_integral
    bblr_ab_total = bblr_ab_before + transform_normalization + gamma
    bblr_watt_total = (
        bblr_watt_before + transform_normalization + gamma
    )
    bblr_ab_deficit = bblr_ab_total - target
    bblr_watt_deficit = bblr_watt_total - target
    original_bblr = strict_power_convolution_kloosterman_audit(
        collapsed_exponent=s,
        cofactor_exponent=delta,
        quotient_exponent=theta,
        left_cross_gcd_exponent=r1,
    )
    bblr_watt_extra = (
        bblr_watt_deficit - original_bblr.bblr_watt_deficit
    )
    return StrictPowerDoublePoissonResonanceAudit(
        collapsed_exponent=s,
        cofactor_exponent=delta,
        gcd_exponent=gamma,
        quotient_exponent=theta,
        left_cross_gcd_exponent=r1,
        right_cross_gcd_exponent=r2,
        left_slope_exponent=left_slope,
        right_slope_exponent=right_slope,
        left_modulus_exponent=left_modulus,
        right_modulus_exponent=right_modulus,
        left_dual_exponent=left_dual,
        right_dual_exponent=right_dual,
        dual_side_product_exponent=dual_product,
        resonance_shift_exponent=resonance_shift,
        poisson_amplitude_exponent=poisson_amplitude,
        overlap_integral_exponent=overlap_integral,
        transformed_absolute_inner_exponent=transformed_inner,
        original_inner_raw_exponent=original_inner,
        absolute_transform_loss_exponent=transform_loss,
        transformed_global_absolute_exponent=transformed_global,
        global_target_exponent=target,
        transformed_required_saving_exponent=required,
        resonance_identity_exact=True,
        two_poisson_scales_exact=True,
        absolute_transform_loss_is_one_minus_delta_plus_theta=(
            transform_loss == 1 - delta + theta
        ),
        absolute_double_poisson_route_covered=False,
        pre_cauchy_signed_resonance_estimate_required=True,
        bblr_sharp_range_verified=(
            bblr_outer_sum >= 2 * resonance_shift
            and delta >= theta
        ),
        bblr_ab_before_normalization_exponent=bblr_ab_before,
        bblr_watt_before_normalization_exponent=bblr_watt_before,
        transform_normalization_exponent=transform_normalization,
        bblr_ab_total_exponent=bblr_ab_total,
        bblr_watt_total_exponent=bblr_watt_total,
        bblr_ab_deficit=bblr_ab_deficit,
        bblr_watt_deficit=bblr_watt_deficit,
        original_bblr_ab_deficit=original_bblr.bblr_ab_deficit,
        original_bblr_watt_deficit=original_bblr.bblr_watt_deficit,
        bblr_ab_deficit_is_invariant=(
            bblr_ab_deficit == original_bblr.bblr_ab_deficit
        ),
        bblr_watt_extra_deficit=bblr_watt_extra,
        bblr_watt_extra_deficit_is_nonnegative=(
            bblr_watt_extra >= 0
        ),
        double_poisson_improves_bblr=(
            bblr_ab_deficit < original_bblr.bblr_ab_deficit
            or bblr_watt_deficit < original_bblr.bblr_watt_deficit
        ),
    )


def transition_line_finite_fourier_identity(
    *,
    a: int,
    b: int,
    r1: int,
    r2: int,
    h: int,
    modulus: int,
) -> dict[str, int | bool]:
    """Check finite-character detection of ``b*r1-a*r2=h``.

    If ``Q`` is larger than the absolute line defect, congruence modulo
    ``Q`` is equivalent to integer equality.  Character orthogonality
    then represents the equality indicator as
    ``Q^(-1) sum_(j mod Q) e(j*defect/Q)`` exactly.
    """
    if min(a, b, r1, r2, modulus) <= 0:
        raise ValueError("line variables and Fourier modulus are positive")
    defect = b * r1 - a * r2 - h
    if modulus <= abs(defect):
        raise ValueError("modulus must exceed the absolute line defect")
    congruence = int(defect % modulus == 0)
    equality = int(defect == 0)
    return {
        "line_defect": defect,
        "congruence_indicator": congruence,
        "integer_equality_indicator": equality,
        "finite_fourier_detects_integer_equality": congruence == equality,
    }


def transition_line_fourier_microarc_audit(
    *,
    denominator_gcd_exponent: Fraction,
) -> TransitionLineFourierMicroarcAudit:
    """Audit the exact frequency scales of the top determinant line.

    Fix one integer ``g=T^gamma`` and put ``A=T^(1-gamma)``.  The
    equation ``b*r1-a*r2=h`` has ``a,b,h`` of length ``A`` and
    ``r1,r2`` of length ``T``.  Fourier orthogonality detects the line,
    and Poisson in the smooth h-window localizes to ``|alpha|<=A^(-1)``.
    The products ``a*r`` have scale ``A*T``, so the constant-phase
    microarc has width ``(A*T)^(-1)``; the full window contains exactly
    one power of T such microarc scales.

    In a fictitious tensor-separated constant mode, the microarc is
    ``T^(-1)|M(A)M(T)|^2``.  Reaching the fixed-g target ``A*T`` would
    require ``|M(A)M(T)|<=T*sqrt(A)``, a saving ``A^(1/2)`` in the
    product, or exponent ``(1-gamma)/2``.  The actual coupled weight has
    not been tensor-separated and its constant tensor coefficient has
    not been shown nonzero, so this is a diagnostic obstruction rather
    than a necessary theorem interface.
    """
    common_gcd = F(denominator_gcd_exponent)
    if common_gcd < 0 or common_gcd > F(1):
        raise ValueError("denominator gcd exponent must lie in [0,1]")
    alpha = F(1) - common_gcd
    product_scale = alpha + F(1)
    full_window = -alpha
    microarc = -product_scale
    microarc_count = full_window - microarc
    raw = F(1) + 2 * alpha
    target = F(1) + alpha
    required = raw - target
    mertens_trivial = alpha + F(1)
    mertens_target = F(1) + alpha / 2
    mertens_saving = mertens_trivial - mertens_target
    return TransitionLineFourierMicroarcAudit(
        denominator_gcd_exponent=common_gcd,
        denominator_cofactor_exponent=alpha,
        h_window_exponent=alpha,
        product_phase_scale_exponent=product_scale,
        full_frequency_window_exponent=full_window,
        constant_phase_microarc_exponent=microarc,
        microarcs_in_full_window_exponent=microarc_count,
        fixed_g_raw_line_exponent=raw,
        fixed_g_target_exponent=target,
        required_fixed_g_saving_exponent=required,
        separated_mertens_product_trivial_exponent=mertens_trivial,
        separated_mertens_product_target_exponent=mertens_target,
        required_mertens_product_saving_exponent=mertens_saving,
        finite_fourier_orthogonality_exact=True,
        h_window_poisson_localization_exact=True,
        actual_coupled_weight_tensor_separated=False,
        nonzero_constant_tensor_mode_verified=False,
        microarc_mertens_reduction_is_actual_gate=False,
        whole_line_family_covered=False,
    )


def transition_balanced_convolution_identity(
    *,
    factor_pairs: tuple[tuple[int, int, int], ...],
    shift_length: int,
) -> dict[str, int | bool]:
    """Verify the exact Fejer autocorrelation reindexing on finite data.

    Each triple is ``(a, r, weight)`` and contributes ``weight`` to the
    balanced product coefficient at ``n=a*r``.  Expanding the coefficient
    autocorrelation and expanding the original four-factor determinant sum
    are the same finite reindexing.  Integrating interval indicators gives
    the integer overlap ``(H-|n-m|)_+`` exactly.
    """
    if shift_length <= 0:
        raise ValueError("shift length must be positive")
    if any(a <= 0 or r <= 0 for a, r, _ in factor_pairs):
        raise ValueError("factor variables must be positive")

    coefficients: dict[int, int] = {}
    for a, r, weight in factor_pairs:
        coefficients[a * r] = coefficients.get(a * r, 0) + weight

    coefficient_expansion = 0
    for n, left in coefficients.items():
        for m, right in coefficients.items():
            coefficient_expansion += (
                max(shift_length - abs(n - m), 0) * left * right
            )

    factor_expansion = 0
    for a, r, left in factor_pairs:
        for b, s, right in factor_pairs:
            factor_expansion += (
                max(shift_length - abs(a * r - b * s), 0)
                * left
                * right
            )

    return {
        "coefficient_expansion": coefficient_expansion,
        "factor_expansion": factor_expansion,
        "short_interval_overlap_integral": coefficient_expansion,
        "autocorrelation_reindex_exact": (
            coefficient_expansion == factor_expansion
        ),
        "fejer_short_interval_identity_exact": True,
    }


def transition_balanced_mobius_convolution_audit(
    *,
    denominator_gcd_exponent: Fraction,
) -> TransitionBalancedMobiusConvolutionAudit:
    """Collapse the top determinant line to one local convolution energy.

    For fixed ``g=T^gamma`` put ``A=T^(1-gamma)`` and

    ``c(n)=sum_(a*r=n) mu(a)mu(r)U(a/A)V(r/T)``.

    A Fejer-smoothed determinant quotient is exactly the autocorrelation of
    ``c`` at differences of length ``A``, equivalently ``A^(-1)`` times the
    mean square of its sums on intervals of length ``A`` around product
    scale ``A*T``.  The raw exponent is ``1+2*(1-gamma)`` and the diagonal
    scale is ``1+(1-gamma)``, so a full factor ``A`` is still required.

    Mangerel's divisor-bounded short-interval theorem, even granted
    optimistically and uniformly after exact Mellin inversion, only makes
    the normalized variance ``o(log^C T)``.  It does not supply the missing
    power ``A``.  The actual balanced coefficient is not multiplicative;
    it is an absolutely convergent Mellin superposition of twisted
    multiplicative convolutions.  The exact coprimality-layer and lifted
    kernel argument recorded by ``transition_coprimality_layer_audit``
    supplies the remaining algebraic aggregation.  The square-root
    variance estimate itself is still unproved.
    """
    gamma = F(denominator_gcd_exponent)
    if gamma < 0 or gamma > F(1):
        raise ValueError("denominator gcd exponent must lie in [0,1]")
    alpha = F(1) - gamma
    product_center = F(1) + alpha
    raw = product_center + alpha
    target = product_center
    required = raw - target
    return TransitionBalancedMobiusConvolutionAudit(
        denominator_gcd_exponent=gamma,
        cofactor_length_exponent=alpha,
        product_center_exponent=product_center,
        product_difference_exponent=alpha,
        raw_autocorrelation_exponent=raw,
        diagonal_scale_target_exponent=target,
        required_variance_saving_exponent=required,
        optimistic_mangerel_bound_exponent=raw,
        optimistic_mangerel_power_deficit=required,
        endpoint_taper_count_in_square=4,
        product_energy_log_loss=1,
        net_endpoint_log_saving=3,
        finite_autocorrelation_identity_exact=True,
        fejer_short_interval_identity_exact=True,
        balanced_coefficient_is_multiplicative=False,
        exact_mellin_twisted_convolution_available=True,
        actual_coprimality_layers_aggregated=True,
        actual_coupled_kernel_nuclear_norm_verified=True,
        published_square_root_variance_proved=False,
        whole_line_family_covered=False,
        source=(
            "Mangerel, Divisor-bounded multiplicative functions in short "
            "intervals, Res. Math. Sci. 10 (2023), Theorem 1.7"
        ),
    )


def _finite_mobius(n: int) -> int:
    """Return the classical Möbius function by exact trial division."""
    if n <= 0:
        raise ValueError("Möbius input must be positive")
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


def _positive_divisors(n: int) -> tuple[int, ...]:
    if n <= 0:
        raise ValueError("divisor input must be positive")
    return tuple(d for d in range(1, n + 1) if n % d == 0)


def transition_line_coprimality_layer_identity(
    *,
    a: int,
    b: int,
    r1: int,
    r2: int,
    g: int,
    q: int,
) -> dict[str, int | bool]:
    """Expand all cross-coprimalities in the determinant line exactly.

    The three Möbius inversions are

    ``1_(a,b)=1 sum_(d0|a,b) mu(d0)``,
    ``1_(r1,g*a)=1 sum_(d1|r1,g*a) mu(d1)``, and
    ``1_(r2,g*b)=1 sum_(d2|r2,g*b) mu(d2)``.

    The remaining q-coprimality is already a product of one-variable
    restrictions and is retained exactly.
    """
    if min(a, b, r1, r2, g, q) <= 0:
        raise ValueError("all coprimality variables must be positive")
    original = int(
        gcd(a, b) == 1
        and gcd(r1, g * a) == 1
        and gcd(r2, g * b) == 1
        and gcd(q, g * a * b * r1 * r2) == 1
    )
    q_factor = int(gcd(q, g * a * b * r1 * r2) == 1)
    sum0 = sum(_finite_mobius(d) for d in _positive_divisors(gcd(a, b)))
    sum1 = sum(
        _finite_mobius(d) for d in _positive_divisors(gcd(r1, g * a))
    )
    sum2 = sum(
        _finite_mobius(d) for d in _positive_divisors(gcd(r2, g * b))
    )
    expanded = q_factor * sum0 * sum1 * sum2
    return {
        "original_indicator": original,
        "q_one_variable_factor": q_factor,
        "d0_mobius_sum": sum0,
        "d1_mobius_sum": sum1,
        "d2_mobius_sum": sum2,
        "expanded_indicator": expanded,
        "three_indicator_expansion_exact": original == expanded,
    }


def transition_line_coprimality_layer_density(
    *,
    d0: int,
    d1: int,
    d2: int,
    g: int,
) -> dict[str, int | Fraction | bool]:
    """Return the exact volume density of one squarefree divisor layer.

    Put ``e_i=(d_i,g)`` and ``f_i=d_i/e_i``.  The layer forces
    ``lcm(d0,f1)|a``, ``lcm(d0,f2)|b``, ``d1|r1``, and ``d2|r2``.
    Its four-variable density is therefore the reciprocal of the product
    of those four moduli, including all overlaps exactly.
    """
    if min(d0, d1, d2, g) <= 0:
        raise ValueError("layer divisors and g must be positive")
    if any(_finite_mobius(d) == 0 for d in (d0, d1, d2, g)):
        raise ValueError("layer divisors and g must be squarefree")
    e1 = gcd(d1, g)
    e2 = gcd(d2, g)
    f1 = d1 // e1
    f2 = d2 // e2
    lcm01 = d0 * f1 // gcd(d0, f1)
    lcm02 = d0 * f2 // gcd(d0, f2)
    denominator = d1 * d2 * lcm01 * lcm02
    return {
        "e1": e1,
        "e2": e2,
        "f1": f1,
        "f2": f2,
        "a_modulus": lcm01,
        "b_modulus": lcm02,
        "r1_modulus": d1,
        "r2_modulus": d2,
        "density_denominator": denominator,
        "density": F(1, denominator),
        "factorization_exact": (
            d1 == e1 * f1
            and d2 == e2 * f2
            and gcd(f1, g) == 1
            and gcd(f2, g) == 1
        ),
    }


def transition_coprimality_layer_audit(
    *,
    denominator_gcd_exponent: Fraction,
) -> TransitionCoprimalityLayerAudit:
    """Audit the exact route from the coupled top kernel to layered DCV.

    At a prime not dividing ``g``, summing the absolute density over the
    eight memberships in ``(d0,d1,d2)`` gives

    ``1 + 3/p^2 + 2/p^3 + 2/p^4``.

    Hence the divisor layers aggregate absolutely.  Primes dividing the
    squarefree ``g`` contribute only a finite ``prod_(p|g)(1+O(1/p))``
    factor.  On the top determinant face, lift the kernel to the five
    independent normalized variables ``(a,b,r1,r2,h)`` before imposing
    ``b*r1-a*r2=h``.  The determinant cutoff is then an h-factor and has
    no positive-power transverse derivative cost.  Two integrations by
    parts in each Fourier coordinate (total order ten) give an integrable
    five-dimensional Fourier majorant from the existing smooth-kernel
    derivative bounds.
    """
    gamma = F(denominator_gcd_exponent)
    if gamma < 0 or gamma > F(1):
        raise ValueError("denominator gcd exponent must lie in [0,1]")
    alpha = F(1) - gamma
    return TransitionCoprimalityLayerAudit(
        denominator_gcd_exponent=gamma,
        cofactor_length_exponent=alpha,
        exact_three_indicator_expansion=True,
        non_g_prime_p2_coefficient=3,
        non_g_prime_p3_coefficient=2,
        non_g_prime_p4_coefficient=2,
        non_g_absolute_euler_product_converges=True,
        g_prime_loss_is_subpolylogarithmic=True,
        lifted_kernel_dimension=5,
        fourier_derivative_order=10,
        determinant_cutoff_derivative_power_cost=F(0),
        lifted_kernel_fourier_nuclear_norm_verified=True,
        layer_density_aggregation_verified=True,
        required_layer_variance_saving_exponent=alpha,
        published_layer_variance_proved=False,
        actual_line_family_reduced_to_layered_variance=True,
        whole_line_family_covered=False,
    )


def transition_mobius_dirichlet_product_identity(
    *,
    left_terms: tuple[tuple[int, int], ...],
    right_terms: tuple[tuple[int, int], ...],
    integer_power: int,
) -> dict[str, Fraction | bool | dict[int, int]]:
    """Verify a finite Dirichlet-product/convolution identity exactly.

    This is the algebra underneath

    ``P_A(t) P_T(t) = sum_n c(n) n^(-1/2-it)``.

    Integer powers keep the fixture rational; the finite reindexing is
    independent of the complex exponent used in the analytic argument.
    """
    if integer_power <= 0:
        raise ValueError("integer power must be positive")
    if any(n <= 0 for n, _ in left_terms + right_terms):
        raise ValueError("Dirichlet indices must be positive")
    convolution: dict[int, int] = {}
    for left_index, left_coefficient in left_terms:
        for right_index, right_coefficient in right_terms:
            product_index = left_index * right_index
            convolution[product_index] = (
                convolution.get(product_index, 0)
                + left_coefficient * right_coefficient
            )
    left_sum = sum(
        (F(coefficient, index**integer_power) for index, coefficient in left_terms),
        F(0),
    )
    right_sum = sum(
        (
            F(coefficient, index**integer_power)
            for index, coefficient in right_terms
        ),
        F(0),
    )
    product_sum = left_sum * right_sum
    convolution_sum = sum(
        (
            F(coefficient, index**integer_power)
            for index, coefficient in convolution.items()
        ),
        F(0),
    )
    return {
        "left_dirichlet_sum": left_sum,
        "right_dirichlet_sum": right_sum,
        "product_dirichlet_sum": product_sum,
        "convolution_coefficients": convolution,
        "convolution_dirichlet_sum": convolution_sum,
        "dirichlet_product_identity_exact": product_sum == convolution_sum,
    }


def transition_mobius_dirichlet_fourth_moment_audit(
    *,
    denominator_gcd_exponent: Fraction,
) -> TransitionMobiusDirichletFourthMomentAudit:
    """Normalize layered DCV as a mixed-fourth-moment superposition.

    Write ``A=T^(1-gamma)`` and ``X=A*T``.  The exact product polynomial
    has length ``X``.  Mellin inversion of the actual two-variable kernel
    contributes ``T/X=1/A`` between coefficient and moment scales.  Thus
    the DCV coefficient target ``X`` becomes a moment target ``T``.
    The generic mean-value theorem instead sees the full length ``X`` and
    misses exactly the power ``A``.
    """
    gamma = F(denominator_gcd_exponent)
    if gamma < 0 or gamma > F(1):
        raise ValueError("denominator gcd exponent must lie in [0,1]")
    alpha = F(1) - gamma
    product = F(1) + alpha
    height = F(1)
    normalization = height - product
    target = product + normalization
    generic = max(height, product)
    return TransitionMobiusDirichletFourthMomentAudit(
        denominator_gcd_exponent=gamma,
        cofactor_length_exponent=alpha,
        long_mobius_polynomial_exponent=F(1),
        product_polynomial_exponent=product,
        physical_height_exponent=height,
        dcv_coefficient_target_exponent=product,
        coefficient_to_moment_normalization_exponent=normalization,
        moment_target_exponent=target,
        generic_mean_value_exponent=generic,
        generic_mean_value_power_deficit=generic - target,
        exact_dirichlet_product_identity=True,
        exact_scaled_log_coordinate_kernel_inversion=True,
        transform_is_schwartz_localized_at_height_T=True,
        separated_transform_compactly_excludes_zero_frequency=False,
        coprimality_layers_already_aggregated=True,
        dcv_exact_mixed_fourth_moment_superposition=True,
        uniform_mixed_fourth_moment_sufficient_for_dcv=True,
        dcv_implies_each_separated_moment=False,
        symmetric_top_face_is_mobius_fourth_moment=gamma == F(0),
        published_mixed_fourth_moment_proved=False,
        whole_line_family_covered=False,
        source=(
            "Exact finite Dirichlet convolution and scaled-log-coordinate "
            "Mellin inversion of the physical W(t/T) kernel; uniform "
            "componentwise control is sufficient but not necessary. The generic "
            "Dirichlet-polynomial mean value loses A=T^(1-gamma), and no "
            "audited published theorem proves the required uniform mixed "
            "Möbius fourth moment."
        ),
    )


def transition_mobius_large_value_audit(
    *,
    amplitude_exponent: Fraction,
) -> TransitionMobiusLargeValueAudit:
    """Compare the top Möbius fourth-moment tail with published bounds.

    For the unnormalised polynomial of length ``N=T``, a value
    ``V=T^sigma`` contributes ``R(V)V^4``.  The desired normalised
    fourth moment ``O(T log^(1+o(1)) T)`` is the unnormalised target
    ``T^(3+o(1))``, so it asks for ``R(V)<=T^(3-4 sigma+o(1))``.

    The classical first large-value term is ``T^2 V^-2``.  At ``N=T``,
    Guth--Maynard Theorem 1.1 contributes after multiplication by
    ``V^4`` the three exponents ``2+2 sigma``, ``18/5``, and ``17/5``.
    Menon's short-interval estimates save logarithms only, hence zero
    on this positive-power ledger.
    """
    sigma = F(amplitude_exponent)
    if sigma < F(1, 2) or sigma > F(1):
        raise ValueError("amplitude exponent must lie in [1/2,1]")
    target = F(3)
    required_count = target - F(4) * sigma
    classical_count = F(2) - F(2) * sigma
    classical_contribution = classical_count + F(4) * sigma
    gm1 = F(2) + F(2) * sigma
    gm2 = F(18, 5)
    gm3 = F(17, 5)
    gm_contribution = max(gm1, gm2, gm3)
    best = min(classical_contribution, gm_contribution)
    deficit = max(F(0), best - target)
    return TransitionMobiusLargeValueAudit(
        amplitude_exponent=sigma,
        unnormalized_fourth_moment_target_exponent=target,
        required_large_value_count_exponent=required_count,
        required_count_exponent_is_negative=required_count < 0,
        classical_large_value_count_exponent=classical_count,
        classical_fourth_contribution_exponent=classical_contribution,
        guth_maynard_term1_contribution_exponent=gm1,
        guth_maynard_term2_contribution_exponent=gm2,
        guth_maynard_term3_contribution_exponent=gm3,
        guth_maynard_fourth_contribution_exponent=gm_contribution,
        best_published_fourth_contribution_exponent=best,
        best_published_power_deficit=deficit,
        menon_positive_power_saving_exponent=F(0),
        componentwise_fourth_moment_pointwise_threshold=F(3, 4),
        mobius_large_value_theorem_proved=False,
        power_boundary_covered=deficit == 0,
        original_signed_dcv_requires_componentwise_large_values=False,
        whole_line_family_covered=False,
        source=(
            "Classical Montgomery-Halasz-Huxley large values; "
            "Guth--Maynard, arXiv:2405.20552v2, Theorem 1.1; and "
            "Menon, arXiv:2607.15574v1, Theorems 1.1 and 1.5."
        ),
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
    transition_determinant_left = transition_type_ii_determinant_audit(
        transition_box,
        b_exponent=F(1, 3),
    )
    transition_determinant_right = transition_type_ii_determinant_audit(
        transition_box,
        b_exponent=F(2, 3),
    )
    print(
        "large_q_transition: type_ii_determinant="
        "1/3:zero=3,target=2747/750,margin=497/750,delta=8/3,"
        "y_modulus=10/3,y_sqrt=5/3,y_b_gap=4/3,y_dual=3;"
        "2/3:zero=3,target=2497/750,margin=247/750,delta=7/3,"
        "y_modulus=8/3,y_sqrt=4/3,y_b_gap=2/3,y_dual=2 "
        "zero_closes=True b_completion=False nonzero_gate=True "
        "proved=False covered=False"
    )
    transition_lcm_generic = transition_type_ii_lcm_completion_audit(
        transition_box,
        b_exponent=F(2, 3),
        gcd_s_exponent=F(0),
    )
    transition_lcm_high_gcd = transition_type_ii_lcm_completion_audit(
        transition_box,
        b_exponent=F(2, 3),
        gcd_s_exponent=F(3, 4),
    )
    print(
        "large_q_transition: type_ii_lcm_completion="
        "generic:beta=2/3,gcd=0,lcm=2,sqrt=1,b_gap=1/3,"
        "b_surplus=0,dual=4/3,required=501/250,remain=501/250,"
        "bp_loss=1/2;"
        "high_gcd:beta=2/3,gcd=3/4,lcm=5/4,sqrt=5/8,b_gap=0,"
        "b_surplus=1/24,dual=7/12,required=627/500,"
        "remain=3637/3000,bp_loss=5/16 "
        "lcm_phase=True smooth_b=False b_closes=False bp_closes=False "
        "covered=False"
    )
    transition_long_trace = transition_long_cutoff_mobius_trace_audit(
        transition_box,
        cutoff_gap_exponent=F(1, 10),
        b_exponent=F(1, 20),
    )
    print(
        "large_q_transition: long_cutoff_mobius_trace="
        "eta=1/10,beta=1/20,U=9/10,a=19/20,reflected=1/20,"
        "trace_margin=9/20,ambient=3,target=999/500,"
        "power_deficit=501/500 identity=True prime_modulus=False "
        "nonexceptional_uniform=False two_logs_close=False covered=False"
    )
    transition_cluster = transition_reciprocal_cluster_closure_audit(
        transition_box,
        distance_max=F(1, 2),
    )
    print(
        "large_q_transition: reciprocal_cluster_closure="
        "Dmax=1/2,A=1,cluster_bound=2,target=2,power_gap=0,"
        "taper_log=2,energy_log=1/2,shell_log=1,kernel_log=0,"
        "net_log=1/2,global_power=1 low_union=True "
        "residual=(1/2,1],top_save=1/2 whole_face=False"
    )
    transition_far_gate = transition_far_shell_mobius_gate_audit(
        transition_box,
        distance=F(1),
        fkm_eta=F(1, 25),
        optimistic_fkm_applications=2,
    )
    print(
        "large_q_transition: far_shell_mobius_gate="
        "theta=1,bound=5/2,target=1999/1000,required=501/1000,"
        "fkm_eta=1/25,fkm_apps=2,fkm_save=2/25,"
        "fkm_residual=421/1000 two_mu=True coupled=True "
        "prime_factor=False frequency=False cofactor=False "
        "new_joint=True proved=False covered=False"
    )
    transition_far_factor = transition_far_shell_factor_box_audit(
        transition_box,
        distance=F(1),
        b_exponent=F(2, 3),
    )
    print(
        "large_q_transition: far_shell_factor_box="
        "theta=1,beta=2/3,U=1/3,V=1/3,a=1/3,"
        "cluster=5/2,target=999/500,required=251/500,"
        "diag=3,square_target=2497/750,diag_margin=247/750 "
        "shifted=True phase=True diag_closes=True nonzero_joint=True "
        "proved=False covered=False"
    )
    transition_square_geometry = transition_factor_square_geometry_audit(
        transition_box,
        distance=F(1),
        b_exponent=F(2, 3),
    )
    print(
        "large_q_transition: factor_square_geometry="
        "theta=1,beta=2/3,Gamma_max=4/3,zero=3,"
        "square_target=2497/750,zero_margin=247/750 "
        "cross_relation=True primitive_zero=True n_offdiag=True "
        "cluster_l2=True zero_closes=True nonzero_gate=True "
        "proved=False covered=False"
    )
    transition_nonzero_gamma = transition_nonzero_gamma_shell_audit(
        transition_box,
        distance=F(1),
        b_exponent=F(2, 3),
        determinant_exponent=F(4, 3),
        s_gcd_exponent=F(0),
        a_gcd_exponent=F(0),
    )
    print(
        "large_q_transition: nonzero_gamma_shell="
        "theta=1,beta=2/3,xi=4/3,gamma=0,alpha=0,"
        "lcm=2,bdual=4/3,astep=1/3,orbit=2/3,"
        "cluster_square=13/3,target=2497/750,required=251/250 "
        "reciprocity_mod=1,reduces=False two_mu=True n_pair=True "
        "coupled=True exact_orbit=True square_proved=False required_gate=True "
        "proved=False covered=False"
    )
    transition_graph_covered = transition_gamma_graph_energy_audit(
        transition_box,
        distance=F(3, 4),
        b_exponent=F(2, 3),
        determinant_exponent=F(1, 3),
    )
    print(
        "large_q_transition: gamma_graph_energy="
        "theta=3/4,beta=2/3,xi=1/3,fiber=0,degree=1/3,"
        "vertex_l2=11/4,bound=37/12,target=2497/750,"
        "margin=123/500,lhs=3/4,threshold=249/250 "
        "mobius=False phase=False covered=True"
    )
    transition_graph_residual = transition_gamma_graph_energy_audit(
        transition_box,
        distance=F(3, 4),
        b_exponent=F(2, 3),
        determinant_exponent=F(13, 12),
    )
    print(
        "large_q_transition: gamma_graph_residual="
        "theta=3/4,beta=2/3,xi=13/12,fiber=3/4,"
        "bound=23/6,margin=-63/125 covered=False"
    )
    transition_gcd_graph_top = transition_gamma_gcd_graph_energy_audit(
        transition_box,
        distance=F(1),
        b_exponent=F(2, 3),
        determinant_exponent=F(4, 3),
        s_gcd_exponent=F(1),
        a_gcd_exponent=F(1, 100),
    )
    print(
        "large_q_transition: gamma_gcd_graph_top="
        "theta=1,beta=2/3,xi=4/3,gamma=1,alpha=1/100,"
        "raw_fiber=1,reduced_fiber=0,degree=97/300,"
        "bound=997/300,target=2497/750,margin=3/500,"
        "lhs=99/100,threshold=249/250 covered=True"
    )
    transition_gcd_graph_primitive = (
        transition_gamma_gcd_graph_energy_audit(
            transition_box,
            distance=F(1),
            b_exponent=F(2, 3),
            determinant_exponent=F(4, 3),
            s_gcd_exponent=F(0),
            a_gcd_exponent=F(0),
        )
    )
    print(
        "large_q_transition: gamma_gcd_graph_primitive="
        "theta=1,beta=2/3,xi=4/3,gamma=0,alpha=0,"
        "reduced_fiber=1,degree=4/3,bound=13/3,"
        "margin=-251/250 covered=False"
    )
    transition_cross_lattice = transition_cross_determinant_lattice_audit(
        transition_box,
        distance=F(1),
        b_exponent=F(2, 3),
        determinant_exponent=F(1, 4),
    )
    print(
        "large_q_transition: cross_determinant_lattice="
        "theta=1,beta=2/3,xi=1/4,degree=1/4,vertex_l2=3,"
        "bound=13/4,target=2497/750,margin=119/1500,"
        "lhs=5/4,threshold=997/750 gcd_k=True fiber=True "
        "mobius=False covered=True"
    )
    transition_cross_residual = transition_cross_determinant_lattice_audit(
        transition_box,
        distance=F(1),
        b_exponent=F(2, 3),
        determinant_exponent=F(1, 3),
    )
    print(
        "large_q_transition: cross_determinant_residual="
        "theta=1,beta=2/3,xi=1/3,bound=10/3,"
        "margin=-1/250 covered=False"
    )
    transition_farey_hecke = transition_farey_hecke_orbit_audit(
        transition_box,
        distance=F(1),
        b_exponent=F(2, 3),
        determinant_exponent=F(1, 3),
    )
    print(
        "large_q_transition: farey_hecke_orbit="
        "theta=1,beta=2/3,xi=1/3,hecke=1,entry=1,modulus=1,"
        "frequency=1,target=2497/750 determinant=True phase=True "
        "b_in_index=True mu_b_squared=True mu_index=False "
        "entry_mu=True cofactor_joint=True arch=True coupled=True "
        "kuznetsov=False new_entry_hecke=True proved=False covered=False"
    )
    transition_farey_hecke_maximal = transition_farey_hecke_orbit_audit(
        transition_box,
        distance=F(1),
        b_exponent=F(2, 3),
        determinant_exponent=F(4, 3),
    )
    print(
        "large_q_transition: farey_hecke_maximal="
        "theta=1,beta=2/3,xi=4/3,hecke=2 covered=False"
    )
    transition_entry_factor = transition_entry_mobius_factorization_audit(
        transition_box,
        distance=F(1),
        b_exponent=F(2, 3),
        entry_short_factor_exponent=F(2, 3),
    )
    print(
        "large_q_transition: entry_mobius_factor="
        "theta=1,beta=2/3,eta=2/3,c=1/3,d=2/3,"
        "wright_size=True,wright_saving=-1,target=1/500,"
        "deficit=501/500 factor=True double_recip=True "
        "cofactor_joint=True shift_joint=True coupled=True "
        "hypotheses=False two_entry=True proved=False covered=False"
    )
    transition_entry_short = transition_entry_mobius_factorization_audit(
        transition_box,
        distance=F(1),
        b_exponent=F(2, 3),
        entry_short_factor_exponent=F(1, 3),
    )
    print(
        "large_q_transition: entry_mobius_short="
        "theta=1,eta=1/3,wright_size=False covered=False"
    )
    transition_cross_gcd = transition_cross_gcd_lattice_audit(
        transition_box,
        distance=F(1),
        b_exponent=F(2, 3),
        determinant_exponent=F(1, 3),
        a_gcd_exponent=F(1, 100),
        w_gcd_exponent=F(0),
    )
    print(
        "large_q_transition: cross_gcd_lattice="
        "theta=1,beta=2/3,xi=1/3,alpha=1/100,omega=0,"
        "reduced=97/300,degree=97/300,bound=997/300,"
        "target=2497/750,margin=3/500,lhs=397/300,"
        "threshold=997/750 combined=True fiber=True "
        "mobius=False covered=True"
    )
    transition_cross_gcd_maximal = transition_cross_gcd_lattice_audit(
        transition_box,
        distance=F(1),
        b_exponent=F(2, 3),
        determinant_exponent=F(4, 3),
        a_gcd_exponent=F(1, 3),
        w_gcd_exponent=F(3, 4),
    )
    print(
        "large_q_transition: cross_gcd_maximal="
        "theta=1,beta=2/3,xi=4/3,alpha=1/3,omega=3/4,"
        "reduced=1/4,bound=13/4,margin=119/1500 covered=True"
    )
    transition_cross_gcd_primitive = transition_cross_gcd_lattice_audit(
        transition_box,
        distance=F(1),
        b_exponent=F(2, 3),
        determinant_exponent=F(4, 3),
        a_gcd_exponent=F(0),
        w_gcd_exponent=F(0),
    )
    print(
        "large_q_transition: cross_gcd_primitive="
        "theta=1,beta=2/3,xi=4/3,alpha=0,omega=0,"
        "reduced=4/3,bound=13/3,margin=-251/250 covered=False"
    )
    transition_triple_gcd = transition_triple_gcd_lattice_audit(
        transition_box,
        distance=F(1),
        b_exponent=F(2, 3),
        determinant_exponent=F(1, 3),
        a_gcd_exponent=F(0),
        s_gcd_exponent=F(1, 100),
        w_gcd_exponent=F(0),
    )
    print(
        "large_q_transition: triple_gcd_lattice="
        "theta=1,beta=2/3,xi=1/3,alpha=0,gamma=1/100,omega=0,"
        "reduced=97/300,bound=997/300,target=2497/750,"
        "margin=3/500 triple=True mobius=False covered=True"
    )
    transition_triple_gcd_maximal = transition_triple_gcd_lattice_audit(
        transition_box,
        distance=F(1),
        b_exponent=F(2, 3),
        determinant_exponent=F(4, 3),
        a_gcd_exponent=F(1, 3),
        s_gcd_exponent=F(1, 3),
        w_gcd_exponent=F(5, 12),
    )
    print(
        "large_q_transition: triple_gcd_maximal="
        "theta=1,beta=2/3,xi=4/3,alpha=1/3,gamma=1/3,"
        "omega=5/12,reduced=1/4,bound=13/4,"
        "margin=119/1500 covered=True"
    )
    transition_triple_gcd_primitive = (
        transition_triple_gcd_lattice_audit(
            transition_box,
            distance=F(1),
            b_exponent=F(2, 3),
            determinant_exponent=F(4, 3),
            a_gcd_exponent=F(0),
            s_gcd_exponent=F(0),
            w_gcd_exponent=F(0),
        )
    )
    print(
        "large_q_transition: triple_gcd_primitive="
        "theta=1,beta=2/3,xi=4/3,alpha=0,gamma=0,omega=0,"
        "reduced=4/3,bound=13/3,margin=-251/250 covered=False"
    )
    transition_final_gate = transition_final_two_entry_gate_audit(
        transition_box,
        distance=F(1),
        b_exponent=F(2, 3),
        determinant_exponent=F(4, 3),
        a_gcd_exponent=F(0),
        s_gcd_exponent=F(0),
        w_gcd_exponent=F(0),
    )
    print(
        "large_q_transition: final_two_entry_gate="
        "theta=1,beta=2/3,xi=4/3,gcd=0,reduced=4/3,"
        "graph=13/3,sqrt_save=1,required=10/3,raw_target=10/3,"
        "margin=0,identity=True critical=True taper_log=4,"
        "energy_log=1,post_cauchy_log=3/2,beta_log=1,"
        "global_log=1/2,global_power=1 required_gate=True "
        "proved=False whole=False"
    )
    transition_final_slack = transition_final_two_entry_gate_audit(
        transition_box,
        distance=F(3, 4),
        b_exponent=F(2, 3),
        determinant_exponent=F(13, 12),
        a_gcd_exponent=F(0),
        s_gcd_exponent=F(0),
        w_gcd_exponent=F(0),
    )
    print(
        "large_q_transition: final_two_entry_slack="
        "theta=3/4,beta=2/3,xi=13/12,gcd=0,"
        "required=17/6,raw_target=10/3,margin=1/2 critical=False"
    )
    transition_h_poisson_critical = transition_h_poisson_line_audit(
        distance=F(1),
        gcd_exponent=F(0),
    )
    print(
        "large_q_transition: h_poisson_line_critical="
        "theta=1,gamma=0,H=1/2,v=1/2,j=1/2,delta0=1/2,n=1/2,"
        "inner=1,outer=1,pre=2,post=5/2,target=2,required=1/2,"
        "sqrt=1/2,margin=0,unimodular=True,critical=True,"
        "fixed_proved=False,square_function_proved=False,whole=False"
    )
    transition_h_poisson_proper = transition_h_poisson_line_audit(
        distance=F(3, 4),
        gcd_exponent=F(0),
    )
    print(
        "large_q_transition: h_poisson_line_slack="
        "theta=3/4,gamma=0,j=1/4,post=9/4,required=1/4,"
        "sqrt=1/2,margin=1/4 critical=False"
    )
    transition_h_poisson_maximal = transition_h_poisson_line_audit(
        distance=F(1),
        gcd_exponent=F(1, 2),
    )
    print(
        "large_q_transition: h_poisson_line_maximal_gcd="
        "theta=1,gamma=1/2,delta0=0,n=1,post=2,required=0,"
        "absolute_target=True,tapers_close=True"
    )
    transition_h_poisson_square = (
        transition_h_poisson_square_offdiagonal_audit()
    )
    print(
        "large_q_transition: h_poisson_square_offdiagonal="
        "slope_pair=1,inner=1,expanded=3,diagonal=2,target=2,"
        "required=1,Delta_max=1,cokernel=1,char_sqrt=1/2,"
        "entry_remaining=1/2,zero_is_diagonal=True,cramer=True,"
        "cyclic=True,four_mu=True,hybrid_proved=False,square_proved=False"
    )
    transition_published_kloosterman = (
        transition_published_kloosterman_entry_audit()
    )
    print(
        "large_q_transition: published_kloosterman_entry="
        "modulus=1,interval=1/2,required=1/2,"
        "bp=1/32,bp_deficit=15/32,mqw=1/100,mqw_deficit=49/100,"
        "pascadi=1/12,pascadi_deficit=5/12,four_bp=1/8,"
        "four_bp_deficit=3/8,sqrt_range=True,arbitrary=True,"
        "kernel=False,separable=False,fixed_modulus=False,"
        "pascadi_uniform=False,covered=False"
    )
    transition_delta_lattice = transition_delta_lattice_poisson_audit(
        determinant_exponent=F(1),
    )
    print(
        "large_q_transition: delta_lattice_poisson="
        "kappa=1,delta_area=1,covolume=1,zero_density=0,"
        "entry_shell=3,zero_absolute=3,target=2,required=1,"
        "dual_long_spacing=-1/2,dual_transverse_spacing=1/2,"
        "active_long=1/2,active_transverse=0,primitive_exact=True,"
        "primitive_layers_worse=False,zero_separable=False,"
        "jacobian=True,gram=True,psd=True,offdiag_subtract=True,"
        "kernel_zero=False,sufficient_only=True,"
        "zero_proved=False,whole=False"
    )
    transition_denominator_line = transition_denominator_gcd_line_audit(
        determinant_exponent=F(1),
        denominator_gcd_exponent=F(1, 2),
    )
    print(
        "large_q_transition: denominator_gcd_line="
        "kappa=1,gamma=1/2,denominator_pairs=3/2,h=1/2,n=1/2,"
        "raw=5/2,target=2,required=1/2,two_mu_length=1,"
        "two_mu_sqrt=1/2,post=2,margin=0,mobius_exact=True,"
        "critical=True,two_mu_proved=False,covered=False"
    )
    transition_denominator_type_ii = (
        transition_denominator_mobius_type_ii_audit(
            determinant_exponent=F(1),
            denominator_gcd_exponent=F(1, 2),
            left_short_mobius_exponent=F(0),
            left_cutoff_divisor_exponent=F(0),
            right_short_mobius_exponent=F(0),
            right_cutoff_divisor_exponent=F(0),
        )
    )
    print(
        "large_q_transition: denominator_type_ii_polytope="
        "kappa=1,gamma=1/2,alpha=1/2,cutoff=1/4,"
        "signed_volume=0,signed_sqrt=0,unsigned_left=1/2,"
        "unsigned_right=1/2,required=1/2,completion=1/2,"
        "identity=True,signed_proved=False,completion_proved=False,"
        "covered=False"
    )
    transition_bourgain_garaev = (
        transition_bourgain_garaev_multilinear_audit()
    )
    print(
        "large_q_transition: bourgain_garaev_multilinear="
        "modulus=1,atom=1/4,n=4,required=1/2,"
        "thm9=1/16,deficit9=7/16,thm10=1/24,deficit10=11/24,"
        "thm11_nmin=7,product=True,count=False,section10_4_Cmin=144,"
        "published_C=4,thm12_threshold=1/4,thm12_length=False,"
        "thm13_product=1,thm13_threshold=1/2,thm13_margin=1/2,"
        "thm13_product_holds=True,thm13_explicit=False,"
        "thm13_half_power=False,prime_required=True,all_prime=False,"
        "product_intervals=False,separable=False,phase=False,covered=False"
    )
    transition_bourgain_garaev_iterated = (
        transition_bourgain_garaev_iterated_factorization_audit()
    )
    print(
        "large_q_transition: bourgain_garaev_iterated="
        "atom=1/4,subatoms=2,subatom=1/8,formal_n=8,nmin=7,"
        "formal_count=True,formal_product=True,thm11_half_power=False,"
        "prime_balanced=False,"
        "forces_seven=False,phase=False,all_prime=False,covered=False"
    )
    transition_mobius_hecke = transition_mobius_hecke_reciprocal_l_audit()
    print(
        "large_q_transition: mobius_hecke_reciprocal_l="
        "line=1/2,required=1/2,k_first_degree=3,local_exact=True,"
        "k_converges=True,balanced_exact=True,L_factors=2,zeta_factors=3,"
        "balanced_k_first_degree=3,hecke_index_shift=True,"
        "mobius_entries_not_indices=True,conditional=True,"
        "kuznetsov=False,negative_moment=False,"
        "half_power=False,covered=False"
    )
    transition_entry_relative_trace = (
        transition_entry_weighted_relative_trace_audit(prime_bound=7)
    )
    print(
        "large_q_transition: entry_weighted_relative_trace="
        "prime_bound=7,primes=2,3,5,7,level=210,log_level_scale=1,"
        "primorial=True,spherical_constant=True,entry_noninvariant=True,"
        "depth2=True,hecke_index_shift=True,polynomial=False,"
        "published=False,covered=False"
    )
    transition_small_prime_hybrid = transition_small_prime_spectral_hybrid_audit(
        fixed_rough_factor_cap=7,
        polynomial_level_exponent=F(2),
    )
    print(
        "large_q_transition: small_prime_spectral_hybrid="
        "factor_cap=7,fixed_cutoff=1/8,level_exponent=2,required=1/2,"
        "rough_power=0,deficit=1/2,log_cutoff_polynomial=True,"
        "log_cutoff_fixed_count=False,fixed_count_superpoly=True,"
        "published=False,covered=False"
    )
    transition_general_cutoff = transition_general_cutoff_line_gate_audit(
        determinant_exponent=F(1),
        denominator_gcd_exponent=F(1, 2),
        cutoff_ratio=F(2, 3),
        type_split_ratio=F(1, 4),
        left_cutoff_divisor_exponent=F(1, 3),
        left_short_mobius_exponent=F(1, 7),
        right_cutoff_divisor_exponent=F(1, 4),
        right_short_mobius_exponent=F(1, 8),
    )
    print(
        "large_q_transition: general_cutoff_line_gate="
        "kappa=1,gamma=1/2,alpha=1/2,u=2/3,v=1/4,U=1/3,V=1/8,"
        "e_left=1/42,e_right=1/8,signed_sqrt=143/336,"
        "unsigned_sqrt=25/336,required=1/2,total=1/2,margin=0,"
        "identity=True,cutoff_slack=False,covered=False"
    )
    transition_bblr_hard = transition_bblr_quadratic_divisor_audit(
        denominator_gcd_exponent=F(0),
        left_signed_outer_exponent=F(0),
        right_signed_outer_exponent=F(0),
    )
    transition_bblr_subcritical = transition_bblr_quadratic_divisor_audit(
        denominator_gcd_exponent=F(4, 5),
        left_signed_outer_exponent=F(1, 5),
        right_signed_outer_exponent=F(1, 5),
    )
    print(
        "large_q_transition: bblr_quadratic_divisor="
        "hard:gamma=0,alpha=1,P=2,s1=0,s2=0,S=0,M=0,X=2,"
        "sharp=False,general1=5/2,h2=2,best=5/2,target=2,"
        "margin=-1/2,global_margin=-1/2;"
        "subcritical:gamma=4/5,alpha=1/5,P=6/5,s1=1/5,s2=1/5,"
        "S=2/5,M=1/5,X=1,sharp=True,e_ab=11/10,e_watt=23/20,"
        "best=23/20,target=6/5,margin=1/20,main=False,covered=False"
    )
    transition_bblr_unsigned_d0 = transition_bblr_hard_unsigned_cell_audit(
        poisson_gcd_exponent=F(0),
    )
    transition_bblr_unsigned_d1 = transition_bblr_hard_unsigned_cell_audit(
        poisson_gcd_exponent=F(1),
    )
    print(
        "large_q_transition: bblr_unsigned_recombination="
        "one=-1,four=1,outer_recombination=True;"
        f"lemma15:d0:z={_fmt(transition_bblr_unsigned_d0.lemma_3_1_z_exponent)},"
        f"x={_fmt(transition_bblr_unsigned_d0.x_interval_exponent)},"
        f"dcount={_fmt(transition_bblr_unsigned_d0.poisson_gcd_count_exponent)},"
        f"layer={_fmt(transition_bblr_unsigned_d0.dyadic_layer_exponent)};"
        f"d1:z={_fmt(transition_bblr_unsigned_d1.lemma_3_1_z_exponent)},"
        f"x={_fmt(transition_bblr_unsigned_d1.x_interval_exponent)},"
        f"dcount={_fmt(transition_bblr_unsigned_d1.poisson_gcd_count_exponent)},"
        f"layer={_fmt(transition_bblr_unsigned_d1.dyadic_layer_exponent)};"
        f"global={_fmt(transition_bblr_unsigned_d0.global_error_exponent)},"
        f"target={_fmt(transition_bblr_unsigned_d0.target_exponent)},"
        f"margin={_fmt(transition_bblr_unsigned_d0.power_margin)},"
        "improved=False"
    )
    transition_banks_shparlinski = (
        transition_banks_shparlinski_pre_cauchy_audit()
    )
    print(
        "large_q_transition: banks_shparlinski_pre_cauchy="
        f"entry={_fmt(transition_banks_shparlinski.entry_scale_exponent)},"
        f"v={_fmt(transition_banks_shparlinski.dual_v_exponent)},"
        f"j={_fmt(transition_banks_shparlinski.dual_j_exponent)},"
        "slopes="
        f"{_fmt(transition_banks_shparlinski.fixed_slope_family_exponent)},"
        "shift="
        f"{_fmt(transition_banks_shparlinski.shift_variable_exponent)},"
        "fixed_count="
        f"{_fmt(transition_banks_shparlinski.fixed_slope_geometric_count_exponent)},"
        "theorem="
        f"{_fmt(transition_banks_shparlinski.best_theorem_role_bound_exponent)},"
        "best="
        f"{_fmt(transition_banks_shparlinski.best_fixed_slope_bound_exponent)},"
        f"H={_fmt(transition_banks_shparlinski.h_poisson_factor_exponent)},"
        f"aggregate={_fmt(transition_banks_shparlinski.aggregated_exponent)},"
        f"target={_fmt(transition_banks_shparlinski.target_exponent)},"
        f"margin={_fmt(transition_banks_shparlinski.power_margin)},"
        "short_threshold="
        f"{_fmt(transition_banks_shparlinski.short_interval_threshold_exponent)},"
        "short_actual="
        f"{_fmt(transition_banks_shparlinski.actual_short_interval_exponent)},"
        "short_margin="
        f"{_fmt(transition_banks_shparlinski.short_interval_threshold_margin)},"
        "fix_slopes=True,shift_mu=False,convolution=True,"
        "convolution_power=False,hypotheses=False,covered=False"
    )
    transition_ramare_proper = transition_ramare_medium_prime_audit(
        entry_exponent=F(1),
        band_lower_exponent=F(1, 4),
        band_upper_exponent=F(3, 4),
    )
    transition_ramare_full = transition_ramare_medium_prime_audit(
        entry_exponent=F(1),
        band_lower_exponent=F(1, 4),
        band_upper_exponent=F(1),
    )
    print(
        "large_q_transition: ramare_medium_prime="
        f"proper:alpha={_fmt(transition_ramare_proper.entry_exponent)},"
        f"lower={_fmt(transition_ramare_proper.band_lower_exponent)},"
        f"upper={_fmt(transition_ramare_proper.band_upper_exponent)},"
        "required="
        f"{_fmt(transition_ramare_proper.required_line_saving_exponent)},"
        "prime_exception="
        f"{_fmt(transition_ramare_proper.prime_exceptional_set_exponent)},"
        "log_density="
        f"{_fmt(transition_ramare_proper.prime_exceptional_log_density_saving)},"
        "power_density="
        f"{_fmt(transition_ramare_proper.prime_exceptional_power_density_saving)},"
        f"deficit={_fmt(transition_ramare_proper.uncovered_power_deficit)},"
        "reaches=False,exceptional=True,in_sum=False;"
        f"full:upper={_fmt(transition_ramare_full.band_upper_exponent)},"
        "reaches=True,in_sum=True,prime_factor="
        f"{_fmt(transition_ramare_full.prime_sector_extracted_factor_exponent)},"
        "cofactor="
        f"{_fmt(transition_ramare_full.prime_sector_cofactor_exponent)},"
        "positive_factors="
        f"{transition_ramare_full.prime_sector_positive_length_factor_count},"
        "forces_two=False,covered=False"
    )
    transition_prime_kloosterman = transition_prime_kloosterman_audit()
    print(
        "large_q_transition: prime_kloosterman="
        f"q={_fmt(transition_prime_kloosterman.modulus_exponent)},"
        f"X={_fmt(transition_prime_kloosterman.prime_interval_exponent)},"
        "required="
        f"{_fmt(transition_prime_kloosterman.required_saving_exponent)},"
        "unrestricted_bound="
        f"{_fmt(transition_prime_kloosterman.unrestricted_prime_bound_exponent)},"
        "unrestricted_save="
        f"{_fmt(transition_prime_kloosterman.unrestricted_prime_saving_exponent)},"
        "progression_bound="
        f"{_fmt(transition_prime_kloosterman.progression_prime_bound_exponent)},"
        "progression_save="
        f"{_fmt(transition_prime_kloosterman.progression_prime_saving_exponent)},"
        "progression_modulus_cap="
        f"{_fmt(transition_prime_kloosterman.progression_modulus_cap_exponent)},"
        "four_unrestricted="
        f"{_fmt(transition_prime_kloosterman.optimistic_four_unrestricted_saving_exponent)},"
        "unrestricted_deficit="
        f"{_fmt(transition_prime_kloosterman.optimistic_four_unrestricted_deficit)},"
        "four_progression="
        f"{_fmt(transition_prime_kloosterman.optimistic_four_progression_saving_exponent)},"
        "progression_deficit="
        f"{_fmt(transition_prime_kloosterman.optimistic_four_progression_deficit)},"
        "fixed_prime=True,actual_prime=False,kernel=False,separable=False,"
        "covered=False"
    )
    exchange_audit = poisson_exchange_second_order_audit()
    print(
        "large_q_transition: poisson_exchange_second_order="
        "shift_conjugate="
        f"{exchange_audit.physical_shifted_sum_swap_is_conjugate},"
        "modulus_changes="
        f"{exchange_audit.poisson_modulus_changes_under_swap},"
        "reciprocity_correction="
        f"{exchange_audit.reciprocity_correction_retained},"
        "full_conjugate="
        f"{exchange_audit.full_poisson_term_swap_is_conjugate},"
        "coefficient_real="
        f"{exchange_audit.completed_coefficient_forced_real},"
        "linear_imaginary="
        f"{exchange_audit.imaginary_coefficient_has_linear_centered_term},"
        "real_required="
        f"{exchange_audit.second_order_bound_requires_real_coefficient},"
        "second_order="
        f"{exchange_audit.second_order_collar_unconditional}"
    )
    common_exchange = common_modulus_exchange_audit()
    print(
        "large_q_transition: common_modulus_exchange="
        f"Q={_fmt(common_exchange.common_modulus_exponent)},"
        f"craw={_fmt(common_exchange.raw_dual_c_exponent)},"
        f"vraw={_fmt(common_exchange.raw_dual_v_exponent)},"
        "original_divisor="
        f"{_fmt(common_exchange.original_gauss_support_divisor_exponent)},"
        "swapped_divisor="
        f"{_fmt(common_exchange.swapped_gauss_support_divisor_exponent)},"
        f"creduced={_fmt(common_exchange.reduced_dual_c_exponent)},"
        f"vreduced={_fmt(common_exchange.reduced_dual_v_exponent)},"
        "r_lattice="
        f"{common_exchange.original_frequency_sublattice_is_r_times_square},"
        "s_lattice="
        f"{common_exchange.swapped_frequency_sublattice_is_s_times_square},"
        "nonzero_intersection="
        f"{not common_exchange.nonzero_sublattice_intersection_empty_mod_rs},"
        "centered_zero="
        f"{common_exchange.centered_zero_frequency_annihilated},"
        "coefficient_real="
        f"{common_exchange.common_modulus_forces_real_completed_coefficient},"
        "conductor_reduced="
        f"{common_exchange.common_modulus_reduces_conductor},"
        "second_order="
        f"{common_exchange.second_order_collar_unconditional}"
    )
    midpoint_hermitian = midpoint_hermitian_completion_audit()
    print(
        "large_q_transition: midpoint_hermitian_completion="
        f"Q={_fmt(midpoint_hermitian.common_modulus_exponent)},"
        f"craw={_fmt(midpoint_hermitian.raw_dual_c_exponent)},"
        f"vraw={_fmt(midpoint_hermitian.raw_dual_v_exponent)},"
        f"ambient={_fmt(midpoint_hermitian.completed_ambient_exponent)},"
        f"prefactor={_fmt(midpoint_hermitian.completion_prefactor_exponent)},"
        f"target={_fmt(midpoint_hermitian.completed_gate_target_exponent)},"
        f"sqrt={_fmt(midpoint_hermitian.square_root_ambient_exponent)},"
        "allowance="
        f"{_fmt(midpoint_hermitian.allowance_beyond_square_root_exponent)},"
        f"unit={midpoint_hermitian.midpoint_coefficient_is_unit},"
        f"involution={midpoint_hermitian.midpoint_coefficient_is_involution},"
        "swap_negates="
        f"{midpoint_hermitian.exchange_negates_midpoint_coefficient},"
        "same_frequency="
        f"{midpoint_hermitian.same_frequency_swap_is_conjugate},"
        "row_centered="
        f"{midpoint_hermitian.centered_multiplier_zero_on_c_zero_row},"
        "column_centered="
        f"{midpoint_hermitian.centered_multiplier_zero_on_v_zero_column},"
        "small_phase="
        f"{midpoint_hermitian.modular_involution_phase_is_near_diagonal_small},"
        f"published={midpoint_hermitian.published_bound_verified}"
    )
    midpoint_published = midpoint_published_hermitian_adapter_audit()
    print(
        "large_q_transition: midpoint_published_hermitian_adapter="
        f"numerator={_fmt(midpoint_published.numerator_exponent)},"
        f"rs_trivial={_fmt(midpoint_published.rs_trivial_exponent)},"
        "claimed_inner="
        f"{_fmt(midpoint_published.withdrawn_claimed_outer_inner_bound_exponent)},"
        "claimed_save="
        f"{_fmt(midpoint_published.withdrawn_claimed_outer_inner_saving_exponent)},"
        "bulk_claimed_inner="
        f"{_fmt(midpoint_published.withdrawn_claimed_bulk_inner_bound_exponent)},"
        "bulk_save="
        f"{_fmt(midpoint_published.withdrawn_claimed_bulk_inner_saving_exponent)},"
        f"fixed_numerator={midpoint_published.theorem_has_moving_numerator},"
        "separated="
        f"{midpoint_published.theorem_accepts_joint_r_s_c_v_coefficient},"
        "frequency_average="
        f"{midpoint_published.theorem_supplies_c_v_frequency_average},"
        "withdrawn="
        f"{midpoint_published.claim_withdrawn_for_missing_l_squared_factor},"
        "corrected_improved="
        f"{midpoint_published.corrected_argument_gives_claimed_improvement},"
        f"closes={midpoint_published.withdrawn_claim_closes_midpoint_gate}"
    )
    midpoint_unitary = midpoint_unitary_divisor_audit()
    print(
        "large_q_transition: midpoint_unitary_divisor="
        f"n={_fmt(midpoint_unitary.product_variable_exponent)},"
        f"Q={_fmt(midpoint_unitary.root_modulus_exponent)},"
        "physical_numerator="
        f"{_fmt(midpoint_unitary.physical_numerator_exponent)},"
        f"dual_numerator={_fmt(midpoint_unitary.dual_numerator_exponent)},"
        "factorization_root_bijection="
        f"{midpoint_unitary.factorization_root_bijection_exact},"
        "mobius_collapses="
        f"{midpoint_unitary.mobius_product_collapses_to_single_mobius},"
        "root_count_subpower="
        f"{midpoint_unitary.root_multiplicity_is_subpower},"
        "balanced_filter="
        f"{midpoint_unitary.balanced_dyadic_condition_is_root_filter},"
        f"joint={midpoint_unitary.root_trace_coefficient_remains_joint},"
        f"published={midpoint_unitary.unitary_root_trace_bound_verified}"
    )
    root_farey = midpoint_root_farey_large_sieve_audit()
    print(
        "large_q_transition: root_farey_large_sieve="
        f"points={_fmt(root_farey.root_point_count_exponent)},"
        f"denominator={_fmt(root_farey.denominator_exponent)},"
        "spacing_reciprocal="
        f"{_fmt(root_farey.reciprocal_spacing_exponent)},"
        "physical_numerator="
        f"{_fmt(root_farey.physical_numerator_length_exponent)},"
        "physical_energy="
        f"{_fmt(root_farey.physical_product_energy_exponent)},"
        "physical_bound="
        f"{_fmt(root_farey.physical_large_sieve_bound_exponent)},"
        f"physical_target={_fmt(root_farey.physical_target_exponent)},"
        f"physical_deficit={_fmt(root_farey.physical_deficit_exponent)},"
        f"dual_numerator={_fmt(root_farey.dual_numerator_length_exponent)},"
        f"dual_energy={_fmt(root_farey.dual_product_energy_exponent)},"
        f"dual_bound={_fmt(root_farey.dual_large_sieve_bound_exponent)},"
        f"dual_target={_fmt(root_farey.dual_target_exponent)},"
        f"dual_deficit={_fmt(root_farey.dual_deficit_exponent)},"
        f"injective={root_farey.root_fractions_injective},"
        f"reduced={root_farey.root_fractions_reduced},"
        f"separated={root_farey.actual_joint_coefficient_is_separated},"
        f"closes={root_farey.root_farey_large_sieve_closes_gate}"
    )
    root_type_ii = midpoint_root_type_ii_audit()
    print(
        "large_q_transition: root_type_ii="
        f"product={_fmt(root_type_ii.product_exponent)},"
        f"left={_fmt(root_type_ii.left_factor_exponent)},"
        f"right={_fmt(root_type_ii.right_factor_exponent)},"
        "physical_numerator="
        f"{_fmt(root_type_ii.physical_numerator_exponent)},"
        f"dual_numerator={_fmt(root_type_ii.dual_numerator_exponent)},"
        f"crt={root_type_ii.generalized_crt_exact},"
        f"reciprocal_split={root_type_ii.reciprocal_phase_split_exact},"
        "left_cU="
        f"{root_type_ii.left_factor_has_truncated_divisor_coefficient},"
        f"right_mu={root_type_ii.right_factor_retains_mobius},"
        f"root_fibers_subpower={root_type_ii.root_fibers_are_subpower},"
        f"completed_centering={root_type_ii.completed_centering_exact},"
        f"zero_residue={root_type_ii.physical_zero_residue_vanishes},"
        "physical_subtraction="
        f"{root_type_ii.physical_centered_subtraction_present},"
        "fixed_numerator="
        f"{root_type_ii.published_hermitian_theorem_has_root_dependent_numerator},"
        f"joint={root_type_ii.actual_transform_coefficient_remains_joint},"
        f"published={root_type_ii.root_type_ii_bound_verified}"
    )
    root_four_factor = midpoint_root_four_factor_audit()
    print(
        "large_q_transition: root_four_factor="
        f"left_product={_fmt(root_four_factor.left_product_exponent)},"
        f"right_product={_fmt(root_four_factor.right_product_exponent)},"
        "physical_numerator="
        f"{_fmt(root_four_factor.physical_numerator_exponent)},"
        f"r={_fmt(root_four_factor.recovered_r_exponent)},"
        f"s={_fmt(root_four_factor.recovered_s_exponent)},"
        "roots_unfold="
        f"{root_four_factor.root_fibers_unfold_to_ordered_factorizations},"
        f"pairwise={root_four_factor.four_factors_are_pairwise_coprime},"
        "left_cU="
        f"{root_four_factor.truncated_divisor_coefficient_remains_on_left_product},"
        "right_mu_splits="
        f"{root_four_factor.mobius_splits_over_right_factors},"
        f"phase={root_four_factor.kloosterman_phase_identity_exact},"
        "completed_centering="
        f"{root_four_factor.completed_centering_exact},"
        f"zero_residue={root_four_factor.physical_zero_residue_vanishes},"
        "physical_subtraction="
        f"{root_four_factor.physical_centered_subtraction_present},"
        "extreme_hard="
        f"{root_four_factor.extreme_sector_recovers_hard_fraction},"
        f"joint={root_four_factor.actual_smooth_weight_remains_joint},"
        f"published={root_four_factor.four_factor_type_ii_bound_verified}"
    )
    physical_poisson = midpoint_physical_poisson_audit()
    print(
        "large_q_transition: midpoint_physical_poisson="
        f"Q={_fmt(physical_poisson.modulus_exponent)},"
        f"h={_fmt(physical_poisson.h_exponent)},"
        f"delta={_fmt(physical_poisson.delta_exponent)},"
        "resonance="
        f"{_fmt(physical_poisson.resonance_window_exponent)},"
        "lattice="
        f"{_fmt(physical_poisson.lattice_parameter_exponent)},"
        "pointwise="
        f"{_fmt(physical_poisson.pointwise_bilinear_bound_exponent)},"
        f"raw={_fmt(physical_poisson.raw_bilinear_exponent)},"
        "physical_save="
        f"{_fmt(physical_poisson.physical_oscillation_saving_exponent)},"
        "outer_points="
        f"{_fmt(physical_poisson.outer_root_point_exponent)},"
        f"outer_target={_fmt(physical_poisson.outer_target_exponent)},"
        "outer_required_save="
        f"{_fmt(physical_poisson.required_outer_saving_exponent)},"
        "lattice_exact="
        f"{physical_poisson.resonance_lattice_bijection_exact},"
        f"poisson_exact={physical_poisson.one_variable_poisson_exact},"
        "joint_derivatives="
        f"{physical_poisson.joint_weight_has_uniform_delta_derivatives},"
        "determinant_line="
        f"{physical_poisson.determinant_line_correspondence_exact},"
        "independent="
        f"{physical_poisson.physical_poisson_route_is_independent},"
        "outer_sqrt="
        f"{physical_poisson.outer_mobius_square_root_verified}"
    )
    root_salie = root_salie_adapter_audit()
    print(
        "large_q_transition: root_salie_adapter="
        f"modulus={_fmt(root_salie.modulus_exponent)},"
        f"numerator={_fmt(root_salie.physical_numerator_exponent)},"
        "fixed_k_bound="
        f"{_fmt(root_salie.fixed_numerator_bound_exponent)},"
        "fixed_k_save="
        f"{_fmt(root_salie.fixed_numerator_saving_exponent)},"
        "summed_k_bound="
        f"{_fmt(root_salie.absolute_numerator_sum_bound_exponent)},"
        f"target={_fmt(root_salie.physical_target_exponent)},"
        "deficit="
        f"{_fmt(root_salie.absolute_numerator_sum_deficit_exponent)},"
        "odd_trace_exact="
        f"{root_salie.odd_full_root_trace_identity_exact},"
        "even_branch="
        f"{root_salie.even_midpoint_modulus_adapter_verified},"
        "balanced_filter="
        f"{root_salie.theorem_accepts_balanced_root_filter},"
        "mobius_modulus="
        f"{root_salie.theorem_accepts_mobius_modulus_weight},"
        "fixed_numerator="
        f"{root_salie.theorem_accepts_moving_numerator},"
        "square_exception="
        f"{root_salie.square_numerator_exception_covered},"
        "joint="
        f"{root_salie.theorem_accepts_joint_transform_weight},"
        f"closes={root_salie.salie_adapter_closes_root_gate}"
    )
    salie_joint = root_salie_joint_average_audit()
    print(
        "large_q_transition: root_salie_joint="
        f"m={_fmt(salie_joint.left_root_factor_exponent)},"
        f"n={_fmt(salie_joint.right_root_factor_exponent)},"
        f"numerator={_fmt(salie_joint.physical_numerator_exponent)},"
        f"bc1={_fmt(salie_joint.bcr_term_1_exponent)},"
        f"bc2={_fmt(salie_joint.bcr_term_2_exponent)},"
        f"bound={_fmt(salie_joint.bcr_bound_exponent)},"
        f"target={_fmt(salie_joint.physical_target_exponent)},"
        f"deficit={_fmt(salie_joint.bcr_deficit_exponent)},"
        "square_pairs="
        f"{_fmt(salie_joint.square_product_pair_count_exponent)},"
        "dfi_y="
        f"{_fmt(salie_joint.dfi_square_main_short_factor_cutoff_exponent)},"
        "dfi_z="
        f"{_fmt(salie_joint.dfi_long_long_cutoff_exponent)},"
        "balanced="
        f"{_fmt(salie_joint.balanced_root_factor_exponent)},"
        "fixed_square="
        f"{_fmt(salie_joint.fixed_square_hermitian_bound_exponent)},"
        "square_bound="
        f"{_fmt(salie_joint.absolute_square_family_bound_exponent)},"
        "square_deficit="
        f"{_fmt(salie_joint.absolute_square_family_deficit_exponent)},"
        "phase="
        f"{salie_joint.salie_factorization_matches_midpoint_phase},"
        "bcr_endpoint="
        f"{salie_joint.joint_average_is_existing_bcr_endpoint},"
        "mobius_coefficients="
        f"{salie_joint.bcr_accepts_mobius_coefficients},"
        "mobius_beyond_l2="
        f"{salie_joint.bcr_uses_mobius_beyond_l2},"
        "dfi_main_excluded="
        f"{salie_joint.balanced_root_filter_excludes_dfi_square_main},"
        f"closes={salie_joint.joint_salie_route_closes_root_gate}"
    )
    salie_gauss = square_salie_gauss_completion_audit()
    print(
        "large_q_transition: square_salie_gauss="
        f"r={_fmt(salie_gauss.r_exponent)},"
        f"s={_fmt(salie_gauss.s_exponent)},"
        f"t={_fmt(salie_gauss.square_root_exponent)},"
        f"x={_fmt(salie_gauss.x_exponent)},"
        f"y={_fmt(salie_gauss.y_exponent)},"
        "normalization="
        f"{_fmt(salie_gauss.gauss_normalization_exponent)},"
        "resonance="
        f"{_fmt(salie_gauss.t_poisson_resonance_exponent)},"
        "localized_pointwise="
        f"{_fmt(salie_gauss.localized_pointwise_exponent)},"
        "direct_square="
        f"{_fmt(salie_gauss.direct_square_sector_pointwise_exponent)},"
        f"identity={salie_gauss.double_gauss_identity_exact},"
        "character_mod8="
        f"{salie_gauss.cross_character_depends_only_on_mod8},"
        "t_linear="
        f"{salie_gauss.square_root_variable_is_linearized},"
        f"joint={salie_gauss.remaining_quadratic_weight_is_joint},"
        "improves="
        f"{salie_gauss.gauss_completion_improves_square_sector},"
        f"closes={salie_gauss.square_salie_gauss_route_closes_gate}"
    )
    mobius_product_shift = mobius_product_shifted_variance_audit()
    print(
        "large_q_transition: mobius_product_shifted_variance="
        f"factor={_fmt(mobius_product_shift.factor_length_exponent)},"
        f"product={_fmt(mobius_product_shift.product_length_exponent)},"
        f"shift={_fmt(mobius_product_shift.transform_shift_exponent)},"
        "diagonal_power="
        f"{_fmt(mobius_product_shift.diagonal_power_exponent)},"
        "diagonal_log="
        f"{_fmt(mobius_product_shift.diagonal_logarithmic_exponent)},"
        "raw_offdiag="
        f"{_fmt(mobius_product_shift.raw_shifted_determinant_exponent)},"
        "target="
        f"{_fmt(mobius_product_shift.shifted_determinant_target_exponent)},"
        "required="
        f"{_fmt(mobius_product_shift.required_shifted_determinant_saving_exponent)},"
        "convolution="
        f"{mobius_product_shift.product_convolution_identity_exact},"
        "diagonal="
        f"{mobius_product_shift.diagonal_parameterization_exact},"
        f"tail={mobius_product_shift.schwartz_tail_is_power_negligible},"
        "collar="
        f"{mobius_product_shift.polylogarithmic_transition_collar_retained},"
        "m4_equivalent="
        f"{mobius_product_shift.equivalent_to_separated_mixed_fourth_moment_gate},"
        "bound="
        f"{mobius_product_shift.shifted_mobius_determinant_bound_proved},"
        "original_requires="
        f"{mobius_product_shift.original_signed_kernel_requires_component_gate},"
        f"closes={mobius_product_shift.route_closes_mwkf_gate}"
    )
    gg_determinant = ganguly_guria_determinant_audit()
    print(
        "large_q_transition: ganguly_guria_determinant="
        f"X={_fmt(gg_determinant.variable_length_exponent)},"
        f"shift={_fmt(gg_determinant.shift_range_exponent)},"
        f"theta={_fmt(gg_determinant.ramanujan_exponent)},"
        f"fixed_error={_fmt(gg_determinant.fixed_shift_error_exponent)},"
        "absolute_shift_sum="
        f"{_fmt(gg_determinant.absolute_shift_sum_error_exponent)},"
        f"target={_fmt(gg_determinant.shifted_determinant_target_exponent)},"
        "deficit="
        f"{_fmt(gg_determinant.absolute_shift_sum_power_deficit)},"
        f"fixed_main={_fmt(gg_determinant.fixed_shift_main_exponent)},"
        f"absolute_main={_fmt(gg_determinant.absolute_shift_sum_main_exponent)},"
        "smooth="
        f"{gg_determinant.smooth_unweighted_fixed_shift_theorem_proved},"
        "distinct="
        f"{gg_determinant.distinct_tensor_weights_accepted_as_stated},"
        "arithmetic="
        f"{gg_determinant.arithmetic_coefficients_accepted},"
        "coefficient_uniform="
        f"{gg_determinant.coefficient_form_uniformity_quantified},"
        f"type_i_ii={gg_determinant.mobius_type_i_ii_adapter_proved},"
        "ramanujan_power="
        f"{gg_determinant.ramanujan_conjecture_removes_power_deficit},"
        "ramanujan_log="
        f"{gg_determinant.ramanujan_conjecture_supplies_logarithmic_saving},"
        "main_cancel="
        f"{gg_determinant.mobius_main_term_cancellation_proved},"
        f"closes={gg_determinant.ganguly_guria_route_closes_mobius_gate}"
    )
    dd_variance = darbar_das_short_variance_audit()
    print(
        "large_q_transition: darbar_das_short_variance="
        f"ambient={_fmt(dd_variance.ambient_length_exponent)},"
        f"window={_fmt(dd_variance.short_window_exponent)},"
        "generic_variance="
        f"{_fmt(dd_variance.generic_short_variance_exponent)},"
        "target_variance="
        f"{_fmt(dd_variance.required_short_variance_exponent)},"
        f"required={_fmt(dd_variance.required_variance_saving_exponent)},"
        "full_series_zeta_power="
        f"{dd_variance.full_mobius_convolution_zeta_power},"
        "auxiliary_zeta_power="
        f"{dd_variance.required_auxiliary_zeta_power},"
        f"h_p={dd_variance.required_auxiliary_prime_coefficient},"
        "h_p2="
        f"{dd_variance.required_auxiliary_prime_square_coefficient},"
        "h_p3="
        f"{dd_variance.required_auxiliary_prime_cube_coefficient},"
        f"m_class={dd_variance.auxiliary_fits_squarefree_m_class},"
        f"g_class={dd_variance.auxiliary_fits_completely_multiplicative_g_class},"
        "restricted_multiplicative="
        f"{dd_variance.restricted_convolution_is_multiplicative},"
        "full_convolution="
        f"{dd_variance.published_theorem_covers_full_mobius_convolution},"
        "restricted_convolution="
        f"{dd_variance.published_theorem_covers_restricted_convolution},"
        f"closes={dd_variance.darbar_das_route_closes_mobius_gate}"
    )
    ratio_mellin = restricted_mobius_ratio_mellin_audit()
    print(
        "large_q_transition: restricted_mobius_ratio_mellin="
        f"factor={_fmt(ratio_mellin.factor_length_exponent)},"
        f"product={_fmt(ratio_mellin.product_length_exponent)},"
        f"window={_fmt(ratio_mellin.short_window_exponent)},"
        "variance_target="
        f"{_fmt(ratio_mellin.required_short_variance_exponent)},"
        "ratio_coordinates="
        f"{ratio_mellin.ratio_coordinate_identity_exact},"
        f"inversion={ratio_mellin.ratio_fourier_inversion_exact},"
        "multiplicative="
        f"{ratio_mellin.integrand_coefficient_is_multiplicative},"
        "dirichlet_series="
        f"{ratio_mellin.shifted_inverse_zeta_dirichlet_series_exact},"
        f"outer_smooth={ratio_mellin.product_coordinate_weight_is_smooth},"
        f"tau_decay={ratio_mellin.ratio_transform_is_rapidly_decaying},"
        "tau_uniform_sufficient="
        f"{ratio_mellin.uniform_single_tau_variance_is_sufficient},"
        f"tau_zero_full={ratio_mellin.tau_zero_is_full_mobius_convolution},"
        "tau_zero_pole="
        f"{ratio_mellin.tau_zero_square_dirichlet_series_zeta_pole_order},"
        f"diag_log={ratio_mellin.tau_zero_diagonal_log_exponent},"
        f"target_log={ratio_mellin.required_diagonal_log_exponent},"
        f"excess={ratio_mellin.tau_zero_formal_diagonal_log_excess},"
        "euler_no_p="
        f"{ratio_mellin.tau_zero_euler_remainder_has_no_prime_term},"
        "euler_half="
        f"{ratio_mellin.tau_zero_euler_remainder_converges_for_real_part_gt_half},"
        "needs_offdiag="
        f"{ratio_mellin.tau_zero_diagonal_excess_requires_offdiagonal_cancellation},"
        "diagonal_lower="
        f"{not ratio_mellin.diagonal_term_is_not_lower_bound_for_full_variance},"
        "diagonal_disproves="
        f"{ratio_mellin.tau_zero_diagonal_alone_disproves_uniform_gate},"
        "joint_diag_log1="
        f"{ratio_mellin.joint_ratio_recombination_has_restricted_diagonal_log_order_one},"
        "mangerel="
        f"{_fmt(ratio_mellin.optimistic_mangerel_variance_exponent)},"
        "mangerel_deficit="
        f"{_fmt(ratio_mellin.mangerel_power_deficit)},"
        "mangerel_log="
        f"{ratio_mellin.mangerel_only_supplies_logarithmic_saving},"
        "tau_hypotheses="
        f"{ratio_mellin.uniform_tau_mangerel_hypotheses_verified},"
        f"published={ratio_mellin.shifted_inverse_zeta_variance_proved},"
        f"closes={ratio_mellin.ratio_mellin_route_closes_mobius_gate}"
    )
    brz = basak_robles_zaharescu_mobius_convolution_audit()
    print(
        "large_q_transition: brz_mobius_convolution="
        f"ambient={_fmt(brz.ambient_length_exponent)},"
        f"window={_fmt(brz.short_window_exponent)},"
        f"critical_q={_fmt(brz.critical_denominator_exponent)},"
        f"term1={_fmt(brz.first_pointwise_term_exponent)},"
        f"term2={_fmt(brz.second_pointwise_term_exponent)},"
        f"term3={_fmt(brz.third_pointwise_term_exponent)},"
        f"best={_fmt(brz.best_published_pointwise_exponent)},"
        f"required={_fmt(brz.required_pointwise_exponent)},"
        f"pointwise_deficit={_fmt(brz.pointwise_exponent_deficit)},"
        "local_variance="
        f"{_fmt(brz.direct_local_arc_variance_exponent)},"
        "variance_target="
        f"{_fmt(brz.required_local_variance_exponent)},"
        "variance_deficit="
        f"{_fmt(brz.local_arc_variance_deficit)},"
        "major_variance="
        f"{_fmt(brz.major_arc_direct_variance_exponent)},"
        f"major_deficit={_fmt(brz.major_arc_power_deficit)},"
        "published="
        f"{brz.published_full_mobius_convolution_pointwise_bound},"
        f"twisted={brz.published_ratio_twisted_family_bound},"
        f"local_l2={brz.published_local_l2_bound},"
        "closes="
        f"{brz.brz_direct_pointwise_route_closes_variance_gate}"
    )
    zero_free = inverse_zeta_variance_zero_free_audit()
    print(
        "large_q_transition: inverse_zeta_zero_free_implication="
        f"ambient={_fmt(zero_free.ambient_length_exponent)},"
        f"window={_fmt(zero_free.short_window_exponent)},"
        f"variance={_fmt(zero_free.variance_bound_exponent)},"
        "block="
        f"{_fmt(zero_free.dyadic_coefficient_block_exponent)},"
        "abscissa="
        f"{_fmt(zero_free.implied_dyadic_convergence_abscissa)},"
        f"x_integral={zero_free.x_integration_identity_exact},"
        f"cauchy={zero_free.cauchy_schwarz_exponent_exact},"
        f"dyadic={zero_free.dyadic_continuation_argument_exact},"
        "zero_free="
        f"{zero_free.implies_zeta_zero_free_real_part_gt_three_quarters},"
        "original_necessary="
        f"{zero_free.original_mwkf_asymptotic_requires_this_gate},"
        "available="
        f"{zero_free.inverse_zeta_variance_gate_available_unconditionally}"
    )
    unsigned_h_poisson = bblr_h_poisson_unsigned_hard_box_audit()
    print(
        "large_q_transition: bblr_h_poisson_unsigned="
        f"old={_fmt(unsigned_h_poisson.old_weil_bound_exponent)},"
        f"new={_fmt(unsigned_h_poisson.h_poisson_bound_exponent)},"
        f"target={_fmt(unsigned_h_poisson.local_target_exponent)},"
        f"saving={_fmt(unsigned_h_poisson.recovered_power_saving)},"
        "h_modulus="
        f"{unsigned_h_poisson.h_length_matches_reduced_modulus},"
        f"poisson={unsigned_h_poisson.h_poisson_identity_exact},"
        "inverse_removed="
        f"{unsigned_h_poisson.inverse_fraction_becomes_linear_congruence},"
        "gcd_sum="
        f"{unsigned_h_poisson.weighted_gcd_sum_is_diagonal_scale},"
        "positive_d_tail="
        f"{unsigned_h_poisson.positive_gcd_layers_are_power_negligible},"
        "approximation="
        f"{_fmt(unsigned_h_poisson.approximation_error_exponent)},"
        "power_closed="
        f"{unsigned_h_poisson.all_unsigned_hard_box_power_closed},"
        "log_closed="
        f"{unsigned_h_poisson.global_logarithmic_little_o_closed},"
        f"whole_face={unsigned_h_poisson.whole_signed_hard_face_covered}"
    )
    signed_h_poisson = bblr_h_poisson_signed_cell_audit(
        outer_scale_exponent=F(1, 4),
    )
    print(
        "large_q_transition: bblr_h_poisson_signed_boundary="
        f"s={_fmt(signed_h_poisson.outer_scale_exponent)},"
        "large_inner="
        f"{_fmt(signed_h_poisson.large_inner_factor_exponent)},"
        "small_inner="
        f"{_fmt(signed_h_poisson.small_inner_factor_exponent)},"
        f"shift={_fmt(signed_h_poisson.transformed_shift_exponent)},"
        "side="
        f"{_fmt(signed_h_poisson.transformed_side_product_exponent)},"
        "raw="
        f"{_fmt(signed_h_poisson.transformed_raw_count_exponent)},"
        "required="
        f"{_fmt(signed_h_poisson.transformed_required_bound_exponent)},"
        "saving="
        f"{_fmt(signed_h_poisson.required_outer_mobius_saving)},"
        "prefactor="
        f"{_fmt(signed_h_poisson.h_poisson_prefactor_exponent)},"
        "error1="
        f"{_fmt(signed_h_poisson.first_total_bblr_error_exponent)},"
        "error2="
        f"{_fmt(signed_h_poisson.second_total_bblr_error_exponent)},"
        f"target={_fmt(signed_h_poisson.global_target_exponent)},"
        f"margin={_fmt(signed_h_poisson.power_margin)},"
        "diagonal_reduction="
        f"{signed_h_poisson.dyadic_cross_terms_reduce_to_diagonal_norms},"
        f"sharp={signed_h_poisson.transformed_bblr_sharp_condition_holds},"
        "published_upper="
        f"{_fmt(signed_h_poisson.published_bblr_power_coverage_upper)},"
        "boundary_log="
        f"{signed_h_poisson.boundary_logarithmic_little_o_closed},"
        "residual_lower="
        f"{_fmt(signed_h_poisson.signed_residual_lower_exponent)},"
        "residual_upper="
        f"{_fmt(signed_h_poisson.signed_residual_upper_exponent)},"
        f"whole_face={signed_h_poisson.whole_signed_hard_face_covered}"
    )
    signed_dual = signed_dual_convolution_audit(
        outer_atom_exponent=F(1, 2),
    )
    print(
        "large_q_transition: signed_dual_convolution="
        f"outer={_fmt(signed_dual.outer_atom_exponent)},"
        f"dual={_fmt(signed_dual.h_poisson_dual_exponent)},"
        f"product={_fmt(signed_dual.product_variable_exponent)},"
        f"signed_atoms={signed_dual.signed_atom_count},"
        f"collapse={signed_dual.signed_dual_product_collapse_exact},"
        "survivor="
        f"{'mobius' if signed_dual.collapsed_coefficient_is_one_mobius else 'none'},"
        f"cutoff={signed_dual.cutoff_condition_retained_exactly},"
        "product_weight="
        f"{signed_dual.actual_transformed_weight_product_compatible},"
        f"ratio_mellin={signed_dual.ratio_mellin_family_required},"
        f"published={signed_dual.weighted_collapse_bound_proved},"
        f"whole_face={signed_dual.whole_signed_hard_face_covered}"
    )
    ratio_type_ii = coupled_ratio_mellin_type_ii_gate_audit(
        outer_scale_exponent=F(1),
    )
    print(
        "large_q_transition: coupled_ratio_mellin_type_ii_endpoint="
        f"s={_fmt(ratio_type_ii.outer_scale_exponent)},"
        f"long={_fmt(ratio_type_ii.long_mobius_variable_exponent)},"
        "collapsed="
        f"{_fmt(ratio_type_ii.collapsed_product_variable_exponent)},"
        f"shift={_fmt(ratio_type_ii.shift_exponent)},"
        "ambient="
        f"{_fmt(ratio_type_ii.convolution_ambient_exponent)},"
        "modulus="
        f"{_fmt(ratio_type_ii.progression_modulus_exponent)},"
        "level="
        f"{_fmt(ratio_type_ii.modulus_level_relative_to_ambient)},"
        f"raw={_fmt(ratio_type_ii.raw_shifted_count_exponent)},"
        "target="
        f"{_fmt(ratio_type_ii.required_inner_bound_exponent)},"
        "required="
        f"{_fmt(ratio_type_ii.required_cancellation_exponent)},"
        "two_coeff_sqrt="
        f"{_fmt(ratio_type_ii.two_collapsed_coefficients_square_root_saving)},"
        f"margin={_fmt(ratio_type_ii.square_root_power_margin)},"
        "bv_range="
        f"{ratio_type_ii.modulus_within_bombieri_vinogradov_level},"
        "fixed_shift="
        f"{ratio_type_ii.fixed_shift_dispersion_suffices_after_shift_sum},"
        "quotient_mobius="
        f"{ratio_type_ii.quotient_mobius_prevents_direct_bv},"
        "coupled_shift="
        f"{ratio_type_ii.full_shift_average_must_remain_coupled},"
        "coprime_allocation="
        f"{ratio_type_ii.coprimality_prime_allocation_required},"
        f"four_variable={ratio_type_ii.four_variable_reduction_exact},"
        "published="
        f"{ratio_type_ii.coupled_ratio_mellin_type_ii_bound_proved},"
        f"whole_face={ratio_type_ii.whole_signed_hard_face_covered}"
    )
    coprime_allocation = collapsed_coprimality_allocation_audit()
    print(
        "large_q_transition: collapsed_coprimality_allocation="
        "cross_conditions="
        f"{coprime_allocation.cross_coprimality_condition_count},"
        "allocation_divisors="
        f"{coprime_allocation.mobius_allocation_divisor_count},"
        f"identity={coprime_allocation.product_gcd_factorization_exact},"
        f"finite={coprime_allocation.allocation_is_finite_reindexing},"
        "power_loss="
        f"{_fmt(coprime_allocation.positive_power_loss_exponent)},"
        "log_loss="
        f"{_fmt(coprime_allocation.registered_logarithmic_loss)},"
        "superposition="
        f"{coprime_allocation.four_variable_superposition_exact},"
        "independent="
        f"{coprime_allocation.collapsed_coefficients_independent_of_long_variables},"
        "bv="
        f"{coprime_allocation.standard_bombieri_vinogradov_adapter_applies},"
        "type_ii="
        f"{coprime_allocation.coupled_ratio_mellin_type_ii_bound_proved},"
        f"whole_face={coprime_allocation.whole_signed_hard_face_covered}"
    )
    chowla_face = collapsed_chowla_face_audit(
        outer_scale_exponent=F(1),
    )
    print(
        "large_q_transition: collapsed_chowla_face_endpoint="
        f"s={_fmt(chowla_face.outer_scale_exponent)},"
        f"long={_fmt(chowla_face.long_mobius_variable_exponent)},"
        "collapsed="
        f"{_fmt(chowla_face.collapsed_product_variable_exponent)},"
        f"face_raw={_fmt(chowla_face.equal_face_raw_exponent)},"
        "target="
        f"{_fmt(chowla_face.required_inner_bound_exponent)},"
        f"margin={_fmt(chowla_face.positive_power_margin)},"
        f"equal_face={chowla_face.equal_collapsed_product_face_present},"
        "fixed_shift="
        f"{chowla_face.determinant_reduces_to_fixed_shift},"
        f"primitive_excludes={chowla_face.primitive_gcd_excludes_face},"
        "zero_ratio_mobius="
        f"{chowla_face.pointwise_zero_ratio_coefficient_is_mobius},"
        f"chowla={chowla_face.face_contains_two_point_chowla},"
        "ordinary_chowla="
        f"{chowla_face.ordinary_two_point_chowla_available_unconditionally},"
        f"log_little_o={chowla_face.logarithmic_little_o_required},"
        "pointwise_triangle="
        f"{chowla_face.uniform_ratio_frequency_triangle_gate_admissible},"
        f"joint_ratio={chowla_face.joint_ratio_integral_must_remain_coupled},"
        f"type_ii={chowla_face.coupled_ratio_mellin_type_ii_bound_proved},"
        f"whole_face={chowla_face.whole_signed_hard_face_covered}"
    )
    physical_ratio = physical_joint_ratio_recombination_audit()
    print(
        "large_q_transition: physical_joint_ratio_recombination="
        "finite_kernel="
        f"{physical_ratio.ratio_mellin_recombines_to_finite_divisor_kernel},"
        "equal_face_nonzero="
        f"{physical_ratio.primitive_equal_face_coefficient_can_be_nonzero},"
        f"witness={physical_ratio.witness_equal_face_coefficient},"
        "joint_mellin_annihilates="
        f"{physical_ratio.joint_ratio_integration_alone_annihilates_chowla_face},"
        "arbitrary_weight="
        f"{physical_ratio.arbitrary_smooth_weight_enlargement_admissible},"
        "allocation_triangle="
        f"{physical_ratio.allocationwise_triangle_inequality_admissible},"
        "face_separate="
        f"{physical_ratio.equal_face_separate_bound_available_unconditionally},"
        "full_outer_coupling="
        f"{physical_ratio.full_outer_scale_and_kernel_sum_must_remain_coupled},"
        "centered_dispersion="
        f"{physical_ratio.centered_coupled_dispersion_bound_proved},"
        f"whole_face={physical_ratio.whole_signed_hard_face_covered}"
    )
    gcd_layer = collapsed_gcd_layer_centered_kernel_audit(
        collapsed_exponent=F(1),
        gcd_exponent=F(3, 5),
    )
    print(
        "large_q_transition: collapsed_gcd_centered_kernel="
        f"s={_fmt(gcd_layer.collapsed_exponent)},"
        f"gamma={_fmt(gcd_layer.gcd_exponent)},"
        f"A={_fmt(gcd_layer.cofactor_exponent)},"
        f"raw={_fmt(gcd_layer.raw_dyadic_layer_exponent)},"
        f"target={_fmt(gcd_layer.global_target_exponent)},"
        f"saving={_fmt(gcd_layer.required_saving_exponent)},"
        f"inner_target={_fmt(gcd_layer.fourier_inner_target_exponent)},"
        f"diagonal_killed={gcd_layer.product_diagonal_annihilated_exactly},"
        f"centered={gcd_layer.constant_fourier_mode_centered_exactly},"
        f"full_g={gcd_layer.full_g_sum_retained},"
        "full_allocation_ratio="
        f"{gcd_layer.full_allocation_and_ratio_sum_retained},"
        "pointwise_chowla="
        f"{gcd_layer.pointwise_fixed_affine_chowla_bound_assumed},"
        "published_average="
        f"{gcd_layer.published_averaged_chowla_adapter_applies},"
        f"dispersion={gcd_layer.centered_coupled_dispersion_bound_proved},"
        f"whole_face={gcd_layer.whole_signed_hard_face_covered}"
    )
    equal_product_pnt = top_equal_product_outer_pnt_audit()
    print(
        "large_q_transition: top_equal_product_outer_pnt="
        f"atom={_fmt(equal_product_pnt.signed_atom_exponent)},"
        f"q={_fmt(equal_product_pnt.poisson_quotient_exponent)},"
        f"outer={_fmt(equal_product_pnt.outer_pair_raw_exponent)},"
        "long="
        f"{_fmt(equal_product_pnt.long_correlation_trivial_exponent)},"
        f"raw={_fmt(equal_product_pnt.face_raw_exponent)},"
        f"target={_fmt(equal_product_pnt.face_target_exponent)},"
        f"margin={_fmt(equal_product_pnt.power_margin)},"
        "factorization="
        f"{equal_product_pnt.primitive_equal_product_factorization_exact},"
        "interval_convolution="
        f"{equal_product_pnt.signed_atom_interval_convolution_exact},"
        f"balanced={equal_product_pnt.balanced_cutoff_ratios_verified},"
        "coprime_pnt="
        f"{equal_product_pnt.uniform_coprime_pnt_log_saving_available},"
        "euler_polylog="
        f"{equal_product_pnt.coprime_euler_factor_loss_only_polylogarithmic},"
        "trivial_long="
        f"{equal_product_pnt.long_mobius_correlation_used_only_trivially},"
        "fixed_chowla="
        f"{equal_product_pnt.fixed_affine_chowla_estimate_required},"
        "face_closed="
        f"{equal_product_pnt.top_equal_product_face_closed_unconditionally},"
        f"whole_face={equal_product_pnt.whole_signed_hard_face_covered}"
    )
    polylog_collar = polylog_gcd_collar_outer_pnt_audit(
        polylog_depth=5,
    )
    print(
        "large_q_transition: polylog_gcd_collar_outer_pnt="
        f"K={polylog_collar.polylog_depth},"
        f"A={_fmt(polylog_collar.cofactor_power_exponent)},"
        f"cross={_fmt(polylog_collar.cross_gcd_power_exponent)},"
        f"q={_fmt(polylog_collar.poisson_quotient_power_exponent)},"
        f"required={_fmt(polylog_collar.required_power_saving_exponent)},"
        "factorization="
        f"{polylog_collar.primitive_unequal_product_factorization_exact},"
        "cross_identity="
        f"{polylog_collar.cross_gcd_product_identity_exact},"
        "divisible_coprime_pnt="
        f"{polylog_collar.prescribed_divisibility_coprime_pnt_available},"
        "absorbs_polylog="
        f"{polylog_collar.arbitrary_log_saving_absorbs_polylog_variables},"
        "trivial_long="
        f"{polylog_collar.long_affine_mobius_sum_used_only_trivially},"
        "collar_closed="
        f"{polylog_collar.polylog_gcd_collar_closed_unconditionally},"
        "positive_power="
        f"{polylog_collar.strict_positive_power_gcd_layers_covered},"
        f"whole_face={polylog_collar.whole_signed_hard_face_covered}"
    )
    strict_core = strict_power_gcd_core_audit(
        collapsed_exponent=F(1),
        cofactor_exponent=F(2, 5),
        quotient_exponent=F(1, 5),
        left_cross_gcd_exponent=F(1, 4),
    )
    print(
        "large_q_transition: strict_power_gcd_core="
        f"s={_fmt(strict_core.collapsed_exponent)},"
        f"delta={_fmt(strict_core.cofactor_exponent)},"
        f"gamma={_fmt(strict_core.gcd_exponent)},"
        f"theta={_fmt(strict_core.quotient_exponent)},"
        f"r1={_fmt(strict_core.left_cross_gcd_exponent)},"
        f"r2={_fmt(strict_core.right_cross_gcd_exponent)},"
        f"a0={_fmt(strict_core.left_reduced_slope_exponent)},"
        f"b0={_fmt(strict_core.right_reduced_slope_exponent)},"
        f"u0={_fmt(strict_core.left_reduced_signed_exponent)},"
        f"v0={_fmt(strict_core.right_reduced_signed_exponent)},"
        "unsigned="
        f"{_fmt(strict_core.unsigned_reduced_block_exponent)},"
        f"signed={_fmt(strict_core.signed_reduced_block_exponent)},"
        f"g={_fmt(strict_core.reconstructed_gcd_exponent)},"
        f"raw={_fmt(strict_core.raw_core_exponent)},"
        f"target={_fmt(strict_core.target_core_exponent)},"
        f"saving={_fmt(strict_core.required_saving_exponent)},"
        f"feasible={strict_core.exponent_polytope_feasible},"
        f"deficit_block={strict_core.unsigned_block_equals_full_deficit},"
        "full_coupling="
        f"{strict_core.all_allocations_and_ratio_integrals_retained},"
        "two_arithmetic="
        f"{strict_core.long_and_collapsed_arithmetic_weights_on_each_side},"
        "bblr_adapter="
        f"{strict_core.bblr_arbitrary_outer_coefficient_adapter_applies},"
        f"required={strict_core.centered_three_block_type_ii_required},"
        f"proved={strict_core.centered_three_block_type_ii_proved},"
        f"whole_face={strict_core.whole_signed_hard_face_covered}"
    )
    strict_convolution = strict_power_convolution_kloosterman_audit(
        collapsed_exponent=F(1),
        cofactor_exponent=F(2, 5),
        quotient_exponent=F(1, 5),
        left_cross_gcd_exponent=F(1, 4),
    )
    print(
        "large_q_transition: strict_power_convolution="
        f"r={_fmt(strict_convolution.left_convolved_outer_exponent)},"
        f"t={_fmt(strict_convolution.right_convolved_outer_exponent)},"
        f"a0={_fmt(strict_convolution.left_inner_slope_exponent)},"
        f"b0={_fmt(strict_convolution.right_inner_slope_exponent)},"
        f"side={_fmt(strict_convolution.side_product_exponent)},"
        f"outside={_fmt(strict_convolution.remaining_outer_exponent)},"
        "bblr_hypotheses="
        f"{strict_convolution.bblr_convolution_hypotheses_verified},"
        f"bblr_ab={_fmt(strict_convolution.bblr_ab_error_exponent)},"
        f"bblr_watt={_fmt(strict_convolution.bblr_watt_error_exponent)},"
        f"bblr_target={_fmt(strict_convolution.bblr_inner_target_exponent)},"
        f"bblr_deficits={_fmt(strict_convolution.bblr_ab_deficit)}/"
        f"{_fmt(strict_convolution.bblr_watt_deficit)},"
        f"bblr_covered={strict_convolution.bblr_convolution_route_covered},"
        f"dual={_fmt(strict_convolution.poisson_dual_exponent)},"
        f"numerator={_fmt(strict_convolution.poisson_numerator_exponent)},"
        f"normalization={_fmt(strict_convolution.poisson_normalization_exponent)},"
        "bc_hypotheses="
        f"{strict_convolution.bc_poisson_hypotheses_verified},"
        f"bc_totals={_fmt(strict_convolution.bc_first_total_exponent)}/"
        f"{_fmt(strict_convolution.bc_second_total_exponent)},"
        f"bc_deficits={_fmt(strict_convolution.bc_first_deficit)}/"
        f"{_fmt(strict_convolution.bc_second_deficit)},"
        f"bc_covered={strict_convolution.bc_poisson_route_covered},"
        "cross_centered="
        f"{strict_convolution.original_cross_diagonal_removed_by_centering},"
        "tuple_diagonal="
        f"{_fmt(strict_convolution.cauchy_tuple_diagonal_exponent)},"
        "grouped_diagonal="
        f"{_fmt(strict_convolution.cauchy_grouped_diagonal_exponent)},"
        "diagonal_target="
        f"{_fmt(strict_convolution.cauchy_diagonal_target_exponent)},"
        "grouped_deficit="
        f"{_fmt(strict_convolution.cauchy_grouped_diagonal_deficit)},"
        "grouped_raw="
        f"{strict_convolution.cauchy_grouped_diagonal_is_raw_scale},"
        "grouped_killed="
        f"{strict_convolution.cauchy_grouped_diagonal_killed_by_centering},"
        f"near_type_ii={strict_convolution.near_frequency_type_ii_proved}"
    )
    ratio_bandwidth = strict_power_ratio_mellin_bandwidth_audit(
        collapsed_exponent=F(1),
        cofactor_exponent=F(2, 5),
        quotient_exponent=F(1, 5),
        left_cross_gcd_exponent=F(1, 4),
    )
    print(
        "large_q_transition: strict_power_ratio_mellin_bandwidth="
        f"u0={_fmt(ratio_bandwidth.left_hidden_fibre_exponent)},"
        f"v0={_fmt(ratio_bandwidth.right_hidden_fibre_exponent)},"
        f"hidden={_fmt(ratio_bandwidth.total_hidden_fibre_exponent)},"
        "height_derivative="
        f"{_fmt(ratio_bandwidth.height_phase_log_derivative_power_exponent)},"
        "ratio_derivative="
        f"{_fmt(ratio_bandwidth.ratio_weight_log_derivative_power_exponent)},"
        "mellin_bandwidth="
        f"{_fmt(ratio_bandwidth.effective_mellin_frequency_power_exponent)},"
        "adjacent="
        f"{_fmt(ratio_bandwidth.left_adjacent_resolution_frequency_exponent)}/"
        f"{_fmt(ratio_bandwidth.right_adjacent_resolution_frequency_exponent)},"
        "cauchy_deficit="
        f"{_fmt(ratio_bandwidth.remaining_cauchy_deficit_exponent)},"
        f"rapid_tail={ratio_bandwidth.mellin_power_tail_is_rapid},"
        "scaled_not_bandwidth="
        f"{ratio_bandwidth.scaled_T_tau_not_independent_bandwidth},"
        "second_coordinate="
        f"{ratio_bandwidth.height_phase_creates_second_power_coordinate},"
        "resolves_hidden="
        f"{ratio_bandwidth.ratio_mellin_resolves_positive_hidden_fibres},"
        "supplies_delta="
        f"{ratio_bandwidth.ratio_mellin_supplies_required_delta_saving},"
        "pre_cauchy="
        f"{ratio_bandwidth.pre_cauchy_joint_kernel_still_required}"
    )
    double_poisson = strict_power_double_poisson_resonance_audit(
        collapsed_exponent=F(1),
        cofactor_exponent=F(2, 5),
        quotient_exponent=F(1, 5),
        left_cross_gcd_exponent=F(1, 4),
    )
    print(
        "large_q_transition: strict_power_double_poisson_resonance="
        f"a0={_fmt(double_poisson.left_slope_exponent)},"
        f"b0={_fmt(double_poisson.right_slope_exponent)},"
        f"r={_fmt(double_poisson.left_modulus_exponent)},"
        f"t={_fmt(double_poisson.right_modulus_exponent)},"
        f"k={_fmt(double_poisson.left_dual_exponent)},"
        f"l={_fmt(double_poisson.right_dual_exponent)},"
        f"product={_fmt(double_poisson.dual_side_product_exponent)},"
        f"shift={_fmt(double_poisson.resonance_shift_exponent)},"
        f"amplitude={_fmt(double_poisson.poisson_amplitude_exponent)},"
        f"overlap={_fmt(double_poisson.overlap_integral_exponent)},"
        "transformed_inner="
        f"{_fmt(double_poisson.transformed_absolute_inner_exponent)},"
        f"original_inner={_fmt(double_poisson.original_inner_raw_exponent)},"
        f"loss={_fmt(double_poisson.absolute_transform_loss_exponent)},"
        "transformed_global="
        f"{_fmt(double_poisson.transformed_global_absolute_exponent)},"
        f"target={_fmt(double_poisson.global_target_exponent)},"
        "required="
        f"{_fmt(double_poisson.transformed_required_saving_exponent)},"
        f"identity={double_poisson.resonance_identity_exact},"
        f"scales={double_poisson.two_poisson_scales_exact},"
        "loss_formula="
        f"{double_poisson.absolute_transform_loss_is_one_minus_delta_plus_theta},"
        f"covered={double_poisson.absolute_double_poisson_route_covered},"
        "pre_cauchy="
        f"{double_poisson.pre_cauchy_signed_resonance_estimate_required}"
    )
    print(
        "large_q_transition: strict_power_double_poisson_bblr="
        f"sharp={double_poisson.bblr_sharp_range_verified},"
        "before="
        f"{_fmt(double_poisson.bblr_ab_before_normalization_exponent)}/"
        f"{_fmt(double_poisson.bblr_watt_before_normalization_exponent)},"
        f"normalization={_fmt(double_poisson.transform_normalization_exponent)},"
        "totals="
        f"{_fmt(double_poisson.bblr_ab_total_exponent)}/"
        f"{_fmt(double_poisson.bblr_watt_total_exponent)},"
        "deficits="
        f"{_fmt(double_poisson.bblr_ab_deficit)}/"
        f"{_fmt(double_poisson.bblr_watt_deficit)},"
        "original="
        f"{_fmt(double_poisson.original_bblr_ab_deficit)}/"
        f"{_fmt(double_poisson.original_bblr_watt_deficit)},"
        f"ab_invariant={double_poisson.bblr_ab_deficit_is_invariant},"
        f"watt_extra={_fmt(double_poisson.bblr_watt_extra_deficit)},"
        "watt_nonnegative="
        f"{double_poisson.bblr_watt_extra_deficit_is_nonnegative},"
        f"improves={double_poisson.double_poisson_improves_bblr}"
    )
    transition_line_microarc = transition_line_fourier_microarc_audit(
        denominator_gcd_exponent=F(1, 2),
    )
    print(
        "large_q_transition: line_fourier_microarc="
        "gamma=1/2,A=1/2,h=1/2,product=3/2,window=-1/2,"
        "microarc=-3/2,microcells=1,fixed_raw=2,fixed_target=3/2,"
        "required=1/2,mertens_trivial=3/2,mertens_target=5/4,"
        "mertens_required=1/4,fourier=True,h_poisson=True,"
        "tensor=False,constant=False,actual_gate=False,covered=False"
    )
    transition_balanced_convolution = (
        transition_balanced_mobius_convolution_audit(
            denominator_gcd_exponent=F(1, 2),
        )
    )
    print(
        "large_q_transition: balanced_mobius_convolution="
        "gamma=1/2,A=1/2,product_center=3/2,difference=1/2,"
        "raw=2,target=3/2,required=1/2,mangerel=2,deficit=1/2,"
        "tapers=4,energy_log=1,net_log=3,autocorrelation=True,"
        "fejer=True,multiplicative=False,mellin=True,coprimality=True,"
        "nuclear_norm=True,published_variance=False,covered=False"
    )
    transition_coprimality_layers = transition_coprimality_layer_audit(
        denominator_gcd_exponent=F(1, 2),
    )
    print(
        "large_q_transition: coprimality_layer_variance="
        "gamma=1/2,A=1/2,expansion=True,euler=1+3p^-2+2p^-3+2p^-4,"
        "convergent=True,g_loss=subpolylog,dimension=5,derivatives=10,"
        "determinant_derivative_cost=0,nuclear_norm=True,layers=True,"
        "required=1/2,published_variance=False,reduced=True,covered=False"
    )
    transition_fourth_moment = transition_mobius_dirichlet_fourth_moment_audit(
        denominator_gcd_exponent=F(1, 2),
    )
    print(
        "large_q_transition: mobius_mixed_fourth_moment="
        "gamma=1/2,A=1/2,long=1,product=3/2,height=1,"
        "coefficient_target=3/2,normalization=-1/2,moment_target=1,"
        "generic=3/2,deficit=1/2,dirichlet_product=True,"
        "scaled_log_inversion=True,zero_compact_exclusion=False,coprimality=True,"
        "dcv_superposition=True,uniform_sufficient=True,"
        "dcv_implies_components=False,published=False,covered=False"
    )
    transition_large_values = transition_mobius_large_value_audit(
        amplitude_exponent=F(2, 3),
    )
    print(
        "large_q_transition: mobius_large_values="
        "sigma=2/3,target=3,required_count=1/3,classical_count=2/3,"
        "classical_moment=10/3,gm1=10/3,gm2=18/5,gm3=17/5,"
        "gm_moment=18/5,best=10/3,deficit=1/3,menon_power=0,"
        "pointwise_threshold=3/4,mobius_theorem=False,"
        "signed_dcv_requires_components=False,covered=False"
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
