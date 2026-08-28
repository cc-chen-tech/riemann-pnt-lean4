#!/usr/bin/env python3
"""Exact-rational adapters for published MWKF core estimates.

The adapters only certify a route when every encoded hypothesis and the
fixed target saving hold.  A rejected result is a coverage witness, not a
claim that the corresponding theorem is false.
"""

from __future__ import annotations

import cmath
import sys
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from math import gcd, isqrt, log, pi
from pathlib import Path

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
    pascadi_uniform_saving_exponent: Fraction
    pascadi_uniform_deficit: Fraction
    pascadi_one_bounded_saving_exponent: Fraction
    pascadi_one_bounded_deficit: Fraction
    pascadi_factorable_saving_exponent: Fraction
    pascadi_factorable_deficit: Fraction
    pascadi_averaged_common_divisor_exponent: Fraction
    pascadi_averaged_modulus_saving_exponent: Fraction
    optimistic_four_bp_applications_saving_exponent: Fraction
    optimistic_four_bp_deficit: Fraction
    bp_square_root_length_condition_holds: bool
    bp_arbitrary_sequences_allowed: bool
    standard_kloosterman_kernel_verified: bool
    coefficients_separate_from_matrix_entries: bool
    fixed_modulus_before_entry_sum_verified: bool
    pascadi_uniform_for_all_moduli: bool
    primitive_determinant_common_divisor_is_one: bool
    pascadi_averaged_modulus_power_saving: bool
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
    zero_mode_weight_separates_in_the_entries: bool
    zero_mode_mobius_variance_proved: bool
    whole_delta_lattice_covered: bool


@dataclass(frozen=True)
class TransitionPoissonResonantGramAudit:
    discrete_identity_diagonal_exponent: Fraction
    continuous_self_gram_exponent: Fraction
    sampling_correction_bound_exponent: Fraction
    sampling_correction_power_deficit: Fraction
    continuous_full_gram_trivial_exponent: Fraction
    square_function_target_exponent: Fraction
    required_continuous_gram_saving_exponent: Fraction
    poisson_covolume_cancels_jacobian: bool
    offdiagonal_zero_mode_is_sign_indefinite: bool
    resonant_recombination_exact: bool
    sampling_correction_has_no_positive_power_obstruction: bool
    endpoint_logarithmic_aggregation_closed: bool
    continuous_mobius_gram_bound_proved: bool
    whole_poisson_zero_mode_covered: bool


@dataclass(frozen=True)
class TransitionPoissonTubeClusterAudit:
    tube_longitudinal_length_exponent: Fraction
    tube_transverse_width_exponent: Fraction
    angular_resolution_exponent: Fraction
    primitive_direction_family_exponent: Fraction
    angular_cluster_count_exponent: Fraction
    entries_per_cluster_exponent: Fraction
    coherent_cluster_energy_exponent: Fraction
    square_root_cluster_energy_exponent: Fraction
    square_function_target_exponent: Fraction
    square_root_margin_exponent: Fraction
    cluster_coefficient: str
    same_cluster_implies_determinant_collar: bool
    determinant_collar_implies_adjacent_clusters: bool
    angular_interaction_has_bounded_cluster_multiplicity: bool
    critical_sector_is_single_beatty_graph: bool
    primitive_mobius_product_fold_exact: bool
    vector_kernel_prevents_scalar_product_collapse: bool
    additive_fourier_interface_reappears_after_strip_transform: bool
    additive_local_moment_input_is_unconditional: bool
    sector_character_parseval_exact: bool
    sector_principal_mode_absorbable: bool
    remaining_resonant_gate_has_only_nonzero_sector_characters: bool
    single_mobius_log_derivative_exact: bool
    nonzero_character_automatic_frequency_decay: bool
    pre_cauchy_type_dispersion_required: bool
    nonzero_character_type_bound_proved: bool
    requires_vector_valued_two_mobius_cancellation: bool
    unweighted_farey_equidistribution_matches: bool
    one_mobius_nilsequence_theorem_matches: bool
    published_coverage: bool
    farey_source: str


@dataclass(frozen=True)
class FareySectorPairLedger:
    q: int
    first_sector: int
    second_sector: int
    sector_distance: int
    signed_determinant: int
    absolute_determinant: int
    same_sector: bool
    in_determinant_collar: bool
    same_sector_implies_collar: bool
    collar_implies_adjacent_sectors: bool


@dataclass(frozen=True)
class FareySectorFiberLedger:
    q: int
    sector: int
    denominator: int
    lower_integer: int
    upper_integer_exclusive: int
    beatty_candidate: int
    members: tuple[int, ...]
    member_count: int
    general_count_bound: int
    unique_when_s_at_most_q: bool


@dataclass(frozen=True)
class FareyPrimitiveProductCoordinateLedger:
    q: int
    k: int
    first_entry: int
    second_entry: int
    shifted_numerator: int
    sector: int
    product_coordinate: int
    mobius_first: int
    mobius_second: int
    mobius_product_coordinate: int
    primitive_entry: bool
    mobius_product_fold_exact: bool
    sector_product_lower_bound: int
    scaled_product_coordinate: int
    sector_product_upper_bound: int
    sector_product_inequality_exact: bool
    second_entry_recovered_from_divisor: int


@dataclass(frozen=True)
class FareyProductSectorFiberLedger:
    q: int
    k: int
    sector: int
    product_coordinate: int
    sector_scale: int
    integer_interval_members: tuple[int, ...]
    primitive_divisor_members: tuple[tuple[int, int, int], ...]
    critical_ratio_bound: int
    critical_scale_hypothesis: bool
    pairwise_diameter_inequality_exact: bool
    integer_fiber_cardinality_bound: int
    bounded_multiplicity_certified: bool
    product_mobius_coefficient_fixed_across_primitive_fiber: bool
    vector_weight_still_factorization_dependent: bool
    cancellation_estimate_proved: bool


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
class TransitionBBLRHardHCompletionAudit:
    poisson_gcd_exponent: Fraction
    reduced_h_length_exponent: Fraction
    reduced_modulus_exponent: Fraction
    h_length_matches_modulus: bool
    nonzero_l_cutoff_exponent: Fraction
    positive_power_gcd_shell_has_no_nonzero_l: bool
    reduced_n1_count_exponent: Fraction
    completed_m1_h_exponent: Fraction
    poisson_integral_exponent: Fraction
    fixed_gcd_value_exponent: Fraction
    poisson_gcd_count_exponent: Fraction
    dyadic_layer_exponent: Fraction
    global_nonzero_frequency_exponent: Fraction
    target_exponent: Fraction
    power_margin: Fraction
    inverse_map_is_permutation_on_units: bool
    multiplier_fibre_bound_is_gcd: bool
    nonzero_frequency_error_closed_with_epsilon_loss: bool
    poisson_main_term_controlled: bool
    whole_unsigned_cell_covered: bool
    source: str


@dataclass(frozen=True)
class TransitionBBLRHCompletionSubcellAudit:
    outer_a_exponent: Fraction
    outer_b_exponent: Fraction
    m1_exponent: Fraction
    m2_exponent: Fraction
    n1_exponent: Fraction
    n2_exponent: Fraction
    shift_exponent: Fraction
    left_side_product_exponent: Fraction
    right_side_product_exponent: Fraction
    x_product_exponent: Fraction
    y_modulus_exponent: Fraction
    x_over_y_excess_exponent: Fraction
    h_or_modulus_exponent: Fraction
    nonzero_l_base_cutoff_exponent: Fraction
    summed_frequency_gcd_exponent: Fraction
    chosen_orientation_hypothesis_verified: bool
    nonzero_frequency_family_empty: bool
    global_nonzero_frequency_exponent: Fraction
    target_exponent: Fraction
    power_margin: Fraction
    nonzero_frequency_cell_covered: bool
    outer_coefficients_may_be_arbitrary: bool
    factorization_multiplicity_is_divisor_bounded: bool
    frequency_gcd_average_is_divisor_bounded: bool
    preserves_two_mobius_weights_in_outer_coefficients: bool
    poisson_main_term_controlled: bool
    whole_type_subcell_covered: bool
    source: str


@dataclass(frozen=True)
class FrequencyGcdSumIdentity:
    modulus: int
    cutoff: int
    direct_gcd_sum: int
    divisor_totient_sum: int
    divisor_count: int
    linear_divisor_bound: int


@dataclass(frozen=True)
class TransitionBBLRZeroMainTermAudit:
    side_product_exponent: Fraction
    shift_exponent: Fraction
    poisson_gcd_exponent: Fraction
    fixed_gcd_exponent: Fraction
    dyadic_gcd_layer_exponent: Fraction
    global_raw_main_term_exponent: Fraction
    target_exponent: Fraction
    power_margin: Fraction
    missing_saving_exponent: Fraction
    main_term_is_independent_of_shift_orientation: bool
    shift_orientations_cancel_internally: bool
    registered_zero_master_identification_proved: bool
    source: str


@dataclass(frozen=True)
class TransitionBBLRSymmetricHCompletionAudit:
    left_prefix_exponent: Fraction
    right_prefix_exponent: Fraction
    smaller_prefix_exponent: Fraction
    side_product_exponent: Fraction
    shift_exponent: Fraction
    cutoff_hyperplane_excess: Fraction
    smaller_prefix_shortfall: Fraction
    chosen_orientation: str
    nonzero_frequency_family_empty: bool
    symmetric_nonzero_frequency_exponent: Fraction
    target_exponent: Fraction
    power_margin: Fraction
    boundary_coverage_conditions_hold: bool
    nonzero_frequency_cell_covered: bool
    source: str


@dataclass(frozen=True)
class TransitionBBLRPhaseGroupSavingAudit:
    side_product_exponent: Fraction
    shift_exponent: Fraction
    left_prefix_exponent: Fraction
    right_prefix_exponent: Fraction
    nonzero_l_range_exponent: Fraction
    raw_nonzero_frequency_exponent: Fraction
    target_exponent: Fraction
    required_l_range_saving_exponent: Fraction
    square_root_l_saving_exponent: Fraction
    remaining_after_square_root_exponent: Fraction
    signed_phase_class_cross_terms_required: bool
    product_frequency_partition_is_sufficient: bool
    required_phase_class_cancellation_proved: bool


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
class PublishedMobiusFourthMomentCoverageAudit:
    target_length_exponent: Fraction
    target_height_exponent: Fraction
    target_normalized_moment_exponent: Fraction
    bhsj_amplifier_length_ceiling: Fraction
    bhsj_length_power_deficit: Fraction
    bhsj_length_hypothesis_met: bool
    bhsj_mobius_coefficient_class_matches: bool
    bhsj_pure_fourth_moment_integrand_matches: bool
    bhsj_direct_coverage: bool
    verjovsky_polynomial_is_additive_fourier: bool
    verjovsky_polynomial_is_multiplicative_dirichlet: bool
    verjovsky_local_arc_exponent: Fraction
    verjovsky_subpolynomial_moment_bound_equivalent_to_rh: bool
    verjovsky_unconditional_coverage: bool
    direct_published_coverage: bool
    bhsj_source: str
    verjovsky_source: str


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
class TransitionKimTernaryCorrelationAudit:
    ambient_length_exponent: Fraction
    shift_length_exponent: Fraction
    target_exponent: Fraction
    relative_shift_exponent: Fraction
    theorem_alpha_zero_shift_floor: Fraction
    theorem_buffer_multiplier: int
    theorem_epsilon_ceiling: Fraction
    ambient_sum_exponent: Fraction
    required_saving_exponent: Fraction
    theorem_saving_ceiling: Fraction
    residual_power_deficit: Fraction
    mobius_dirichlet_series_is_reciprocal_l: bool
    mobius_holomorphic_halfplane_hypothesis: bool
    mobius_critical_line_second_moment_hypothesis: bool
    dyadic_convolution_is_one_multiplicative_function: bool
    theorem_applies_to_actual_packet: bool
    whole_line_family_covered: bool
    source: str


@dataclass(frozen=True)
class TransitionDoyleKFreeMomentAudit:
    product_center_exponent: Fraction
    short_interval_exponent: Fraction
    relative_interval_exponent: Fraction
    k_two_middle_part_exponent: Fraction
    mobius_l1_threshold_exponent: Fraction
    length_margin_exponent: Fraction
    theorem_is_l1_lower_bound: bool
    theorem_is_variance_upper_bound: bool
    middle_coefficient_uses_square_divisors: bool
    middle_coefficient_matches_balanced_two_mobius_convolution: bool
    theorem_applies_to_actual_packet: bool
    whole_line_family_covered: bool
    source: str


@dataclass(frozen=True)
class TransitionShiBesselKuznetsovAudit:
    exact_orbit_first_fourier_index: int
    exact_orbit_second_fourier_index: int
    bessel_argument_is_zero: bool
    paper_requires_positive_dyadic_bessel_argument: bool
    paper_linear_twist_identified_in_actual_orbit: bool
    classical_nondegenerate_kuznetsov_adapter_verified: bool
    subcritical_rapid_decay_applies: bool
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


def h_product_phase_character_orthogonality(
    *,
    s: int,
    w: int,
    delta: int,
    dual_v: int,
) -> dict[str, int | str | bool | None]:
    """Audit exactly what remains of ``a=h*delta`` after h-dualization.

    The additive phase in the complete ``h`` residue class is

    ``e_s(h*(dual_v-delta*inverse(w)))``.

    Character orthogonality makes its complete sum equal to ``s`` exactly
    when ``dual_v == delta*inverse(w) (mod s)``, and zero otherwise.  Since
    ``w`` is a unit, this is equivalent to the determinant-line incidence

    ``w*dual_v-j*s=delta``.

    Thus the original product-frequency phase is converted into a lattice
    constraint.  No residual ``h*delta`` oscillator survives on one dual
    mode.  The smooth Fourier weight may still couple all outer labels, so
    this finite identity proves no cancellation estimate.
    """
    if s <= 0:
        raise ValueError("the phase modulus must be positive")
    if gcd(w, s) != 1:
        raise ValueError("w must be a unit modulo s")

    w_inverse = pow(w, -1, s)
    phase_residue = (dual_v - delta * w_inverse) % s
    lattice_numerator = w * dual_v - delta
    lattice_constraint = lattice_numerator % s == 0
    character_sum = s if phase_residue == 0 else 0
    return {
        "modulus": s,
        "w_inverse": w_inverse,
        "combined_character_residue": phase_residue,
        "complete_character_sum": character_sum,
        "lattice_numerator": lattice_numerator,
        "dual_j": lattice_numerator // s if lattice_constraint else None,
        "character_condition_equals_lattice_constraint": (
            (phase_residue == 0) == lattice_constraint
        ),
        "afe_product_frequency_before_dualization": "h*delta",
        "product_phase_converted_to_lattice_constraint": True,
        "h_variable_eliminated_by_character_orthogonality": True,
        "residual_hdelta_oscillation_available": False,
        "automatic_power_saving_from_product_frequency": False,
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
    Wu Theorem 1.1 saves ``c^(1/100)`` uniformly.  Pascadi v2 Theorem
    1.1 saves ``c^(1/700)`` for all moduli, or ``c^(1/276)`` when one
    sequence is 1-bounded; Theorem 1.2 can save ``c^(1/12)`` for
    favorable composite moduli.  Corollary 1.4 gives no power saving on
    the primitive determinant shell because its only common fixed divisor
    is ``q=1``.

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
    pascadi_uniform = F(1, 700)
    pascadi_one_bounded = F(1, 276)
    pascadi_factorable = F(1, 12)
    averaged_common_divisor = F(0)
    averaged_modulus_saving = F(0)
    four_bp = 4 * bp
    return TransitionPublishedKloostermanEntryAudit(
        modulus_exponent=modulus,
        delta_interval_exponent=interval,
        required_mobius_entry_saving_exponent=required,
        bp_uniform_saving_exponent=bp,
        bp_uniform_deficit=required - bp,
        mqw_uniform_saving_exponent=mqw,
        mqw_uniform_deficit=required - mqw,
        pascadi_uniform_saving_exponent=pascadi_uniform,
        pascadi_uniform_deficit=required - pascadi_uniform,
        pascadi_one_bounded_saving_exponent=pascadi_one_bounded,
        pascadi_one_bounded_deficit=required - pascadi_one_bounded,
        pascadi_factorable_saving_exponent=pascadi_factorable,
        pascadi_factorable_deficit=required - pascadi_factorable,
        pascadi_averaged_common_divisor_exponent=averaged_common_divisor,
        pascadi_averaged_modulus_saving_exponent=averaged_modulus_saving,
        optimistic_four_bp_applications_saving_exponent=four_bp,
        optimistic_four_bp_deficit=required - four_bp,
        bp_square_root_length_condition_holds=(2 * interval == modulus),
        bp_arbitrary_sequences_allowed=True,
        standard_kloosterman_kernel_verified=False,
        coefficients_separate_from_matrix_entries=False,
        fixed_modulus_before_entry_sum_verified=False,
        pascadi_uniform_for_all_moduli=True,
        primitive_determinant_common_divisor_is_one=True,
        pascadi_averaged_modulus_power_saving=False,
        published_coverage=False,
        bp_source=(
            "Blomer--Pascadi, arXiv:2607.24311v1, Theorem 1.1"
        ),
        mqw_source=(
            "Milicevic--Qin--Wu, arXiv:2511.07550v1, Theorem 1.1"
        ),
        pascadi_source=(
            "Pascadi, arXiv:2511.08445v2, Theorems 1.1--1.2 and "
            "Corollary 1.4"
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
        zero_mode_weight_separates_in_the_entries=False,
        zero_mode_mobius_variance_proved=False,
        whole_delta_lattice_covered=False,
    )


def transition_poisson_resonant_gram_audit(
) -> TransitionPoissonResonantGramAudit:
    """Separate the canonical zero mode from its diagonal sampling error.

    For an offdiagonal entry pair, writing ``G_B(z)=F_B(Bz)`` cancels
    the Poisson covolume ``abs(det B)^(-1)`` against the change-of-variable
    Jacobian.  Adding and subtracting the *continuous* self pairs gives

    ``D_disc + Z0_off = c0*E_cont + (D_disc-c0*D_cont)``.

    The already registered discrete identity diagonal has exponent two.
    The continuous self diagonal has the same exponent: in one entry the
    coordinates ``(v,delta=w*v-s*j)`` have Jacobian ``s asymp T`` and the
    two support lengths are ``T^(1/2)``, so their normalized area has
    exponent zero; summing the entry family costs exponent two.  Hence the
    sampling correction has no positive-power deficit (its endpoint
    logarithms are not closed here).  The full continuous Gram retains the
    absolute zero-mode exponent three from the delta-lattice audit and
    still needs one power of coupled Möbius cancellation.
    """
    target = F(2)
    discrete_diagonal = F(2)
    continuous_self = F(2)
    sampling_bound = max(discrete_diagonal, continuous_self)
    continuous_full = F(3)
    return TransitionPoissonResonantGramAudit(
        discrete_identity_diagonal_exponent=discrete_diagonal,
        continuous_self_gram_exponent=continuous_self,
        sampling_correction_bound_exponent=sampling_bound,
        sampling_correction_power_deficit=max(F(0), sampling_bound - target),
        continuous_full_gram_trivial_exponent=continuous_full,
        square_function_target_exponent=target,
        required_continuous_gram_saving_exponent=continuous_full - target,
        poisson_covolume_cancels_jacobian=True,
        offdiagonal_zero_mode_is_sign_indefinite=True,
        resonant_recombination_exact=True,
        sampling_correction_has_no_positive_power_obstruction=(
            sampling_bound <= target
        ),
        endpoint_logarithmic_aggregation_closed=False,
        continuous_mobius_gram_bound_proved=False,
        whole_poisson_zero_mode_covered=False,
    )


def transition_poisson_tube_cluster_audit(
) -> TransitionPoissonTubeClusterAudit:
    """Resolve the continuous resonant Gram into Farey angular clusters.

    A critical one-entry kernel is supported on a tube in the ``(v,j)``
    plane of longitudinal length ``T^(1/2)`` and transverse width
    ``T^(-1/2)``.  Its angular resolution is therefore ``T^(-1)``.
    The primitive directions ``w/s`` with ``w,s asymp T`` form a family of
    exponent two, so there are ``T`` angular clusters and ``T`` entries in
    one cluster.  Coherent summation gives energy ``T * T^2=T^3``;
    square-root cancellation in each vector-valued cluster gives
    ``T * T=T^2``, exactly the target and with no spare power.

    The entry coefficient is ``mu(s)mu(k*s+w)``.  Smooth or unweighted
    Farey/horocycle equidistribution does not retain this two-Möbius weight,
    and one-Möbius nilsequence orthogonality does not allow the second
    moving Möbius factor.  The audit therefore records geometry, not a
    published proof of the cluster square function.
    """
    longitudinal = F(1, 2)
    transverse = F(-1, 2)
    angular_resolution = transverse - longitudinal
    direction_family = F(2)
    cluster_count = -angular_resolution
    entries_per_cluster = direction_family - cluster_count
    coherent_energy = cluster_count + 2 * entries_per_cluster
    square_root_energy = cluster_count + entries_per_cluster
    target = F(2)
    return TransitionPoissonTubeClusterAudit(
        tube_longitudinal_length_exponent=longitudinal,
        tube_transverse_width_exponent=transverse,
        angular_resolution_exponent=angular_resolution,
        primitive_direction_family_exponent=direction_family,
        angular_cluster_count_exponent=cluster_count,
        entries_per_cluster_exponent=entries_per_cluster,
        coherent_cluster_energy_exponent=coherent_energy,
        square_root_cluster_energy_exponent=square_root_energy,
        square_function_target_exponent=target,
        square_root_margin_exponent=target - square_root_energy,
        cluster_coefficient="mu(s)*mu(k*s+w)",
        same_cluster_implies_determinant_collar=True,
        determinant_collar_implies_adjacent_clusters=True,
        angular_interaction_has_bounded_cluster_multiplicity=True,
        critical_sector_is_single_beatty_graph=True,
        primitive_mobius_product_fold_exact=True,
        vector_kernel_prevents_scalar_product_collapse=True,
        additive_fourier_interface_reappears_after_strip_transform=True,
        additive_local_moment_input_is_unconditional=False,
        sector_character_parseval_exact=True,
        sector_principal_mode_absorbable=True,
        remaining_resonant_gate_has_only_nonzero_sector_characters=True,
        single_mobius_log_derivative_exact=True,
        nonzero_character_automatic_frequency_decay=False,
        pre_cauchy_type_dispersion_required=True,
        nonzero_character_type_bound_proved=False,
        requires_vector_valued_two_mobius_cancellation=True,
        unweighted_farey_equidistribution_matches=False,
        one_mobius_nilsequence_theorem_matches=False,
        published_coverage=False,
        farey_source=(
            "Panti, arXiv:1503.02539v2, weighted Farey sequence and "
            "horocycle equidistribution; smooth denominator weights, not "
            "the two-Mobius microscopic square function."
        ),
    )


def farey_sector_pair_ledger(
    *,
    q: int,
    w1: int,
    s1: int,
    w2: int,
    s2: int,
) -> FareySectorPairLedger:
    """Give an exact finite sector/determinant implication ledger.

    Put the nonnegative slope ``w/s`` in sector ``floor(q*w/s)``.  If two
    slopes lie in the same sector, their determinant obeys

    ``q*abs(w1*s2-w2*s1) < s1*s2``.

    Conversely that strict determinant collar makes the two real sector
    coordinates differ by less than one, so their integer sector labels
    differ by at most one.  Thus the physical angular collar is covered by
    same-or-neighbor sectors with multiplicity at most three; it is not
    identical to the same-sector relation.
    """
    if q <= 0:
        raise ValueError("q must be positive")
    if s1 <= 0 or s2 <= 0:
        raise ValueError("sector denominators must be positive")
    if w1 < 0 or w2 < 0:
        raise ValueError("sector numerators must be nonnegative")

    first_sector = q * w1 // s1
    second_sector = q * w2 // s2
    sector_distance = abs(first_sector - second_sector)
    determinant = w1 * s2 - w2 * s1
    absolute_determinant = abs(determinant)
    same_sector = sector_distance == 0
    collar = q * absolute_determinant < s1 * s2
    return FareySectorPairLedger(
        q=q,
        first_sector=first_sector,
        second_sector=second_sector,
        sector_distance=sector_distance,
        signed_determinant=determinant,
        absolute_determinant=absolute_determinant,
        same_sector=same_sector,
        in_determinant_collar=collar,
        same_sector_implies_collar=(not same_sector) or collar,
        collar_implies_adjacent_sectors=(not collar) or sector_distance <= 1,
    )


def farey_sector_fiber_ledger(
    *,
    q: int,
    b: int,
    s: int,
) -> FareySectorFiberLedger:
    """List one exact angular-sector fiber over a fixed denominator.

    The sector condition is ``b*s <= q*w < (b+1)*s``.  Its integral
    points form the half-open interval

    ``ceil(b*s/q) <= w < ceil((b+1)*s/q)``.

    Hence the fiber contains at most ``ceil(s/q)`` integers, and at the
    critical resolution ``s <= q`` it is either empty or the single
    truncated Beatty value ``ceil(b*s/q)``.
    """
    if q <= 0 or s <= 0:
        raise ValueError("q and s must be positive")
    if b < 0:
        raise ValueError("the nonnegative-slope sector must be nonnegative")

    lower = (b * s + q - 1) // q
    upper = ((b + 1) * s + q - 1) // q
    members = tuple(range(lower, upper))
    general_bound = (s + q - 1) // q
    return FareySectorFiberLedger(
        q=q,
        sector=b,
        denominator=s,
        lower_integer=lower,
        upper_integer_exclusive=upper,
        beatty_candidate=lower,
        members=members,
        member_count=len(members),
        general_count_bound=general_bound,
        unique_when_s_at_most_q=(s > q) or len(members) <= 1,
    )


def farey_primitive_product_coordinate_ledger(
    *,
    q: int,
    k: int,
    r: int,
    s: int,
) -> FareyPrimitiveProductCoordinateLedger:
    """Fold one primitive two-Mobius Farey entry into ``n=r*s``.

    Write ``w=r-k*s >= 0`` and ``b=floor(q*w/s)``.  On ``gcd(r,s)=1``
    multiplicativity gives ``mu(r)mu(s)=mu(r*s)``.  The angular sector
    is equivalently the exact product-coordinate inequality

    ``(k*q+b)*s^2 <= q*(r*s) < (k*q+b+1)*s^2``.

    This is an entrywise identity only.  It does not collapse the
    vector-valued wave packet, which still depends separately on ``r``
    and ``s``.
    """
    if q <= 0 or s <= 0 or r <= 0:
        raise ValueError("q, r, and s must be positive")
    if k < 0:
        raise ValueError("k must be nonnegative")
    w = r - k * s
    if w < 0:
        raise ValueError("the shifted numerator w=r-k*s must be nonnegative")

    primitive = gcd(r, s) == 1
    if not primitive:
        raise ValueError("the product fold requires a primitive entry")
    sector = q * w // s
    product = r * s
    mu_r = _finite_mobius(r)
    mu_s = _finite_mobius(s)
    mu_product = _finite_mobius(product)
    lower = (k * q + sector) * s * s
    scaled_product = q * product
    upper = (k * q + sector + 1) * s * s
    return FareyPrimitiveProductCoordinateLedger(
        q=q,
        k=k,
        first_entry=s,
        second_entry=r,
        shifted_numerator=w,
        sector=sector,
        product_coordinate=product,
        mobius_first=mu_s,
        mobius_second=mu_r,
        mobius_product_coordinate=mu_product,
        primitive_entry=primitive,
        mobius_product_fold_exact=mu_s * mu_r == mu_product,
        sector_product_lower_bound=lower,
        scaled_product_coordinate=scaled_product,
        sector_product_upper_bound=upper,
        sector_product_inequality_exact=lower <= scaled_product < upper,
        second_entry_recovered_from_divisor=product // s,
    )


def farey_product_sector_fiber_ledger(
    *,
    q: int,
    k: int,
    b: int,
    n: int,
    critical_ratio_bound: int,
) -> FareyProductSectorFiberLedger:
    """Bound a fixed product-sector denominator fiber exactly.

    Put A=k*q+b.  The product-coordinate sector condition is

    A*s^2 <= q*n < (A+1)*s^2.

    If every such point satisfies s <= C*A, two points s1<s2 obey

    A*(s2-s1)*(s1+s2) < s1^2,

    and therefore s2-s1<C.  The fiber then contains at most C integers.
    Primitive divisor points additionally require s|n and gcd(s,n/s)=1;
    on them mu(s)mu(n/s)=mu(n).  The wave packet still depends on the
    chosen factorization, so this finite fold proves no cancellation.
    """
    if q <= 0 or n <= 0:
        raise ValueError("q and n must be positive")
    if k < 0 or b < 0:
        raise ValueError("k and the sector must be nonnegative")
    if critical_ratio_bound < 1:
        raise ValueError("the critical ratio bound must be positive")
    sector_scale = k * q + b
    if sector_scale <= 0:
        raise ValueError("the zero product-sector scale is degenerate")

    upper_search = isqrt((q * n) // sector_scale)
    members = tuple(
        s
        for s in range(1, upper_search + 1)
        if sector_scale * s * s <= q * n
        < (sector_scale + 1) * s * s
    )
    primitive_members: list[tuple[int, int, int]] = []
    for s in members:
        if n % s != 0:
            continue
        r = n // s
        w = r - k * s
        if w < 0 or gcd(r, s) != 1:
            continue
        if q * w // s != b:
            raise AssertionError("product-sector and angular-sector labels disagree")
        primitive_members.append((s, r, w))

    scale_hypothesis = all(
        s <= critical_ratio_bound * sector_scale for s in members
    )
    pairwise_exact = all(
        sector_scale * (s2 - s1) * (s1 + s2) < s1 * s1
        for left_index, s1 in enumerate(members)
        for s2 in members[left_index + 1 :]
    )
    cardinality_bound = critical_ratio_bound
    bounded = (
        scale_hypothesis
        and pairwise_exact
        and len(members) <= cardinality_bound
    )
    fixed_mobius = all(
        _finite_mobius(s) * _finite_mobius(r) == _finite_mobius(n)
        for s, r, _ in primitive_members
    )
    return FareyProductSectorFiberLedger(
        q=q,
        k=k,
        sector=b,
        product_coordinate=n,
        sector_scale=sector_scale,
        integer_interval_members=members,
        primitive_divisor_members=tuple(primitive_members),
        critical_ratio_bound=critical_ratio_bound,
        critical_scale_hypothesis=scale_hypothesis,
        pairwise_diameter_inequality_exact=pairwise_exact,
        integer_fiber_cardinality_bound=cardinality_bound,
        bounded_multiplicity_certified=bounded,
        product_mobius_coefficient_fixed_across_primitive_fiber=fixed_mobius,
        vector_weight_still_factorization_dependent=True,
        cancellation_estimate_proved=False,
    )


def banded_sector_gram_sides(
    *,
    cluster_vectors: dict[int, tuple[Fraction, ...]],
    bandwidth: int,
) -> dict[str, Fraction | int | bool]:
    """Verify the finite bounded-overlap sector-Gram reduction.

    If cluster vectors ``S_b`` have zero inner product whenever
    ``abs(b-c)>R``, then Cauchy--Schwarz and ``2ab<=a^2+b^2`` give

    ``||sum_b S_b||^2 <= (2R+1) sum_b ||S_b||^2``.

    The helper evaluates both sides over exact rational vectors.  In the
    analytic application the vanishing is supplied by compact wave-packet
    support after widening the angular sectors by a fixed cutoff-dependent
    bandwidth.
    """
    if bandwidth < 0:
        raise ValueError("bandwidth must be nonnegative")
    if not cluster_vectors:
        raise ValueError("at least one cluster vector is required")
    dimensions = {len(vector) for vector in cluster_vectors.values()}
    if len(dimensions) != 1:
        raise ValueError("all cluster vectors must have one dimension")

    def dot(
        left: tuple[Fraction, ...],
        right: tuple[Fraction, ...],
    ) -> Fraction:
        return sum((F(x) * F(y) for x, y in zip(left, right)), F(0))

    sectors = sorted(cluster_vectors)
    dimension = dimensions.pop()
    total_vector = tuple(
        sum((F(cluster_vectors[b][i]) for b in sectors), F(0))
        for i in range(dimension)
    )
    direct_energy = dot(total_vector, total_vector)
    expanded_energy = sum(
        (
            dot(cluster_vectors[b], cluster_vectors[c])
            for b in sectors
            for c in sectors
        ),
        F(0),
    )
    cluster_square = sum(
        (dot(cluster_vectors[b], cluster_vectors[b]) for b in sectors),
        F(0),
    )
    far_vanish = all(
        dot(cluster_vectors[b], cluster_vectors[c]) == 0
        for b in sectors
        for c in sectors
        if abs(b - c) > bandwidth
    )
    overlap = 2 * bandwidth + 1
    upper_bound = overlap * cluster_square
    return {
        "far_cluster_inner_products_vanish": far_vanish,
        "direct_global_energy": direct_energy,
        "expanded_global_energy": expanded_energy,
        "energy_expansion_exact": direct_energy == expanded_energy,
        "cluster_square_function": cluster_square,
        "bounded_overlap_constant": overlap,
        "bounded_overlap_upper_bound": upper_bound,
        "global_energy_bounded_by_cluster_square_function": (
            far_vanish and direct_energy <= upper_bound
        ),
    }


def sector_character_parseval_sides(
    *,
    entries: tuple[tuple[int, Fraction, tuple[Fraction, ...]], ...],
    modulus: int,
    original_entry_ids: tuple[str, ...] | None = None,
) -> dict[str, Fraction | bool]:
    """Verify exact cyclic Parseval for vector-valued angular sectors.

    Each entry is ``(sector, coefficient, vector)``.  Sectors are embedded
    without aliasing in ``Z/modulus Z``.  Character orthogonality then gives

    ``sum_b ||S_b||^2 = modulus^-1 sum_xi ||sum_e c_e e(xi*b_e/M)G_e||^2``.

    The helper evaluates the normalized character side algebraically via
    the exact congruence indicator, avoiding floating roots of unity.  The
    principal character is exactly ``modulus^-1`` times the original global
    Gram ``||sum_e c_e G_e||^2``.

    If ``original_entry_ids`` is supplied, packets with one original entry
    id are recombined before its self diagonal is formed.  All packets in
    one such group must lie in the same sector.
    """
    if modulus <= 0:
        raise ValueError("modulus must be positive")
    if not entries:
        raise ValueError("at least one sector entry is required")
    dimensions = {len(vector) for _, _, vector in entries}
    if len(dimensions) != 1:
        raise ValueError("all entry vectors must have one dimension")
    if any(sector < 0 or sector >= modulus for sector, _, _ in entries):
        raise ValueError("sector labels must lie in the no-alias interval")
    if (
        original_entry_ids is not None
        and len(original_entry_ids) != len(entries)
    ):
        raise ValueError("original entry ids must match the entry list")

    def dot(
        left: tuple[Fraction, ...],
        right: tuple[Fraction, ...],
    ) -> Fraction:
        return sum((F(x) * F(y) for x, y in zip(left, right)), F(0))

    dimension = dimensions.pop()
    sectors = sorted({sector for sector, _, _ in entries})
    cluster_vectors = {
        sector: tuple(
            sum(
                (
                    F(coefficient) * F(vector[i])
                    for entry_sector, coefficient, vector in entries
                    if entry_sector == sector
                ),
                F(0),
            )
            for i in range(dimension)
        )
        for sector in sectors
    }
    cluster_square = sum(
        (dot(vector, vector) for vector in cluster_vectors.values()),
        F(0),
    )
    normalized_character_energy = sum(
        (
            F(coefficient_left)
            * F(coefficient_right)
            * dot(vector_left, vector_right)
            for sector_left, coefficient_left, vector_left in entries
            for sector_right, coefficient_right, vector_right in entries
            if (sector_left - sector_right) % modulus == 0
        ),
        F(0),
    )
    global_vector = tuple(
        sum(
            (F(coefficient) * F(vector[i]) for _, coefficient, vector in entries),
            F(0),
        )
        for i in range(dimension)
    )
    global_gram = dot(global_vector, global_vector)
    principal = global_gram / modulus
    nonprincipal = normalized_character_energy - principal
    entry_ids = (
        original_entry_ids
        if original_entry_ids is not None
        else tuple(str(index) for index in range(len(entries)))
    )
    if any(
        len(
            {
                sector
                for entry_id, (sector, _, _) in zip(entry_ids, entries)
                if entry_id == target_id
            }
        )
        != 1
        for target_id in set(entry_ids)
    ):
        raise ValueError("one original entry id must lie in one sector")
    grouped_entry_vectors = {
        target_id: tuple(
            sum(
                (
                    F(coefficient) * F(vector[i])
                    for entry_id, (_, coefficient, vector) in zip(
                        entry_ids, entries
                    )
                    if entry_id == target_id
                ),
                F(0),
            )
            for i in range(dimension)
        )
        for target_id in set(entry_ids)
    }
    entry_self_diagonal = sum(
        (dot(vector, vector) for vector in grouped_entry_vectors.values()),
        F(0),
    )
    nonprincipal_entry_diagonal = (
        F(modulus - 1, modulus) * entry_self_diagonal
    )
    nonprincipal_offdiagonal = nonprincipal - nonprincipal_entry_diagonal
    return {
        "no_sector_aliasing": True,
        "cluster_square_function": cluster_square,
        "normalized_all_character_energy": normalized_character_energy,
        "finite_parseval_exact": cluster_square == normalized_character_energy,
        "original_global_gram": global_gram,
        "principal_character_energy": principal,
        "nonprincipal_character_energy": nonprincipal,
        "nonprincipal_character_energy_nonnegative": nonprincipal >= 0,
        "entry_self_diagonal_energy": entry_self_diagonal,
        "nonprincipal_entry_diagonal_energy": nonprincipal_entry_diagonal,
        "nonprincipal_offdiagonal_energy": nonprincipal_offdiagonal,
        "nonprincipal_diagonal_split_exact": (
            nonprincipal
            == nonprincipal_entry_diagonal + nonprincipal_offdiagonal
        ),
        "sector_character_is_trivial_on_entry_diagonal": True,
        "original_entry_groups_recombined": original_entry_ids is not None,
    }


def sector_character_correlation_coefficients(
    *,
    cluster_vectors: dict[int, tuple[Fraction, ...]],
) -> dict[str, object]:
    """Expand sector-character energy into cluster-offset correlations.

    The character variable is denoted xi so it is not confused with the
    original AFE product a_AFE=h*delta.  For
    ``A_xi=sum_b e(xi*b/M)S_b`` one has formally

    ``||A_xi||^2=sum_u e(xi*u/M) C_u`` with
    ``C_u=sum_b <S_(b+u),S_b>``.

    Banded packet geometry limits the number of offsets but does not make
    the resulting fixed-degree trigonometric polynomial decay with ``a``.
    Orthogonal nonzero cluster vectors give the exact counterexample
    ``C_0=sum_b||S_b||^2`` and ``C_u=0`` for every ``u!=0``; the character
    energy is then constant at every frequency.
    """
    if not cluster_vectors:
        raise ValueError("at least one cluster vector is required")
    dimensions = {len(vector) for vector in cluster_vectors.values()}
    if len(dimensions) != 1:
        raise ValueError("all cluster vectors must have one dimension")

    def dot(
        left: tuple[Fraction, ...],
        right: tuple[Fraction, ...],
    ) -> Fraction:
        return sum((F(x) * F(y) for x, y in zip(left, right)), F(0))

    sectors = sorted(cluster_vectors)
    offsets = range(min(sectors) - max(sectors), max(sectors) - min(sectors) + 1)
    correlations = {
        offset: sum(
            (
                dot(cluster_vectors[b + offset], cluster_vectors[b])
                for b in sectors
                if b + offset in cluster_vectors
            ),
            F(0),
        )
        for offset in offsets
    }
    correlations = {
        offset: value
        for offset, value in correlations.items()
        if value != 0
    }
    offzero_vanish = all(offset == 0 for offset in correlations)
    constant_energy = correlations.get(0, F(0)) if offzero_vanish else None
    return {
        "correlation_coefficients": correlations,
        "offzero_correlations_vanish": offzero_vanish,
        "character_energy_is_frequency_independent": offzero_vanish,
        "constant_character_energy": constant_energy,
        "nonzero_character_alone_supplies_saving": False,
    }


def sector_principal_absorption_audit(
    *,
    modulus: int,
    bandwidth: int,
) -> dict[str, Fraction | int | bool | None]:
    """Audit absorption of the sector principal character.

    If banded overlap gives ``E <= L * cluster_square`` and Parseval gives
    ``cluster_square = E/M + N_nonzero``, then

    ``(1-L/M)E <= L*N_nonzero``.

    For ``M>=2L`` the original Gram therefore satisfies
    ``E<=2L*N_nonzero``.  No independent estimate of the sector principal
    character is required; it is a small feedback copy of the quantity on
    the left.
    """
    if modulus <= 0:
        raise ValueError("modulus must be positive")
    if bandwidth < 0:
        raise ValueError("bandwidth must be nonnegative")
    overlap = 2 * bandwidth + 1
    feedback = F(overlap, modulus)
    denominator = F(1) - feedback
    absorbable = denominator > 0
    exact_multiplier = F(overlap) / denominator if absorbable else None
    twice_overlap = F(2 * overlap)
    return {
        "bounded_overlap_constant": overlap,
        "principal_feedback_coefficient": feedback,
        "absorption_denominator": denominator,
        "exact_nonprincipal_multiplier": exact_multiplier,
        "twice_overlap_upper_multiplier": twice_overlap,
        "modulus_at_least_twice_overlap": modulus >= 2 * overlap,
        "principal_mode_absorbable": absorbable,
        "zero_sector_frequency_requires_separate_bound": not absorbable,
    }


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


def inverse_multiplier_unit_fibre_max(
    modulus: int,
    multiplier: int,
) -> int:
    """Largest fibre of ``x -> multiplier*inverse(x) mod modulus``."""

    if modulus < 1 or multiplier == 0:
        raise ValueError("require a positive modulus and nonzero multiplier")
    fibres: dict[int, int] = {}
    for residue in range(modulus):
        if gcd(residue, modulus) != 1:
            continue
        image = (multiplier * pow(residue, -1, modulus)) % modulus
        fibres[image] = fibres.get(image, 0) + 1
    return max(fibres.values(), default=0)


def frequency_gcd_sum_identity(
    *,
    modulus: int,
    cutoff: int,
) -> FrequencyGcdSumIdentity:
    """Evaluate ``sum_{l<=L} (l,q)`` by its exact divisor expansion."""

    if modulus < 1 or cutoff < 0:
        raise ValueError("require a positive modulus and nonnegative cutoff")
    divisors = tuple(
        divisor
        for divisor in range(1, modulus + 1)
        if modulus % divisor == 0
    )
    totients = {
        divisor: sum(
            1 for residue in range(1, divisor + 1)
            if gcd(residue, divisor) == 1
        )
        for divisor in divisors
    }
    direct = sum(gcd(frequency, modulus) for frequency in range(1, cutoff + 1))
    expanded = sum(
        totients[divisor] * (cutoff // divisor) for divisor in divisors
    )
    divisor_count = len(divisors)
    return FrequencyGcdSumIdentity(
        modulus=modulus,
        cutoff=cutoff,
        direct_gcd_sum=direct,
        divisor_totient_sum=expanded,
        divisor_count=divisor_count,
        linear_divisor_bound=cutoff * divisor_count,
    )


def transition_bblr_hard_h_completion_audit(
    *,
    poisson_gcd_exponent: Fraction,
) -> TransitionBBLRHardHCompletionAudit:
    """Complete the shift before estimating BBLR's hard remainder.

    In the all-unsigned hard cell, equation (14) has
    ``A=B=1, M1=M2=N1=N2=H=T``.  Write
    ``d=(m1,n1)=T^eta``, ``m1=d*m`` and ``n1=d*n``.  The new shift
    variable has length ``H/d`` and its additive phase has modulus ``n``;
    both have exponent ``1-eta``.  Poisson summation in the shift gives a
    rapidly decaying weight in ``l*inverse(m) mod n``.

    As ``m`` varies, inversion permutes the units modulo ``n`` and
    multiplication by ``l`` has fibres bounded by ``(l,n)``.  Thus the
    combined ``m,h`` sum has exponent ``1-eta`` up to ``T^epsilon``, not
    the trivial ``2-2*eta``.  The remaining n count contributes
    ``1-eta`` and the Fourier integral F in equation (14) contributes
    ``eta``.  For fixed d this is ``2-eta``; the d shell has ``T^eta``
    members, leaving exponent 2.

    Equation (14)'s nonzero-frequency cutoff is ``L=T^epsilon/d``, so
    every fixed positive-power d shell is actually empty.  This controls
    only the nonzero Poisson frequencies: the l=0 main term still needs
    its full Möbius/outer-scale recombination.
    """

    eta = F(poisson_gcd_exponent)
    if eta < F(0) or eta > F(1):
        raise ValueError("Poisson gcd exponent must lie in [0,1]")
    reduced = F(1) - eta
    l_cutoff = -eta
    n_count = reduced
    completed_m_h = reduced
    integral = eta
    fixed_d = n_count + completed_m_h + integral
    d_count = eta
    layer = fixed_d + d_count
    target = F(2)
    return TransitionBBLRHardHCompletionAudit(
        poisson_gcd_exponent=eta,
        reduced_h_length_exponent=reduced,
        reduced_modulus_exponent=reduced,
        h_length_matches_modulus=True,
        nonzero_l_cutoff_exponent=l_cutoff,
        positive_power_gcd_shell_has_no_nonzero_l=(eta > 0),
        reduced_n1_count_exponent=n_count,
        completed_m1_h_exponent=completed_m_h,
        poisson_integral_exponent=integral,
        fixed_gcd_value_exponent=fixed_d,
        poisson_gcd_count_exponent=d_count,
        dyadic_layer_exponent=layer,
        global_nonzero_frequency_exponent=layer,
        target_exponent=target,
        power_margin=target - layer,
        inverse_map_is_permutation_on_units=True,
        multiplier_fibre_bound_is_gcd=True,
        nonzero_frequency_error_closed_with_epsilon_loss=(layer <= target),
        poisson_main_term_controlled=False,
        whole_unsigned_cell_covered=False,
        source=(
            "Bettin--Bui--Li--Radziwill, arXiv:1609.02539v1, "
            "Proposition 3.1 equations (14)--(16), h completed first"
        ),
    )


def transition_bblr_h_completion_subcell_audit(
    *,
    outer_a_exponent: Fraction,
    outer_b_exponent: Fraction,
    m1_exponent: Fraction,
    m2_exponent: Fraction,
    n1_exponent: Fraction,
    n2_exponent: Fraction,
    shift_exponent: Fraction,
) -> TransitionBBLRHCompletionSubcellAudit:
    """Exact nonzero-frequency coverage test after completing h first.

    In the BBLR orientation ``B*N1<=A*M1``, put

    ``X=a*m1/d`` and ``Y=b*n1/d``.

    For fixed d, the factorizations of X and Y have divisor-bounded
    multiplicity, so arbitrary outer coefficients (including every
    Möbius atom) are harmless.  Completing the h sum and then summing X
    through its residue classes modulo Y costs

    ``max(Y,H) * (1 + X/Y)``

    up to ``T^epsilon`` and the gcd fibre of the nonzero frequency l.
    The remaining continuous Poisson integral has scale ``M2/Y``.  The
    exact identity

    ``sum_{l<=L} (l,Y) = sum_{r|Y} phi(r) floor(L/r)``

    bounds the whole frequency gcd average by ``L*tau(Y)``, rather than
    the pointwise ``L^2`` cost.  At d=1 the resulting exponent is

    ``M2 + max(0,X-Y) + max(Y,H) + max(0,L)``,

    where ``L=A+M1-N2`` is the exponent of equation (14)'s l cutoff.
    Positive d exponents only shorten L, so this is the global maximum.
    If L<0, the nonzero-frequency family is empty on that subcell.

    This is an error-term adapter only.  The l=0 Poisson main term remains
    a separate outer-scale recombination obligation.
    """

    a = F(outer_a_exponent)
    b = F(outer_b_exponent)
    m1 = F(m1_exponent)
    m2 = F(m2_exponent)
    n1 = F(n1_exponent)
    n2 = F(n2_exponent)
    h = F(shift_exponent)
    if min(a, b, m1, m2, n1, n2, h) < 0:
        raise ValueError("BBLR subcell exponents must be nonnegative")
    if m1 > m2 or n1 > n2:
        raise ValueError("require the BBLR orderings M1<=M2 and N1<=N2")
    left_product = a + m1 + m2
    right_product = b + n1 + n2
    if left_product != right_product:
        raise ValueError("the two BBLR side products must balance")

    x = a + m1
    y = b + n1
    ratio = max(F(0), x - y)
    h_or_modulus = max(h, y)
    l_cutoff = a + m1 - n2
    frequency_gcd = max(F(0), l_cutoff)
    orientation_verified = y <= x
    family_empty = l_cutoff < 0
    bound = m2 + ratio + h_or_modulus + frequency_gcd
    target = left_product
    covered = orientation_verified and (family_empty or bound <= target)
    return TransitionBBLRHCompletionSubcellAudit(
        outer_a_exponent=a,
        outer_b_exponent=b,
        m1_exponent=m1,
        m2_exponent=m2,
        n1_exponent=n1,
        n2_exponent=n2,
        shift_exponent=h,
        left_side_product_exponent=left_product,
        right_side_product_exponent=right_product,
        x_product_exponent=x,
        y_modulus_exponent=y,
        x_over_y_excess_exponent=ratio,
        h_or_modulus_exponent=h_or_modulus,
        nonzero_l_base_cutoff_exponent=l_cutoff,
        summed_frequency_gcd_exponent=frequency_gcd,
        chosen_orientation_hypothesis_verified=orientation_verified,
        nonzero_frequency_family_empty=family_empty,
        global_nonzero_frequency_exponent=bound,
        target_exponent=target,
        power_margin=target - bound,
        nonzero_frequency_cell_covered=covered,
        outer_coefficients_may_be_arbitrary=True,
        factorization_multiplicity_is_divisor_bounded=True,
        frequency_gcd_average_is_divisor_bounded=True,
        preserves_two_mobius_weights_in_outer_coefficients=True,
        poisson_main_term_controlled=False,
        whole_type_subcell_covered=False,
        source=(
            "Bettin--Bui--Li--Radziwill, arXiv:1609.02539v1, "
            "Proposition 3.1 equation (14), h completed before Watt"
        ),
    )


def transition_bblr_zero_main_term_audit(
    *,
    side_product_exponent: Fraction,
    shift_exponent: Fraction,
    poisson_gcd_exponent: Fraction,
) -> TransitionBBLRZeroMainTermAudit:
    """Count BBLR's phase-free ``l=0`` main term before recombination.

    Let each balanced side have product exponent ``P`` and let
    ``d=T^eta``.  Reindexing by ``X=a*m1/d`` and ``Y=b*n1/d`` gives
    divisor-bounded factorization multiplicity.  The X and Y counts, the
    shift length ``H/d`` and the integral length ``d*M2/(B*N1)`` have
    total exponent ``P+alpha-2*eta`` for a fixed d.  A dyadic d layer
    contains ``T^eta`` values, so its exponent is ``P+alpha-eta`` and
    the global maximum is ``P+alpha`` at d of subpower size.

    The BBLR main term is the same for the plus and minus shifted
    equations because setting l=0 deletes their only orientation phase.
    This is a raw-size ledger, not the missing outer-scale estimate.
    """

    product = F(side_product_exponent)
    shift = F(shift_exponent)
    eta = F(poisson_gcd_exponent)
    if product < 0 or shift < 0:
        raise ValueError("BBLR product and shift exponents must be nonnegative")
    if eta < 0 or eta > shift:
        raise ValueError("Poisson gcd exponent must lie in [0,shift]")
    fixed = product + shift - 2 * eta
    layer = fixed + eta
    global_raw = product + shift
    return TransitionBBLRZeroMainTermAudit(
        side_product_exponent=product,
        shift_exponent=shift,
        poisson_gcd_exponent=eta,
        fixed_gcd_exponent=fixed,
        dyadic_gcd_layer_exponent=layer,
        global_raw_main_term_exponent=global_raw,
        target_exponent=product,
        power_margin=product - global_raw,
        missing_saving_exponent=shift,
        main_term_is_independent_of_shift_orientation=True,
        shift_orientations_cancel_internally=False,
        registered_zero_master_identification_proved=False,
        source=(
            "Bettin--Bui--Li--Radziwill, arXiv:1609.02539v1, "
            "Proposition 3.1 l=0 main term"
        ),
    )


def transition_bblr_symmetric_h_completion_audit(
    *,
    outer_a_exponent: Fraction,
    outer_b_exponent: Fraction,
    m1_exponent: Fraction,
    m2_exponent: Fraction,
    n1_exponent: Fraction,
    n2_exponent: Fraction,
    shift_exponent: Fraction,
) -> TransitionBBLRSymmetricHCompletionAudit:
    """Take the better of the two symmetric BBLR h-completions.

    Put ``x=a+m1``, ``y=b+n1`` and let both side products equal ``P``.
    Proposition 3.1 swaps the two sides before assuming ``y<=x``.  In
    that orientation the h-first bound simplifies to

    ``P + max(0,alpha-y) + max(0,x+y-P)``.

    Taking the better orientation therefore replaces y by ``min(x,y)``.
    Below ``x+y=P`` the nonzero l-family is empty; on the boundary the
    exact coverage condition is ``min(x,y)>=alpha``; above it this
    completion retains the positive excess ``x+y-P``.
    """

    a = F(outer_a_exponent)
    b = F(outer_b_exponent)
    m1 = F(m1_exponent)
    m2 = F(m2_exponent)
    n1 = F(n1_exponent)
    n2 = F(n2_exponent)
    shift = F(shift_exponent)
    if min(a, b, m1, m2, n1, n2, shift) < 0:
        raise ValueError("BBLR subcell exponents must be nonnegative")
    if m1 > m2 or n1 > n2:
        raise ValueError("require the BBLR orderings M1<=M2 and N1<=N2")
    product = a + m1 + m2
    if product != b + n1 + n2:
        raise ValueError("the two BBLR side products must balance")

    x = a + m1
    y = b + n1
    smaller = min(x, y)
    excess = x + y - product
    shortfall = max(F(0), shift - smaller)
    frequency_excess = max(F(0), excess)
    bound = product + shortfall + frequency_excess
    family_empty = excess < 0
    covered = family_empty or bound <= product
    return TransitionBBLRSymmetricHCompletionAudit(
        left_prefix_exponent=x,
        right_prefix_exponent=y,
        smaller_prefix_exponent=smaller,
        side_product_exponent=product,
        shift_exponent=shift,
        cutoff_hyperplane_excess=excess,
        smaller_prefix_shortfall=shortfall,
        chosen_orientation=(
            "left_to_right" if x >= y else "right_to_left"
        ),
        nonzero_frequency_family_empty=family_empty,
        symmetric_nonzero_frequency_exponent=bound,
        target_exponent=product,
        power_margin=product - bound,
        boundary_coverage_conditions_hold=(
            excess == 0 and smaller >= shift
        ),
        nonzero_frequency_cell_covered=covered,
        source=(
            "Bettin--Bui--Li--Radziwill, arXiv:1609.02539v1, "
            "Proposition 3.1 equation (14), better symmetric orientation"
        ),
    )


def transition_bblr_phase_group_saving_audit(
    *,
    side_product_exponent: Fraction,
    shift_exponent: Fraction,
    left_prefix_exponent: Fraction,
    right_prefix_exponent: Fraction,
) -> TransitionBBLRPhaseGroupSavingAudit:
    """Record the exact saving demanded from supercritical phase classes.

    On the symmetric region where both prefixes are at least the shift
    exponent, the h-first bound exceeds the local target only by
    ``lambda=x+y-P``, exactly the nonzero-l range exponent.  A generic
    Cauchy/large-sieve square root can register only ``lambda/2``.  The
    other half must therefore come from signed cross terms inside the full
    reciprocal-phase collision classes (or an earlier exact
    recombination), not from partitioning rows by h*delta alone.
    """

    product = F(side_product_exponent)
    shift = F(shift_exponent)
    x = F(left_prefix_exponent)
    y = F(right_prefix_exponent)
    if min(product, shift, x, y) < 0:
        raise ValueError("BBLR phase-group exponents must be nonnegative")
    if min(x, y) < shift:
        raise ValueError("phase-group ledger requires both prefixes >= shift")
    l_range = x + y - product
    if l_range <= 0:
        raise ValueError("phase-group ledger requires a supercritical l-range")
    raw = product + l_range
    square_root = l_range / 2
    remaining = l_range - square_root
    return TransitionBBLRPhaseGroupSavingAudit(
        side_product_exponent=product,
        shift_exponent=shift,
        left_prefix_exponent=x,
        right_prefix_exponent=y,
        nonzero_l_range_exponent=l_range,
        raw_nonzero_frequency_exponent=raw,
        target_exponent=product,
        required_l_range_saving_exponent=l_range,
        square_root_l_saving_exponent=square_root,
        remaining_after_square_root_exponent=remaining,
        signed_phase_class_cross_terms_required=True,
        product_frequency_partition_is_sufficient=False,
        required_phase_class_cancellation_proved=False,
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


def _finite_prime_exponents(n: int) -> dict[int, int]:
    """Return the exact prime-exponent dictionary of a positive integer."""
    if n <= 0:
        raise ValueError("factorization input must be positive")
    exponents: dict[int, int] = {}
    remaining = n
    prime = 2
    while prime * prime <= remaining:
        while remaining % prime == 0:
            exponents[prime] = exponents.get(prime, 0) + 1
            remaining //= prime
        prime += 1
    if remaining > 1:
        exponents[remaining] = exponents.get(remaining, 0) + 1
    return exponents


def mobius_log_derivative_prime_coordinate_identity(
    *,
    n: int,
) -> dict[str, dict[int, int] | bool]:
    """Verify ``-mu(n)log n=(mu*Lambda)(n)`` without real logs.

    The coefficient of ``log p`` on the left is
    ``-mu(n)*v_p(n)``.  On the convolution side it is

    ``sum_(1<=j<=v_p(n)) mu(n/p^j)``,

    because ``Lambda(p^j)=log p``.  Comparing these integer coordinates
    proves the finite identity exactly, including nonsquarefree ``n``.
    """
    if n <= 0:
        raise ValueError("n must be positive")
    exponents = _finite_prime_exponents(n)
    mu_n = _finite_mobius(n)
    left = {
        prime: -mu_n * exponent
        for prime, exponent in exponents.items()
    }
    right = {
        prime: sum(
            _finite_mobius(n // (prime**power))
            for power in range(1, exponent + 1)
        )
        for prime, exponent in exponents.items()
    }
    return {
        "left_prime_log_coefficients": left,
        "right_prime_log_coefficients": right,
        "prime_coordinate_identity_exact": left == right,
    }


def farey_single_mobius_type_identity(
    *,
    q: int,
    b: int,
    k: int,
    s: int,
) -> dict[str, object]:
    """Apply the exact one-Mobius log identity on one Farey fiber.

    At critical resolution ``s<=q`` the sector fiber is empty or contains
    one ``w``.  For ``r=k*s+w`` the identity becomes

    ``-mu(s)mu(r)log r = sum_(d*m=r) mu(s)mu(d)Lambda(m)``.

    The first Mobius factor, sector label, and exact packet entry are not
    changed.  Only ``mu(r)`` is decomposed.  The returned Type terms record
    ``(d,m,mu(s),mu(d),p)`` whenever ``m`` is a power of the prime ``p``.
    """
    if k < 0:
        raise ValueError("k must be nonnegative")
    fiber = farey_sector_fiber_ledger(q=q, b=b, s=s)
    if not fiber.members:
        return {
            "sector_fiber_nonempty": False,
            "sector_character_label_retained": b,
            "one_mobius_factor_only": True,
        }
    if len(fiber.members) != 1:
        raise ValueError("critical Farey Type identity requires s<=q")

    w = fiber.members[0]
    r = k * s + w
    log_identity = mobius_log_derivative_prime_coordinate_identity(n=r)
    type_terms: list[tuple[int, int, int, int, int]] = []
    mu_s = _finite_mobius(s)
    for d in _positive_divisors(r):
        m = r // d
        m_factors = _finite_prime_exponents(m)
        if len(m_factors) == 1:
            prime = next(iter(m_factors))
            type_terms.append((d, m, mu_s, _finite_mobius(d), prime))
    return {
        "sector_fiber_nonempty": True,
        "w": w,
        "r": r,
        "sector_membership_exact": b * s <= q * w < (b + 1) * s,
        "retained_first_mobius": mu_s,
        "left_prime_log_coefficients": log_identity[
            "left_prime_log_coefficients"
        ],
        "right_prime_log_coefficients": log_identity[
            "right_prime_log_coefficients"
        ],
        "prime_coordinate_identity_exact": log_identity[
            "prime_coordinate_identity_exact"
        ],
        "type_terms": tuple(type_terms),
        "one_mobius_factor_only": True,
        "sector_character_label_retained": b,
    }


def farey_global_mobius_type_partition(
    *,
    q: int,
    k: int,
    sector_character: int,
    denominators: tuple[int, ...],
    h: int,
    delta: int,
    short_cutoff: int,
    packet_label: str,
) -> dict[str, object]:
    """Reassemble all critical Farey sectors before one-Mobius Type splitting.

    For every supplied ``s<=q``, the nonempty sector fibers biject with the
    primitive wedge ``0<=w<s``.  On ``r=k*s+w`` the prime-coordinate identity

    ``-mu(s)mu(r)log(r) = sum_(d*m=r) mu(s)mu(d)Lambda(m)``

    is accumulated by sector before any character evaluation.  Each prime
    power term is Type I when ``min(d,m)<=short_cutoff`` and Type II otherwise.
    The partition is finite and exact; it deliberately proves no estimate.
    """

    if q <= 1:
        raise ValueError("a nonzero sector character requires q>1")
    if k < 0:
        raise ValueError("k must be nonnegative")
    if not 0 < sector_character < q:
        raise ValueError("sector_character must be nonzero modulo q")
    if short_cutoff < 1:
        raise ValueError("short_cutoff must be positive")
    if not denominators:
        raise ValueError("at least one denominator is required")
    if any(s < 1 or s > q for s in denominators):
        raise ValueError("critical Farey denominators must lie in [1,q]")

    entries: list[tuple[int, int, int, int]] = []
    type_i_terms: list[dict[str, object]] = []
    type_ii_terms: list[dict[str, object]] = []
    left: dict[tuple[int, int], int] = {}
    right: dict[tuple[int, int], int] = {}
    squarefree_left: dict[tuple[int, int], int] = {}
    squarefree_right: dict[tuple[int, int], int] = {}
    product_frequency = h * delta

    for s in denominators:
        for b in range(q):
            fiber = farey_sector_fiber_ledger(q=q, b=b, s=s)
            for w in fiber.members:
                r = k * s + w
                if r < 1 or gcd(r, s) != 1:
                    continue
                entries.append((b, s, w, r))
                mu_s = _finite_mobius(s)
                mu_r = _finite_mobius(r)
                for prime, exponent in _finite_prime_exponents(r).items():
                    key = (b, prime)
                    left[key] = left.get(key, 0) - mu_s * mu_r * exponent
                    if mu_r != 0:
                        squarefree_left[key] = (
                            squarefree_left.get(key, 0)
                            - mu_s * mu_r * exponent
                        )
                    for power in range(1, exponent + 1):
                        prime_power = prime**power
                        type_divisor = r // prime_power
                        mu_d = _finite_mobius(type_divisor)
                        right[key] = right.get(key, 0) + mu_s * mu_d
                        if mu_r != 0:
                            squarefree_right[key] = (
                                squarefree_right.get(key, 0) + mu_s * mu_d
                            )
                        type_class = (
                            "I"
                            if min(type_divisor, prime_power) <= short_cutoff
                            else "II"
                        )
                        term = {
                            "packet_label": packet_label,
                            "sector_character": sector_character,
                            "sector": b,
                            "denominator": s,
                            "shifted_numerator": w,
                            "numerator": r,
                            "type_divisor": type_divisor,
                            "prime_power": prime_power,
                            "denominator_mobius": mu_s,
                            "divisor_mobius": mu_d,
                            "prime": prime,
                            "h": h,
                            "delta": delta,
                            "product_frequency": product_frequency,
                            "type_class": type_class,
                        }
                        if type_class == "I":
                            type_i_terms.append(term)
                        else:
                            type_ii_terms.append(term)

    entries.sort(key=lambda entry: (entry[1], entry[2], entry[0]))
    expected_entries = sorted(
        (
            (
                q * w // s,
                s,
                w,
                k * s + w,
            )
            for s in denominators
            for w in range(s)
            if k * s + w >= 1 and gcd(k * s + w, s) == 1
        ),
        key=lambda entry: (entry[1], entry[2], entry[0]),
    )
    all_terms = type_i_terms + type_ii_terms
    nonzero_mollifier_terms = tuple(
        term
        for term in all_terms
        if term["denominator_mobius"] != 0
        and _finite_mobius(int(term["numerator"])) != 0
    )
    return {
        "primitive_entries": tuple(entries),
        "product_frequency": product_frequency,
        "nonzero_sector_character_retained": 0 < sector_character < q,
        "packet_label_retained": packet_label,
        "all_sector_fibers_reassemble_primitive_wedge": (
            entries == expected_entries
        ),
        "left_prime_coordinates": left,
        "right_prime_coordinates": right,
        "global_log_identity_exact": left == right,
        "squarefree_left_prime_coordinates": squarefree_left,
        "squarefree_right_prime_coordinates": squarefree_right,
        "squarefree_supported_global_identity_exact": (
            squarefree_left == squarefree_right
        ),
        "type_i_terms": tuple(type_i_terms),
        "type_ii_terms": tuple(type_ii_terms),
        "type_i_term_count": len(type_i_terms),
        "type_ii_term_count": len(type_ii_terms),
        "all_type_terms_partitioned_without_remainder": (
            len(all_terms) == sum(
                exponent
                for _, _, _, r in entries
                for exponent in _finite_prime_exponents(r).values()
            )
        ),
        "nonzero_mollifier_support_term_count": len(nonzero_mollifier_terms),
        "prime_power_is_prime_on_nonzero_mollifier_support": all(
            term["prime_power"] == term["prime"]
            for term in nonzero_mollifier_terms
        ),
        "two_mobius_weights_retained_in_every_type_term": all(
            "denominator_mobius" in term and "divisor_mobius" in term
            for term in all_terms
        ),
        "type_estimate_proved": False,
    }


def farey_global_type_scale_ledger(
    *,
    numerator_exponent: Fraction,
    cutoff_exponent: Fraction,
) -> dict[str, object]:
    """Record the critical Type-I/II ranges and their remaining saving.

    The transition cluster family has exponent one, with exponent one
    entries per cluster.  Coherent energy therefore has exponent three,
    while the target square function has exponent two.  Splitting the
    exact packet does not by itself reduce either sector's worst-case
    cardinality, so a separate estimate must save one power in energy,
    equivalently one half-power before squaring.
    """

    n = F(numerator_exponent)
    u = F(cutoff_exponent)
    if n <= 0:
        raise ValueError("the numerator exponent must be positive")
    if u <= 0 or 2 * u >= n:
        raise ValueError("the cutoff must lie strictly between 0 and n/2")

    coherent_energy = F(3)
    target_energy = F(2)
    required_energy = coherent_energy - target_energy
    return {
        "type_i_short_factor_range": (F(0), u),
        "type_i_long_factor_range": (n - u, n),
        "type_ii_divisor_range": (u, n - u),
        "type_ii_prime_range": (u, n - u),
        "coherent_cluster_energy_exponent": coherent_energy,
        "square_function_target_exponent": target_energy,
        "required_energy_saving_exponent": required_energy,
        "required_unsquared_saving_exponent": required_energy / 2,
        "product_frequency_retained": "h*delta",
        "two_mobius_weights_retained": "mu(s)*mu(d)",
        "type_ii_prime_bearing_on_squarefree_support": True,
        "type_i_bound_proved": False,
        "type_ii_bound_proved": False,
        "combined_gate_proved": False,
    }


def farey_type_i_unit_divisor_shifted_prime_reassembly(
    *,
    q: int,
    sector_character: int,
    denominators: tuple[int, ...],
    h: int,
    delta: int,
    packet_label: str,
) -> dict[str, object]:
    """Reindex the most favorable Type-I subpacket by its prime shift.

    This selects the ``d=1`` terms on nonzero mollifier support from the
    unit-slope packet ``p=s+w``.  Regrouping by ``w`` gives the exact
    shifted-prime coordinate ``mu(s)=mu(p-w)``.  The Farey sector label
    remains ``floor(q*w/(p-w))`` and can therefore vary with ``p`` even
    after the shift ``w`` is fixed.  No estimate is asserted.
    """

    partition = farey_global_mobius_type_partition(
        q=q,
        k=1,
        sector_character=sector_character,
        denominators=denominators,
        h=h,
        delta=delta,
        short_cutoff=1,
        packet_label=packet_label,
    )
    terms = tuple(
        term
        for term in partition["type_i_terms"]
        if term["type_divisor"] == 1
        and term["prime_power"] == term["numerator"]
        and term["denominator_mobius"] != 0
        and _finite_mobius(int(term["numerator"])) != 0
    )
    entries = tuple(
        (
            int(term["sector"]),
            int(term["denominator"]),
            int(term["shifted_numerator"]),
            int(term["prime"]),
            int(term["denominator_mobius"]),
        )
        for term in terms
    )
    left_coordinates = {
        (b, s, w, prime): mu_s for b, s, w, prime, mu_s in entries
    }
    shifted_coordinates = {
        (q * w // (prime - w), prime - w, w, prime): _finite_mobius(
            prime - w
        )
        for _, _, w, prime, _ in entries
    }
    sector_labels_by_shift: dict[int, set[int]] = {}
    for b, _, w, _, _ in entries:
        sector_labels_by_shift.setdefault(w, set()).add(b)
    sector_phase_varies = any(
        len(labels) > 1 for labels in sector_labels_by_shift.values()
    )
    afe_weight_moves_with_entry = bool(entries)
    return {
        "unit_divisor_entries": entries,
        "shifted_prime_reassembly_exact": (
            left_coordinates == shifted_coordinates
        ),
        "prime_equals_denominator_plus_shift": all(
            prime == s + w for _, s, w, prime, _ in entries
        ),
        "mobius_is_negative_prime_shift_exact": all(
            mu_s == _finite_mobius(prime - w)
            for _, _, w, prime, mu_s in entries
        ),
        "product_frequency": h * delta,
        "packet_label_retained": partition["packet_label_retained"],
        "sector_character_retained": sector_character,
        "shift_one_sector_labels": tuple(
            sorted(sector_labels_by_shift.get(1, set()))
        ),
        "sector_phase_varies_after_fixing_shift": sector_phase_varies,
        "afe_weight_depends_on_shift_and_prime": afe_weight_moves_with_entry,
        "lichtman_fixed_weight_hypothesis_matched": (
            not sector_phase_varies and not afe_weight_moves_with_entry
        ),
        "type_i_estimate_proved": False,
    }


def lichtman_shifted_prime_type_i_coverage_audit(
    *,
    prime_length_exponent: Fraction,
    shift_length_exponent: Fraction,
    required_unsquared_saving_exponent: Fraction,
) -> dict[str, object]:
    """Compare Lichtman's shifted-prime average with the Type-I gate.

    Lichtman, Theorem 1.1 (arXiv:2009.08969v2), averages absolute values
    over shifts.  In the polynomial regime it saves a power of ``log X``
    (up to ``1/3-delta``), not a positive power of ``X``.  The present
    packet also has a shift-dependent Farey/AFE weight and needs a vector
    cluster square estimate.  This ledger records those theorem-level
    mismatches without treating them as a disproof of a stronger result.
    """

    x = F(prime_length_exponent)
    shift = F(shift_length_exponent)
    required = F(required_unsquared_saving_exponent)
    if x <= 0 or shift <= 0:
        raise ValueError("prime and shift length exponents must be positive")
    if required < 0:
        raise ValueError("the required saving exponent must be nonnegative")
    published_power = F(0)
    return {
        "source": "Lichtman, arXiv:2009.08969v2, Theorem 1.1 and Lemma 6.1",
        "published_average_norm": "L1 over shifts",
        "required_average_norm": "vector cluster L2",
        "published_saving_kind": "logarithmic",
        "published_log_saving_exponent_supremum": F(1, 3),
        "published_power_saving_exponent": published_power,
        "required_unsquared_saving_exponent": required,
        "remaining_power_deficit": max(F(0), required - published_power),
        "strict_shift_range_h_less_x": shift < x,
        "fixed_weight_across_shifts": False,
        "norm_hypothesis_matched": False,
        "covers_type_i_gate": False,
    }


def trigonometric_grid_aliasing_sides(
    *,
    q: int,
    coefficients: dict[int, Fraction],
) -> dict[str, object]:
    """Expand normalized Q-grid energy into exact Fourier alias classes.

    For ``F(b)=sum_k c_k e(k*b/q)``, character orthogonality gives

    ``q^-1 sum_b |F(b)|^2 = sum_(k1=k2 mod q) c_k1*c_k2``.

    The right side is the sum of squared coefficient sums in every residue
    class.  Its zero-alias part is the continuous Fourier energy; all
    distinct frequencies differing by a nonzero multiple of ``q`` form the
    alias cross term.  Coefficients are exact rationals, so no numerical
    roots of unity are used.
    """

    if q <= 0:
        raise ValueError("q must be positive")
    if not coefficients:
        raise ValueError("at least one Fourier coefficient is required")
    exact = {
        int(frequency): F(value)
        for frequency, value in coefficients.items()
    }
    residue_groups: dict[int, list[tuple[int, Fraction]]] = {}
    for frequency, coefficient in exact.items():
        residue_groups.setdefault(frequency % q, []).append(
            (frequency, coefficient)
        )
    for group in residue_groups.values():
        group.sort()

    continuous = sum((value * value for value in exact.values()), F(0))
    residue_sums = tuple(
        (
            residue,
            sum((value for _, value in group), F(0)),
        )
        for residue, group in sorted(residue_groups.items())
    )
    discrete = sum((value * value for _, value in residue_sums), F(0))
    expanded = sum(
        (
            left_value * right_value
            for group in residue_groups.values()
            for _, left_value in group
            for _, right_value in group
        ),
        F(0),
    )
    max_multiplicity = max(len(group) for group in residue_groups.values())
    cauchy_majorant = max_multiplicity * continuous
    return {
        "modulus": q,
        "continuous_fourier_energy": continuous,
        "residue_class_sums": residue_sums,
        "zero_alias_diagonal_energy": continuous,
        "nonzero_alias_cross_energy": expanded - continuous,
        "discrete_grid_energy": discrete,
        "expanded_collision_energy": expanded,
        "discrete_parseval_identity_verified": discrete == expanded,
        "max_alias_multiplicity": max_multiplicity,
        "cauchy_alias_majorant": cauchy_majorant,
        "alias_majorant_verified": discrete <= cauchy_majorant,
    }


def technau_zafeiropoulos_grid_coverage_audit(
    *,
    value_length_exponent: Fraction,
    fourier_truncation_exponent: Fraction,
    slope_grid_exponent: Fraction,
    coefficient_l2_energy_exponent: Fraction,
    target_energy_exponent: Fraction,
) -> dict[str, object]:
    """Audit continuous metric Beatty L2 against the rational slope grid.

    The classical finite polynomial displayed as (3.1) in
    Technau--Zafeiropoulos has frequencies ``k=m*j`` with ``m<=X`` and
    ``|j|<=sqrt(X)``.  Sampling a bandwidth ``K`` polynomial on only ``Q``
    rational slopes permits ``K/Q`` frequencies in one alias class.  This
    ledger records the generic sampling loss for the optimistic scalar
    surrogate; it does not claim that every structured coefficient
    saturates that loss.  The published theorem also keeps one arithmetic
    function fixed while the slope moves.  The actual second Mobius weight
    depends on the Beatty preimage, so a separate finite collision ledger
    shows that this fixed-function adapter already fails before sampling.
    """

    x = F(value_length_exponent)
    truncation = F(fourier_truncation_exponent)
    grid = F(slope_grid_exponent)
    coefficient_energy = F(coefficient_l2_energy_exponent)
    target = F(target_energy_exponent)
    if min(x, truncation, grid, coefficient_energy, target) < 0:
        raise ValueError("all scale exponents must be nonnegative")
    bandwidth = x + truncation
    alias_multiplicity = max(F(0), bandwidth - grid)
    continuous_total = grid + coefficient_energy
    generic_sampled = continuous_total + alias_multiplicity
    return {
        "source": (
            "Technau--Zafeiropoulos, arXiv:1907.06050, "
            "Theorem 2.1, Corollary 4.4, and equation (3.1)"
        ),
        "trigonometric_bandwidth_exponent": bandwidth,
        "slope_grid_exponent": grid,
        "alias_multiplicity_exponent": alias_multiplicity,
        "continuous_slope_total_energy_exponent": continuous_total,
        "generic_sampled_energy_exponent": generic_sampled,
        "target_energy_exponent": target,
        "remaining_energy_deficit": max(F(0), generic_sampled - target),
        "published_slope_average": "continuous Lebesgue",
        "actual_slope_average": "Q-point rational grid",
        "continuous_metric_l2_reaches_target": continuous_total <= target,
        "second_index_mobius_supported": False,
        "fixed_arithmetic_function_across_slopes_supported": False,
        "finite_fixed_f_collision_exhibited": True,
        "afe_product_frequency_interlaces_sector_grid": False,
        "type_packet_fourier_adapter_constructed": False,
        "structured_nonzero_alias_cancellation_required": (
            alias_multiplicity > 0
        ),
        "covers_coupled_type_gate": False,
    }


def structured_beatty_sobolev_sampling_audit(
    *,
    value_length_exponent: Fraction,
    fourier_truncation_exponent: Fraction,
    slope_grid_exponent: Fraction,
    coefficient_l2_energy_exponent: Fraction,
    target_energy_exponent: Fraction,
    epsilon: Fraction,
) -> dict[str, object]:
    """Exploit the divisor-convolution Fourier coefficients before sampling.

    The Beatty polynomial is not an arbitrary bandwidth-XJ polynomial:

    a_k = sum_(m*j=k) g_m*c_j,  with  |c_j| << 1/|j|.

    For h-separated nodes, the Hilbert-valued Sobolev sampling inequality
    at order sigma>1/2 bounds the normalized sampled energy by

    ||F||_2^2 + h^(2*sigma)|| |D|^sigma F||_2^2.

    Divisor Cauchy and |c_j|<=1/j give, up to a T^eta divisor loss,

    h^(2*sigma)|| |D|^sigma F||_2^2
      << T^(2*sigma*(X-grid))
         J^(2*sigma-1) sum_m ||g_m||^2.

    At X=grid and J=T^(1/2), choose sigma=1/2+epsilon/4.
    The grid then costs only T^epsilon, even for nonuniform separated
    nodes.  This removes the generic bandwidth alias loss for a fixed
    Hilbert coefficient family.  It does not make the actual moving
    two-Mobius packet fixed across slopes.
    """
    x = F(value_length_exponent)
    truncation = F(fourier_truncation_exponent)
    grid = F(slope_grid_exponent)
    coefficient_energy = F(coefficient_l2_energy_exponent)
    target = F(target_energy_exponent)
    eps = F(epsilon)
    if min(x, truncation, grid, coefficient_energy, target) < 0:
        raise ValueError("all scale exponents must be nonnegative")
    if eps <= 0:
        raise ValueError("epsilon must be positive")

    sobolev_slack = eps / 4
    sobolev_order = F(1, 2) + sobolev_slack
    positive_length_mismatch = max(F(0), x - grid)
    length_mismatch_loss = 2 * sobolev_order * positive_length_mismatch
    harmonic_decay_loss = truncation * (2 * sobolev_order - 1)
    divisor_convolution_loss = eps / 4
    normalized_sample_loss = (
        length_mismatch_loss
        + harmonic_decay_loss
        + divisor_convolution_loss
    )
    structured_sampled = (
        grid + coefficient_energy + normalized_sample_loss
    )
    target_with_epsilon = target + eps
    return {
        "source": (
            "Technau--Zafeiropoulos arXiv:1907.06050 equation (3.1), "
            "plus Hilbert Sobolev sampling and divisor Cauchy"
        ),
        "fourier_coefficient_shape": "a_k=sum_(m*j=k) g_m*c_j",
        "harmonic_coefficient_decay": "|c_j|<=C/|j|",
        "sobolev_order": sobolev_order,
        "sobolev_slack": sobolev_slack,
        "value_grid_length_mismatch_exponent": positive_length_mismatch,
        "length_mismatch_loss_exponent": length_mismatch_loss,
        "harmonic_decay_loss_exponent": harmonic_decay_loss,
        "divisor_convolution_loss_budget": divisor_convolution_loss,
        "normalized_sampling_loss_exponent": normalized_sample_loss,
        "structured_sampled_energy_exponent": structured_sampled,
        "target_energy_with_epsilon_exponent": target_with_epsilon,
        "generic_bandwidth_alias_loss_is_necessary": False,
        "nonuniform_separated_nodes_supported": True,
        "hilbert_valued_fixed_coefficients_supported": True,
        "structured_sampling_reaches_target": (
            structured_sampled <= target_with_epsilon
        ),
        "actual_packet_fixed_across_slopes": False,
        "moving_two_mobius_vector_adapter_constructed": False,
        "covers_coupled_type_gate": False,
    }


def beatty_divisor_fourier_coefficient_sides(
    *,
    coefficient_vectors: dict[int, tuple[Fraction, ...]],
    harmonic_weights: dict[int, Fraction],
    frequency_power: int = 0,
) -> dict[str, object]:
    """Verify finite Hilbert divisor Cauchy for product frequencies.

    For positive value indices m and nonzero harmonics j, form

    a_k = sum_(m*j=k) g_m*c_j.

    At each k, Hilbert-space Cauchy bounds the square norm of the sum by
    the number of represented divisors times the sum of termwise square
    norms.  Multiplication by the nonnegative integer weight |k|^p keeps
    the inequality exact over rational vectors.
    """
    if not coefficient_vectors or not harmonic_weights:
        raise ValueError("coefficient vectors and harmonic weights are required")
    if frequency_power < 0:
        raise ValueError("the frequency power must be nonnegative")
    if any(index <= 0 for index in coefficient_vectors):
        raise ValueError("value indices must be positive")
    if 0 in harmonic_weights:
        raise ValueError("the zero harmonic is not part of the discrepancy")
    dimensions = {len(vector) for vector in coefficient_vectors.values()}
    if dimensions == {0} or len(dimensions) != 1:
        raise ValueError("all coefficient vectors need one positive dimension")
    dimension = next(iter(dimensions))

    terms_by_frequency: dict[int, list[tuple[Fraction, ...]]] = {}
    for m, vector in coefficient_vectors.items():
        for j, weight in harmonic_weights.items():
            term = tuple(F(weight) * F(value) for value in vector)
            terms_by_frequency.setdefault(m * j, []).append(term)

    coefficients: list[tuple[int, tuple[Fraction, ...]]] = []
    energy = F(0)
    cauchy_majorant = F(0)
    max_representations = 0
    for frequency, terms in sorted(terms_by_frequency.items()):
        coefficient = tuple(
            sum((term[coordinate] for term in terms), F(0))
            for coordinate in range(dimension)
        )
        coefficients.append((frequency, coefficient))
        frequency_weight = F(abs(frequency) ** frequency_power)
        energy += frequency_weight * sum(
            (value * value for value in coefficient),
            F(0),
        )
        representation_count = len(terms)
        max_representations = max(max_representations, representation_count)
        cauchy_majorant += frequency_weight * representation_count * sum(
            (
                sum((value * value for value in term), F(0))
                for term in terms
            ),
            F(0),
        )

    return {
        "fourier_coefficients": tuple(coefficients),
        "frequency_power": frequency_power,
        "weighted_fourier_energy": energy,
        "divisor_cauchy_majorant": cauchy_majorant,
        "max_product_representations": max_representations,
        "divisor_cauchy_bound_verified": energy <= cauchy_majorant,
        "hilbert_vector_identity_exact": True,
    }


def farey_beatty_chowla_projector_sides(
    *,
    q: int,
    k: int,
    labelled_entry_vectors: dict[
        tuple[int, int, str], tuple[Fraction, ...]
    ],
    determinant_zero_energy: Fraction,
) -> dict[str, object]:
    """Form the exact moving-Beatty Hilbert square function.

    A key ``(s,w,label)`` represents one retained packet vector on the
    primitive entry ``r=k*s+w``.  The vector enters sector
    ``b=floor(q*w/s)`` with its full coefficient ``mu(s)*mu(r)``.  Thus

    ``X_b=sum_(floor(q*w/s)=b) mu(s)mu(k*s+w) G_(s,w,label)``.

    Finite character orthogonality gives the nonprincipal projector

    ``sum_b ||X_b||^2 - q^-1 ||sum_b X_b||^2``.

    If the already recombined determinant-zero contribution ``D`` is
    nonnegative, the signed nonzero-determinant part is ``J=projector-D``
    and hence ``J<=projector``.  Thus the centered projector bound is the
    positive one-sided gate; bounding ``sum_b||X_b||^2`` is a stronger
    sufficient condition.  This helper verifies the finite implication
    only; it proves no uniform analytic estimate.
    """

    if q <= 1:
        raise ValueError("a nonprincipal sector projector requires q>1")
    if k < 0:
        raise ValueError("k must be nonnegative")
    if not labelled_entry_vectors:
        raise ValueError("at least one labelled entry vector is required")
    determinant_zero = F(determinant_zero_energy)
    if determinant_zero < 0:
        raise ValueError("the determinant-zero energy must be nonnegative")

    dimensions = {len(vector) for vector in labelled_entry_vectors.values()}
    if dimensions == {0} or len(dimensions) != 1:
        raise ValueError("all entry vectors need one common positive dimension")
    dimension = next(iter(dimensions))

    sector_vectors: dict[int, list[Fraction]] = {}
    labels_by_sector: dict[int, set[str]] = {}
    coefficient_ledger: list[tuple[int, int, str, int, int, int]] = []
    for (s, w, label), vector in labelled_entry_vectors.items():
        if s < 1 or s > q:
            raise ValueError("critical denominators must lie in [1,q]")
        if w < 0 or w >= s:
            raise ValueError("the Beatty numerator must lie in [0,s)")
        if not label:
            raise ValueError("every packet label must be nonempty")
        r = k * s + w
        if r < 1 or gcd(r, s) != 1:
            raise ValueError("every supplied Farey entry must be positive and primitive")
        sector = q * w // s
        coefficient = _finite_mobius(s) * _finite_mobius(r)
        target = sector_vectors.setdefault(sector, [F(0)] * dimension)
        for index, value in enumerate(vector):
            target[index] += F(coefficient) * F(value)
        labels_by_sector.setdefault(sector, set()).add(label)
        coefficient_ledger.append((s, w, label, r, sector, coefficient))

    exact_sector_vectors = tuple(
        (sector, tuple(vector))
        for sector, vector in sorted(sector_vectors.items())
    )

    def norm_square(vector: tuple[Fraction, ...] | list[Fraction]) -> Fraction:
        return sum((F(value) * F(value) for value in vector), F(0))

    def dot(
        left: tuple[Fraction, ...],
        right: tuple[Fraction, ...],
    ) -> Fraction:
        return sum(
            (F(x) * F(y) for x, y in zip(left, right)),
            F(0),
        )

    same_sector = sum(
        (norm_square(vector) for _, vector in exact_sector_vectors),
        F(0),
    )
    total_vector = tuple(
        sum((vector[index] for _, vector in exact_sector_vectors), F(0))
        for index in range(dimension)
    )
    principal = norm_square(total_vector) / q
    projector = same_sector - principal
    orthogonality_pair_expansion = sum(
        (
            (F(1) if left_sector == right_sector else F(0)) - F(1, q)
        )
        * dot(left_vector, right_vector)
        for left_sector, left_vector in exact_sector_vectors
        for right_sector, right_vector in exact_sector_vectors
    )
    signed_nonzero = projector - determinant_zero
    return {
        "q": q,
        "k": k,
        "entry_coefficients": tuple(sorted(coefficient_ledger)),
        "sector_vectors": exact_sector_vectors,
        "labels_by_sector": tuple(
            (sector, tuple(sorted(labels)))
            for sector, labels in sorted(labels_by_sector.items())
        ),
        "same_sector_energy": same_sector,
        "principal_energy": principal,
        "nonprincipal_projector_energy": projector,
        "orthogonality_pair_expansion_energy": orthogonality_pair_expansion,
        "weakest_positive_gate_energy": projector,
        "determinant_zero_energy": determinant_zero,
        "signed_nonzero_determinant_energy": signed_nonzero,
        "finite_character_parseval_exact": (
            projector == orthogonality_pair_expansion
        ),
        "projector_bounded_by_same_sector_energy": (
            F(0) <= projector <= same_sector
        ),
        "same_sector_gate_is_stronger": projector <= same_sector,
        "signed_nonzero_bounded_by_projector": signed_nonzero <= projector,
        "one_sided_nonzero_determinant_bound_implied": (
            signed_nonzero <= same_sector
        ),
        "two_mobius_coefficients_retained": all(
            coefficient == _finite_mobius(s) * _finite_mobius(k * s + w)
            for s, w, _, _, _, coefficient in coefficient_ledger
        ),
        "all_packet_labels_retained": (
            sum(len(labels) for labels in labels_by_sector.values())
            <= len(labelled_entry_vectors)
            and {
                label for _, _, label in labelled_entry_vectors
            }
            == {
                label
                for labels in labels_by_sector.values()
                for label in labels
            }
        ),
        "analytic_square_function_bound_proved": False,
    }


def beatty_chowla_power_gate_audit(
    *,
    entry_length_exponent: Fraction,
    sector_count_exponent: Fraction,
    target_energy_exponent: Fraction,
) -> dict[str, object]:
    """Compare the exact Beatty square gate with published Chowla results.

    A coherent length-``T^n`` vector in each of ``T^q`` sectors has energy
    exponent ``q+2n``.  The target therefore requires half of the energy
    saving before squaring.  Crncevic et al. prove a qualitative
    logarithmic limit for ``lambda(n)lambda(floor(alpha*n))`` at one fixed
    irrational alpha.  Teravainen--Walker subsume that result and treat
    two fixed inhomogeneous Beatty slopes, including their rational
    resonant classification.  Neither paper gives a uniform power saving
    on the moving rational Q-grid or a Hilbert-valued packet square
    function.
    """

    entry = F(entry_length_exponent)
    sectors = F(sector_count_exponent)
    target = F(target_energy_exponent)
    if min(entry, sectors, target) < 0:
        raise ValueError("all scale exponents must be nonnegative")
    coherent = sectors + 2 * entry
    required_energy = max(F(0), coherent - target)
    required_unsquared = required_energy / 2
    published_power = F(0)
    return {
        "sources": (
            (
                "Crncevic--Hernandez--Rizk--Sereesuchart--Tao, "
                "arXiv:2211.15830v4, Theorem B"
            ),
            "Teravainen--Walker, arXiv:2303.12574v1, Theorem 1.2",
        ),
        "coherent_energy_exponent": coherent,
        "target_energy_exponent": target,
        "required_energy_saving_exponent": required_energy,
        "required_unsquared_saving_exponent": required_unsquared,
        "published_power_saving_exponent": published_power,
        "remaining_unsquared_power_deficit": max(
            F(0), required_unsquared - published_power
        ),
        "crncevic_result_is_subsumed_by_teravainen_walker": True,
        "published_average": "logarithmic qualitative limit",
        "published_slope_regime": (
            "fixed slopes: irrational cancellation and rational resonance "
            "classification"
        ),
        "actual_slope_regime": "moving rational Q-grid",
        "rational_resonance_requires_prior_diagonal_extraction": True,
        "mobius_pair_power_bound_published": False,
        "hilbert_packet_square_function_published": False,
        "uniform_moving_grid_bound_published": False,
        "covers_one_sided_joint_type_gate": False,
    }


def primitive_beatty_fourier_boundary_sides(
    *,
    q: int,
    k: int,
    labelled_entry_vectors: dict[
        tuple[int, int, str], tuple[Fraction, ...]
    ],
) -> dict[str, object]:
    """Isolate the jump boundary in the sector-step Fourier series.

    The step function ``e_q(xi*floor(q*x))`` is discontinuous exactly at
    ``q*x`` integral.  On a primitive Farey entry ``x=w/s`` this means

    ``s | q*w`` and ``gcd(w,s)=1``, hence ``s | q``.

    More precisely, primitive boundary entries are the reduced fractions
    of ``b/q`` for ``0<=b<q``.  The map

    ``b -> (s,w)=(q/gcd(b,q), b/gcd(b,q))``

    is a bijection, including ``b=0 -> (1,0)``.  Thus every sector has
    exactly one primitive jump entry.  Once all outer labels on an
    original entry are recombined, its same-sector energy is literally
    the corresponding diagonal sub-sum; no Mobius cancellation or
    Cauchy loss is needed.  Supplied vectors are understood to include
    whatever scalar jump and packet coefficients the application uses.
    """

    if q <= 0:
        raise ValueError("q must be positive")
    if k < 0:
        raise ValueError("k must be nonnegative")
    if not labelled_entry_vectors:
        raise ValueError("at least one labelled entry vector is required")
    dimensions = {len(vector) for vector in labelled_entry_vectors.values()}
    if dimensions == {0} or len(dimensions) != 1:
        raise ValueError("all entry vectors need one common positive dimension")
    dimension = next(iter(dimensions))

    canonical: list[tuple[int, int, int]] = []
    for sector in range(q):
        common = gcd(sector, q)
        s = q // common
        w = sector // common
        canonical.append((sector, s, w))

    enumerated = tuple(
        sorted(
            (q * w // s, s, w)
            for s in range(1, q + 1)
            for w in range(s)
            if gcd(k * s + w, s) == 1 and (q * w) % s == 0
        )
    )
    canonical_entries = tuple(canonical)
    primitive_equivalence = all(
        ((q * w) % s == 0) == (q % s == 0)
        for s in range(1, q + 1)
        for w in range(s)
        if gcd(k * s + w, s) == 1
    )
    divisors = tuple(s for s in range(1, q + 1) if q % s == 0)
    totient_sum = sum(
        sum(1 for w in range(s) if gcd(w, s) == 1)
        for s in divisors
    )

    combined_by_entry: dict[tuple[int, int], list[Fraction]] = {}
    labels_by_entry: dict[tuple[int, int], set[str]] = {}
    supplied_boundary_label_count = 0
    for (s, w, label), vector in labelled_entry_vectors.items():
        if s < 1 or s > q or w < 0 or w >= s:
            raise ValueError("entry coordinates must satisfy 1<=s<=q and 0<=w<s")
        if not label:
            raise ValueError("every packet label must be nonempty")
        if gcd(k * s + w, s) != 1:
            raise ValueError("every supplied Farey entry must be primitive")
        if (q * w) % s != 0:
            continue
        supplied_boundary_label_count += 1
        key = (s, w)
        target = combined_by_entry.setdefault(key, [F(0)] * dimension)
        for index, value in enumerate(vector):
            target[index] += F(value)
        labels_by_entry.setdefault(key, set()).add(label)

    def norm_square(vector: tuple[Fraction, ...] | list[Fraction]) -> Fraction:
        return sum((F(value) * F(value) for value in vector), F(0))

    supplied_sector_vectors = tuple(
        sorted(
            (q * w // s, tuple(vector))
            for (s, w), vector in combined_by_entry.items()
        )
    )
    diagonal = sum(
        (norm_square(vector) for vector in combined_by_entry.values()),
        F(0),
    )
    same_sector = sum(
        (norm_square(vector) for _, vector in supplied_sector_vectors),
        F(0),
    )
    total_vector = tuple(
        sum((vector[index] for _, vector in supplied_sector_vectors), F(0))
        for index in range(dimension)
    )
    principal = norm_square(total_vector) / q
    projector = same_sector - principal
    return {
        "q": q,
        "k": k,
        "canonical_boundary_entries": canonical_entries,
        "enumerated_boundary_entries": enumerated,
        "primitive_boundary_entry_count": len(enumerated),
        "sector_count": q,
        "one_primitive_boundary_entry_per_sector": (
            enumerated == canonical_entries
        ),
        "boundary_iff_denominator_divides_q": primitive_equivalence,
        "totient_divisor_sum": totient_sum,
        "totient_divisor_sum_identity": totient_sum == q,
        "supplied_boundary_sector_vectors": supplied_sector_vectors,
        "recombined_boundary_entry_diagonal_energy": diagonal,
        "boundary_same_sector_energy": same_sector,
        "boundary_principal_energy": principal,
        "boundary_nonprincipal_projector_energy": projector,
        "boundary_energy_bounded_by_recombined_diagonal": (
            F(0) <= projector <= same_sector == diagonal
        ),
        "all_supplied_boundary_labels_recombined_by_entry": (
            sum(len(labels) for labels in labels_by_entry.values())
            == supplied_boundary_label_count
        ),
        "analytic_boundary_layer_reduces_to_known_diagonal": True,
    }


def beatty_sector_fourier_type_phase_ledger(
    *,
    q: int,
    sector_character: int,
    harmonic: int,
    k: int,
    s: int,
    w: int,
    type_divisor: int,
    prime_power: int,
) -> dict[str, object]:
    """Record the exact sector Fourier frequency after one Type split.

    Away from jumps, the ``xi`` sector step has Fourier frequencies
    ``a=xi+j*q``.  If ``d*p=k*s+w``, integrality of ``a*k`` gives

    ``e(a*w/s)=e(a*d*p/s)``.

    This is a direct linear fraction, not an inverse phase.  At a jump
    ``q*w/s`` integral, the half-jump correction must be retained; the
    separate primitive-boundary helper shows that layer is diagonal-sized.
    """

    if q <= 1 or not 0 < sector_character < q:
        raise ValueError("sector_character must be nonzero modulo q")
    if k < 0 or s <= 0 or w < 0 or w >= s:
        raise ValueError("require k>=0, s>0, and 0<=w<s")
    if type_divisor <= 0 or prime_power <= 0:
        raise ValueError("Type factors must be positive")

    frequency = sector_character + harmonic * q
    numerator = k * s + w
    type_relation = type_divisor * prime_power == numerator
    primitive = gcd(numerator, s) == 1
    boundary = (q * w) % s == 0
    phase_difference = frequency * (w - type_divisor * prime_power)
    return {
        "q": q,
        "sector_character": sector_character,
        "harmonic": harmonic,
        "fourier_frequency": frequency,
        "frequency_mod_q": frequency % q,
        "numerator": numerator,
        "type_relation_exact": type_relation,
        "primitive_entry": primitive,
        "integer_slope_part_drops_out": (frequency * k * s) % s == 0,
        "type_linear_fraction_phase_exact": (
            type_relation and phase_difference % s == 0
        ),
        "at_fourier_jump_boundary": boundary,
        "boundary_correction_required": boundary,
        "primitive_boundary_forces_denominator_divides_q": (
            not (primitive and boundary) or q % s == 0
        ),
        "fourier_coefficient_formula": (
            "q*(1-e(-sector_character/q))"
            "/(2*pi*i*(sector_character+harmonic*q))"
        ),
        "zero_fourier_mode_absent": frequency != 0,
    }


def beatty_type_i_additive_large_sieve_audit(
    *,
    divisor_exponent: Fraction,
    denominator_exponent: Fraction,
    sector_modulus_exponent: Fraction,
    target_energy_exponent: Fraction,
) -> dict[str, object]:
    """Audit the standard additive large sieve after sector completion.

    On ``d*p=k*s+w`` with ``s=T^sigma`` and ``d=T^delta``, the
    prime-bearing length is ``P=T^(sigma-delta)``.  For one fixed ``d``,
    Cauchy in ``s`` followed by the additive large sieve on the Farey
    points ``a*d/s`` gives

    ``T^(sigma-q) * (P+S^2) * ||beta||_2^2``.

    The first factor is the denominator Cauchy count divided by the
    sector-character normalization ``Q``.  At ``sigma=q=1`` it cancels,
    but ``S^2`` still makes the fixed-d energy ``T^(3-delta)``.  Even
    granting perfect orthogonality among the ``T^delta`` divisors leaves
    exponent three.  Ordinary Cauchy in ``d`` is worse.  This ledger is
    optimistic: it assumes the packet has already been separated into a
    common prime coefficient family.  Hence failure here rules out the
    standard large sieve as a closure, but is not a lower bound for every
    possible joint dispersion argument.
    """

    delta = F(divisor_exponent)
    sigma = F(denominator_exponent)
    q_scale = F(sector_modulus_exponent)
    target = F(target_energy_exponent)
    if min(delta, sigma, q_scale, target) < 0:
        raise ValueError("all scale exponents must be nonnegative")
    if delta > sigma:
        raise ValueError("the Type divisor cannot exceed the numerator scale")

    prime_length = sigma - delta
    large_sieve_constant = max(prime_length, 2 * sigma)
    prime_coefficient_energy = prime_length
    denominator_cauchy_minus_average = sigma - q_scale
    fixed_divisor = (
        denominator_cauchy_minus_average
        + large_sieve_constant
        + prime_coefficient_energy
    )
    optimistic_divisor_orthogonality = fixed_divisor + delta
    divisor_cauchy = fixed_divisor + 2 * delta
    remaining = max(F(0), optimistic_divisor_orthogonality - target)
    return {
        "divisor_exponent": delta,
        "denominator_exponent": sigma,
        "sector_modulus_exponent": q_scale,
        "prime_bearing_length_exponent": prime_length,
        "farey_large_sieve_constant_exponent": large_sieve_constant,
        "prime_coefficient_l2_energy_exponent": prime_coefficient_energy,
        "denominator_cauchy_minus_sector_average_exponent": (
            denominator_cauchy_minus_average
        ),
        "fixed_divisor_energy_exponent": fixed_divisor,
        "optimistic_dyadic_divisor_orthogonality_energy_exponent": (
            optimistic_divisor_orthogonality
        ),
        "cauchy_over_divisors_energy_exponent": divisor_cauchy,
        "target_energy_exponent": target,
        "remaining_energy_deficit_even_with_divisor_orthogonality": remaining,
        "remaining_unsquared_deficit": remaining / 2,
        "sector_average_normalization_cancels_denominator_cauchy_count": (
            sigma == q_scale
        ),
        "common_prime_coefficient_family_assumed_optimistically": True,
        "requires_joint_mobius_or_determinant_dispersion": remaining > 0,
        "standard_additive_large_sieve_covers_type_i": (
            optimistic_divisor_orthogonality <= target
        ),
    }


def beatty_afe_type_kloosterman_phase_ledger(
    *,
    sector_modulus: int,
    sector_character: int,
    harmonic: int,
    denominator: int,
    quotient: int,
    remainder: int,
    type_divisor: int,
    prime_power: int,
    h: int,
    delta: int,
) -> dict[str, object]:
    """Recombine the sector harmonic with the original AFE inverse phase.

    Put ``r=d*p=k*s+w`` and ``alpha=xi+j*Q``.  The sector completion
    supplies ``e_s(alpha*w)``, while the exact Poisson packet already
    contains ``e_s(-h*delta*inverse(r))``.  Since ``alpha*k`` is integral,

    ``alpha*w-h*delta*inverse(r)``
    ``=alpha*d*p-h*delta*inverse(d)*inverse(p) (mod s)``.

    Thus the continuous Type-I prime-bearing variable has the genuine
    nonhomogeneous Kloosterman phase ``e_s(B*p+A*inverse(p))`` with
    ``B=alpha*d`` and ``A=-h*delta*inverse(d)``.  No ``h*delta`` label or
    either Mobius factor is spent in deriving the identity.
    """

    if sector_modulus <= 1:
        raise ValueError("sector_modulus must exceed one")
    if not 0 < sector_character < sector_modulus:
        raise ValueError("sector_character must be nonzero modulo Q")
    if denominator <= 1 or quotient < 0:
        raise ValueError("require denominator>1 and quotient>=0")
    if remainder < 0 or remainder >= denominator:
        raise ValueError("require 0<=remainder<denominator")
    if type_divisor <= 0 or prime_power <= 0:
        raise ValueError("Type factors must be positive")
    if h == 0 or delta == 0:
        raise ValueError("the nonzero Poisson packet requires h*delta nonzero")

    frequency = sector_character + harmonic * sector_modulus
    numerator = quotient * denominator + remainder
    if type_divisor * prime_power != numerator:
        raise ValueError("the exact Type relation d*p=k*s+w is required")
    if gcd(numerator, denominator) != 1:
        raise ValueError("the Farey/Type entry must be primitive")

    inverse_numerator = pow(numerator, -1, denominator)
    inverse_divisor = pow(type_divisor, -1, denominator)
    inverse_prime = pow(prime_power, -1, denominator)
    afe_product = h * delta
    left_phase = (
        frequency * remainder - afe_product * inverse_numerator
    ) % denominator
    direct_coefficient = (frequency * type_divisor) % denominator
    inverse_coefficient = (-afe_product * inverse_divisor) % denominator
    right_phase = (
        direct_coefficient * prime_power
        + inverse_coefficient * inverse_prime
    ) % denominator
    korolev_gcd = gcd(direct_coefficient * inverse_coefficient, denominator)
    invariant_gcd = gcd(frequency * afe_product, denominator)
    return {
        "sector_modulus": sector_modulus,
        "sector_character": sector_character,
        "harmonic": harmonic,
        "fourier_frequency": frequency,
        "denominator": denominator,
        "quotient": quotient,
        "remainder": remainder,
        "numerator": numerator,
        "type_divisor": type_divisor,
        "prime_power": prime_power,
        "afe_product": afe_product,
        "type_relation_exact": type_divisor * prime_power == numerator,
        "primitive_entry": gcd(numerator, denominator) == 1,
        "sector_phase_numerator_mod_denominator": (
            frequency * remainder
        ) % denominator,
        "afe_inverse_phase_numerator_mod_denominator": (
            -afe_product * inverse_numerator
        ) % denominator,
        "combined_original_phase_mod_denominator": left_phase,
        "prime_kloosterman_direct_coefficient_mod_denominator": (
            direct_coefficient
        ),
        "prime_kloosterman_inverse_coefficient_mod_denominator": (
            inverse_coefficient
        ),
        "combined_type_phase_mod_denominator": right_phase,
        "combined_phase_exact_mod_denominator": left_phase == right_phase,
        "korolev_coefficient_product_gcd": korolev_gcd,
        "frequency_times_afe_gcd": invariant_gcd,
        "korolev_unit_condition_equivalent_to_frequency_times_afe_unit": (
            korolev_gcd == invariant_gcd
        ),
        "korolev_unit_condition_holds": korolev_gcd == 1,
        "both_mobius_weights_retained": True,
        "retained_mobius_factors": ("mu(denominator)", "mu(type_divisor)"),
        "afe_factorization_retained": True,
        "retained_afe_factors": (h, delta),
        "phase_class": "nonhomogeneous_prime_kloosterman",
    }


def korolev_prime_kloosterman_type_i_audit(
    *,
    modulus_exponent: Fraction,
    type_divisor_exponent: Fraction,
    required_unsquared_saving: Fraction,
) -> dict[str, object]:
    """Map Korolev's prime-Kloosterman theorem to one Type-I slice.

    Korolev, arXiv:1911.09981, Theorem 1, bounds the von-Mangoldt sum

    ``sum Lambda(p) e_q(A*inverse(p)+B*p)``

    by ``X*q^eps*Delta`` for ``q^(3/4+eps)<=X<=q^(3/2)``, where

    ``Delta=(q^(3/4)/X)^(1/7)+(q^(2/3)/X)^(3/35)``.

    With ``q=T^sigma`` and ``p=T^(sigma-delta)``, the two saving
    exponents are ``(pi-3*sigma/4)/7`` and
    ``3*(pi-2*sigma/3)/35``.  At the most favorable full-length point
    ``pi=sigma`` their minimum is only ``sigma/35``.  The theorem is
    pointwise in the modulus and coefficients; it supplies no joint
    moment over the sector character, ``h*delta``, or the outer Mobius
    modulus, so it cannot by itself prove the coupled square-function
    gate even on a numerically sufficient slice.
    """

    sigma = F(modulus_exponent)
    divisor = F(type_divisor_exponent)
    required = F(required_unsquared_saving)
    if sigma <= 0:
        raise ValueError("modulus_exponent must be positive")
    if divisor < 0 or divisor > sigma:
        raise ValueError("Type divisor exponent must lie in [0,sigma]")
    if required < 0:
        raise ValueError("required saving must be nonnegative")

    prime_length = sigma - divisor
    lower_endpoint = 3 * sigma / 4
    transition = 7 * sigma / 8
    upper_endpoint = 3 * sigma / 2
    published_range = lower_endpoint < prime_length <= upper_endpoint
    branch_one = max(F(0), (prime_length - lower_endpoint) / 7)
    branch_two = max(F(0), 3 * (prime_length - 2 * sigma / 3) / 35)
    saving = min(branch_one, branch_two) if published_range else F(0)
    remaining = max(F(0), required - saving)
    return {
        "source": "Korolev, arXiv:1911.09981, Theorem 1",
        "modulus_exponent": sigma,
        "type_divisor_exponent": divisor,
        "prime_length_exponent": prime_length,
        "published_lower_endpoint_exponent": lower_endpoint,
        "published_transition_exponent": transition,
        "published_upper_endpoint_exponent": upper_endpoint,
        "published_range_holds": published_range,
        "strict_positive_epsilon_above_lower_endpoint_required": True,
        "first_delta_term_saving_exponent": branch_one,
        "second_delta_term_saving_exponent": branch_two,
        "korolev_saving_exponent": saving,
        "two_branches_meet": branch_one == branch_two,
        "required_unsquared_saving": required,
        "remaining_unsquared_deficit": remaining,
        "saving_meets_required": published_range and saving >= required,
        "von_mangoldt_type_weight_matches": True,
        "smooth_dyadic_weight_reachable_by_partial_summation": True,
        "requires_unit_direct_and_inverse_coefficients": True,
        "joint_sector_character_moment_provided": False,
        "joint_h_delta_moment_provided": False,
        "outer_mobius_modulus_average_provided": False,
        "pointwise_theorem_covers_coupled_gate": False,
    }


def fkm_prime_modulus_kloosterman_type_i_audit(
    *,
    modulus_exponent: Fraction,
    type_divisor_exponent: Fraction,
    required_unsquared_saving: Fraction,
) -> dict[str, object]:
    """Audit Fouvry--Kowalski--Michel on the prime-modulus Type-I slice.

    For prime modulus ``p``, the function
    ``K(x)=e_p(B*x+A*inverse(x))`` with ``A`` nonzero is a bounded-
    conductor, nonexceptional trace weight.  The smoothed form of
    Fouvry--Kowalski--Michel, arXiv:1211.6043v3, Theorem 1.5, is

    ``sum_{l prime} K(l)V(l/X) << X(1+p/X)^(1/6)p^(-eta)``,

    for every ``eta<1/24``.  With ``p=T^sigma`` and
    ``X=T^pi<=p``, the limiting relative saving is
    ``sigma/24-(sigma-pi)/6 = pi/6-sigma/8``.  It is positive only
    for ``pi>3*sigma/4`` and reaches at most ``sigma/24``.  The strict
    ``eta<1/24`` is recorded by calling this a limiting exponent, not
    an attained endpoint.
    """

    sigma = F(modulus_exponent)
    divisor = F(type_divisor_exponent)
    required = F(required_unsquared_saving)
    if sigma <= 0:
        raise ValueError("modulus_exponent must be positive")
    if divisor < 0 or divisor > sigma:
        raise ValueError("Type divisor exponent must lie in [0,sigma]")
    if required < 0:
        raise ValueError("required saving must be nonnegative")

    prime_length = sigma - divisor
    trace_penalty = max(F(0), sigma - prime_length) / 6
    limiting_trace_saving = sigma / 24
    limiting_saving = max(F(0), limiting_trace_saving - trace_penalty)
    power_range = prime_length > 3 * sigma / 4
    remaining = max(F(0), required - limiting_saving)
    return {
        "source": (
            "Fouvry--Kowalski--Michel, arXiv:1211.6043v3, Theorem 1.5"
        ),
        "modulus_exponent": sigma,
        "type_divisor_exponent": divisor,
        "prime_length_exponent": prime_length,
        "trace_weight_p_power_saving_supremum": limiting_trace_saving,
        "short_length_penalty_exponent": trace_penalty,
        "limiting_saving_exponent": limiting_saving,
        "endpoint_exponent_is_strict_supremum": True,
        "power_saving_range_holds": power_range,
        "required_unsquared_saving": required,
        "remaining_unsquared_deficit": remaining,
        "limiting_saving_meets_required": (
            power_range and limiting_saving >= required
        ),
        "phase_is_nonexceptional_on_unit_inverse_coefficient_stratum": True,
        "smooth_prime_weight_matches_after_log_partial_summation": True,
        "higher_prime_powers_require_separate_trivial_treatment": True,
        "prime_power_tail_trivial_saving_exponent": prime_length / 2,
        "prime_modulus_required": True,
        "composite_squarefree_moduli_covered": False,
        "joint_sector_character_moment_provided": False,
        "joint_h_delta_moment_provided": False,
        "outer_mobius_modulus_average_provided": False,
        "pointwise_theorem_covers_coupled_gate": False,
    }


def fkm_prime_modulus_bilinear_type_ii_audit(
    *,
    modulus_exponent: Fraction,
    first_factor_exponent: Fraction,
    required_unsquared_saving: Fraction,
) -> dict[str, object]:
    """Audit FKM Theorem 1.17 on the prime-modulus product trace.

    For ``K(x)=e_p(B*x+C*inverse(x))`` and arbitrary dyadic
    coefficient sequences of lengths ``M`` and ``N``, Fouvry--Kowalski--
    Michel, arXiv:1211.6043v3, Theorem 1.17, gives the relative factor

    ``p^(-1/4)+M^(-1/2)+p^(1/4)N^(-1/2)``.

    Orient the theorem with ``M`` the shorter factor.  If
    ``p=T^sigma`` and the two product factors have exponents ``v`` and
    ``sigma-v``, the saving is the minimum of

    ``sigma/4, v/2, sigma/4-v/2``.

    It is positive off the exactly balanced point, reaches ``sigma/8``
    at ``v=sigma/4``, and degenerates to zero at ``v=sigma/2``.  The
    one-variable FKM theorems are better very near ``v=0``; their
    limiting saving is ``sigma/24-v/6`` for ``v<sigma/4``.  Neither
    fixed-prime-modulus result includes the outer modulus Mobius average
    or the joint sector and ``h*delta`` moments.
    """

    sigma = F(modulus_exponent)
    first = F(first_factor_exponent)
    required = F(required_unsquared_saving)
    if sigma <= 0:
        raise ValueError("modulus_exponent must be positive")
    if first < 0 or first > sigma:
        raise ValueError("factor exponent must lie in [0,sigma]")
    if required < 0:
        raise ValueError("required saving must be nonnegative")

    short = min(first, sigma - first)
    long = sigma - short
    conductor_term = sigma / 4
    short_term = short / 2
    long_term = long / 2 - sigma / 4
    bilinear_saving = min(conductor_term, short_term, long_term)
    one_variable_saving = (
        sigma / 24 - short / 6 if short < sigma / 4 else F(0)
    )
    best = max(bilinear_saving, one_variable_saving)
    remaining = max(F(0), required - best)
    return {
        "source": (
            "Fouvry--Kowalski--Michel, arXiv:1211.6043v3, "
            "Theorem 1.17"
        ),
        "modulus_exponent": sigma,
        "first_factor_exponent": first,
        "second_factor_exponent": sigma - first,
        "short_factor_exponent": short,
        "long_factor_exponent": long,
        "conductor_term_saving_exponent": conductor_term,
        "short_factor_term_saving_exponent": short_term,
        "long_factor_term_saving_exponent": long_term,
        "bilinear_saving_exponent": bilinear_saving,
        "one_variable_limiting_saving_exponent": one_variable_saving,
        "best_published_prime_slice_saving_exponent": best,
        "required_unsquared_saving": required,
        "remaining_unsquared_deficit": remaining,
        "bilinear_bound_is_power_saving": bilinear_saving > 0,
        "exact_balanced_point_degenerates": short == sigma / 2,
        "maximum_bilinear_saving_exponent": sigma / 8,
        "arbitrary_dyadic_coefficients_accepted": True,
        "product_kloosterman_trace_matches": True,
        "prime_modulus_required": True,
        "composite_squarefree_moduli_covered": False,
        "joint_sector_character_moment_provided": False,
        "joint_h_delta_moment_provided": False,
        "outer_mobius_modulus_average_provided": False,
        "saving_meets_required": best >= required,
        "fixed_prime_modulus_bound_covers_coupled_gate": False,
    }


def product_trace_additive_completion_audit(
    *,
    modulus: int,
    direct_coefficient: int,
    inverse_coefficient: int,
    left_coefficients: dict[int, complex],
    right_coefficients: dict[int, complex],
) -> dict[str, object]:
    """Verify the exact additive completion of a product trace kernel.

    Put ``K(x)=e_q(B*x+C*inverse(x))`` on the units and zero elsewhere.
    With the unnormalised additive Fourier transform,

    ``Khat(h)=S(B-h,C;q)`` and
    ``K(x)=q^(-1) sum_h Khat(h)e_q(h*x)``.

    The routine also opens a finite bilinear form and both Parseval
    identities.  They show precisely why completing to classical
    Kloosterman sums does not itself save a power: the second
    Kloosterman argument is fixed, the new frequency has full length
    ``q``, and Cauchy--Parseval merely returns the original arbitrary-
    coefficient energy.
    """

    q = int(modulus)
    if q < 2:
        raise ValueError("modulus must be at least two")
    if not left_coefficients or not right_coefficients:
        raise ValueError("both coefficient families must be nonempty")

    b = direct_coefficient % q
    c = inverse_coefficient % q
    root = cmath.exp(2j * cmath.pi / q)
    units = tuple(x for x in range(q) if gcd(x, q) == 1)
    kernel = [0j] * q
    for x in units:
        kernel[x] = root ** ((b * x + c * pow(x, -1, q)) % q)

    transform = []
    expected_kloosterman = []
    for h in range(q):
        transform.append(
            sum(kernel[x] * root ** ((-h * x) % q) for x in range(q))
        )
        expected_kloosterman.append(
            sum(
                root
                ** (((b - h) * x + c * pow(x, -1, q)) % q)
                for x in units
            )
        )

    reconstructed = [
        sum(transform[h] * root ** ((h * x) % q) for h in range(q)) / q
        for x in range(q)
    ]
    tolerance = 1e-9

    atoms = [
        (d * p % q, complex(alpha) * complex(beta))
        for d, alpha in left_coefficients.items()
        for p, beta in right_coefficients.items()
    ]
    direct_bilinear = sum(weight * kernel[x] for x, weight in atoms)
    additive_transform = [
        sum(weight * root ** ((h * x) % q) for x, weight in atoms)
        for h in range(q)
    ]
    completed_bilinear = sum(
        transform[h] * additive_transform[h] for h in range(q)
    ) / q

    kloosterman_energy = sum(abs(value) ** 2 for value in transform)
    kernel_energy = q * sum(abs(value) ** 2 for value in kernel)
    additive_energy = sum(abs(value) ** 2 for value in additive_transform)
    incidence_energy = q * sum(
        weight_i * weight_j.conjugate()
        for x_i, weight_i in atoms
        for x_j, weight_j in atoms
        if x_i == x_j
    )

    return {
        "modulus": q,
        "direct_coefficient_mod_modulus": b,
        "inverse_coefficient_mod_modulus": c,
        "unit_coefficients": gcd(b * c, q) == 1,
        "unit_residue_count": len(units),
        "forward_transform_is_kloosterman_sum": max(
            abs(actual - expected)
            for actual, expected in zip(transform, expected_kloosterman)
        )
        < tolerance,
        "inverse_completion_exact": max(
            abs(actual - expected)
            for actual, expected in zip(reconstructed, kernel)
        )
        < tolerance,
        "completed_bilinear_identity_exact": (
            abs(direct_bilinear - completed_bilinear) < tolerance
        ),
        "kloosterman_parseval_exact": (
            abs(kloosterman_energy - kernel_energy) < tolerance
        ),
        "additive_bilinear_parseval_exact": (
            abs(additive_energy - incidence_energy) < tolerance
        ),
        "completion_normalization_denominator": q,
        "completed_frequency_count": q,
        "second_kloosterman_argument_is_fixed": True,
        "first_kloosterman_argument_runs_over_complete_residue_system": True,
        "additive_coefficient_is_product_bilinear_transform": True,
        "pascadi_short_two_argument_adapter_available": False,
        "termwise_weil_completion_worse_than_trivial_at_balance": True,
        "parseval_supplies_power_saving": False,
        "joint_mobius_signs_retained_before_completion": True,
    }


def fkms_rank_one_prime_type_ii_route_audit(
    *,
    modulus_exponent: Fraction,
    first_factor_exponent: Fraction,
    moment_parameter: int,
    required_unsquared_saving: Fraction,
) -> dict[str, object]:
    """Separate the 2026 FKMS rank-one route from a proved theorem row.

    FKMS, arXiv:2511.09459v3, Theorem 1.3(2), proves a quantitative
    Type-II estimate for *gallant* sheaves, hence for rank at least two.
    Section 9.11 says that the same method can handle rank-one kernels
    ``chi(f(x))*psi(g(x))`` and explicitly says the inverse-pole case
    ``g=1/X`` goes through, but it leaves the application-specific
    diagonal-variety verification to the reader.

    This helper records the saving that Theorem 1.3 would give after a
    gallant-strength rank-one adapter.  Direct pole counting does not
    supply such an adapter: at moment order ``m=ceil(l/3)``, the locus
    on which all ``2m`` shifts coincide and both the linear coefficient
    and total reciprocal residue vanish has dimension at least
    ``4m-1``.  The gallant proof needs an exceptional set of dimension
    at most ``3m``.  Thus for ``m>=2`` the formal exponent is not even a
    currently valid rank-one route; a new treatment of this collision
    family would be required.
    """

    sigma = F(modulus_exponent)
    first = F(first_factor_exponent)
    required = F(required_unsquared_saving)
    ell = int(moment_parameter)
    if sigma <= 0:
        raise ValueError("modulus_exponent must be positive")
    if first < 0 or first > sigma:
        raise ValueError("factor exponent must lie in [0,sigma]")
    if ell < 2:
        raise ValueError("moment_parameter must be at least two")
    if required < 0:
        raise ValueError("required saving must be nonnegative")

    short = min(first, sigma - first)
    long = sigma - short
    lower = 3 * sigma / (2 * ell)
    upper = sigma / 2 + 3 * sigma / (4 * ell)
    exponent_range = short > lower and short <= upper and long <= sigma
    first_bracket_saving = long / 2
    second_bracket_saving = (
        sigma - 3 * sigma / 4 - 7 * sigma / (4 * ell)
    ) / (2 * ell)
    formal_saving = (
        max(F(0), min(first_bracket_saving, second_bracket_saving))
        if exponent_range
        else F(0)
    )
    moment_order = (ell + 2) // 3
    required_exceptional_dimension = 3 * moment_order
    collision_dimension = 4 * moment_order - 1
    collision_excess = max(0, collision_dimension - required_exceptional_dimension)
    direct_route_saving = formal_saving if collision_excess == 0 else F(0)
    return {
        "source": (
            "Fouvry--Kowalski--Michel--Sawin, arXiv:2511.09459v3, "
            "Theorem 1.3(2) and Section 9.11"
        ),
        "modulus_exponent": sigma,
        "short_factor_exponent": short,
        "long_factor_exponent": long,
        "moment_parameter": ell,
        "published_exponent_range_would_hold": exponent_range,
        "published_lower_short_factor_exponent": lower,
        "published_upper_short_factor_exponent": upper,
        "first_bracket_saving_exponent": first_bracket_saving,
        "second_bracket_saving_exponent": second_bracket_saving,
        "formal_gallant_formula_saving_exponent": formal_saving,
        "direct_rank_one_route_saving_exponent": direct_route_saving,
        "required_unsquared_saving": required,
        "remaining_unsquared_deficit_under_formal_formula": max(
            F(0), required - formal_saving
        ),
        "remaining_unsquared_deficit_after_registered_bounds": required,
        "gallant_moment_order": moment_order,
        "required_type_ii_exceptional_dimension": (
            required_exceptional_dimension
        ),
        "equal_shift_collision_dimension_lower_bound": collision_dimension,
        "equal_shift_collision_dimension_excess": collision_excess,
        "direct_pole_stratification_supports_formula": collision_excess == 0,
        "published_gallant_theorem_directly_applies": False,
        "gallant_definition_forces_rank_at_least_two": True,
        "kernel_is_rank_one_artin_schreier": True,
        "kernel_has_inverse_pole": True,
        "paper_discusses_rank_one_inverse_pole_method": True,
        "paper_states_quantitative_rank_one_type_ii_theorem": False,
        "rank_one_stratification_adapter_proved_in_source": False,
        "rank_one_stratification_adapter_proved_here": False,
        "registered_prime_slice_saving_exponent": F(0),
        "prime_modulus_required": True,
        "composite_squarefree_moduli_covered": False,
        "joint_sector_character_moment_provided": False,
        "joint_h_delta_moment_provided": False,
        "outer_mobius_modulus_average_provided": False,
        "fixed_prime_modulus_bound_covers_coupled_gate": False,
    }


def fkms_rank_one_type_ii_collision_witness(
    *,
    modulus: int,
    direct_coefficient: int,
    inverse_coefficient: int,
    common_shift: int,
    first_dilations: tuple[int, ...],
    second_dilations: tuple[int, ...],
) -> dict[str, object]:
    """Give an exact finite obstruction to the naive rank-one Type II moment.

    For signs ``(+,...,+,-,...,-)`` and all translations equal to ``r``,
    the Type-II one-variable phase for

    ``K(x)=e_q(B*x+C*inverse(x))``

    is

    ``B*(v+r)*sum eps_j(a_j-b_j)``
    ``+ C*inverse(v+r)*sum eps_j(inverse(a_j)-inverse(b_j))``.

    If the two displayed coefficients vanish, every non-pole summand is
    one even though ``a_j != b_j`` pointwise.  The two equations cut a
    family of local dimension ``4m-1`` including the common translation;
    the gallant Type-II moment argument allows only ``3m`` exceptional
    dimensions.
    """

    q = int(modulus)
    if q < 3 or any(q % p == 0 for p in range(2, isqrt(q) + 1)):
        raise ValueError("modulus must be an odd prime")
    if len(first_dilations) != len(second_dilations):
        raise ValueError("dilation families must have equal length")
    if len(first_dilations) == 0 or len(first_dilations) % 2:
        raise ValueError("each dilation family must have positive even length")

    first = tuple(value % q for value in first_dilations)
    second = tuple(value % q for value in second_dilations)
    if any(value == 0 for value in first + second):
        raise ValueError("all dilations must be units")
    moment_order = len(first) // 2
    signs = (1,) * moment_order + (-1,) * moment_order
    linear = sum(
        sign * (a - b)
        for sign, a, b in zip(signs, first, second)
    ) % q
    residue = sum(
        sign * (pow(a, -1, q) - pow(b, -1, q))
        for sign, a, b in zip(signs, first, second)
    ) % q

    phase_values = {}
    pole = (-common_shift) % q
    for variable in range(q):
        if variable == pole:
            continue
        shifted = (variable + common_shift) % q
        phase_values[variable] = (
            direct_coefficient * shifted * linear
            + inverse_coefficient * pow(shifted, -1, q) * residue
        ) % q

    row_linear = tuple(sign % q for sign in signs) + tuple(
        (-sign) % q for sign in signs
    )
    row_residue = tuple(
        (-sign * pow(a, -2, q)) % q
        for sign, a in zip(signs, first)
    ) + tuple(
        (sign * pow(b, -2, q)) % q
        for sign, b in zip(signs, second)
    )
    if all(value == 0 for value in row_linear + row_residue):
        jacobian_rank = 0
    elif any(
        (row_linear[i] * row_residue[j] - row_linear[j] * row_residue[i])
        % q
        for i in range(len(row_linear))
        for j in range(i + 1, len(row_linear))
    ):
        jacobian_rank = 2
    else:
        jacobian_rank = 1

    collision_dimension = 4 * moment_order + 1 - jacobian_rank
    required_dimension = 3 * moment_order
    root = cmath.exp(2j * cmath.pi / q)
    return {
        "modulus": q,
        "moment_order": moment_order,
        "signs": signs,
        "pointwise_type_ii_exclusion_holds": all(
            a != b for a, b in zip(first, second)
        ),
        "linear_coefficient_mod_modulus": linear,
        "reciprocal_pole_residue_mod_modulus": residue,
        "linear_coefficient_vanishes": linear == 0,
        "pole_residue_vanishes": residue == 0,
        "phase_is_zero_off_common_pole": all(
            value == 0 for value in phase_values.values()
        ),
        "zero_phase_count": sum(
            1 if value == 0 else 0 for value in phase_values.values()
        ),
        "one_variable_sum": sum(
            root**value for value in phase_values.values()
        ),
        "jacobian_rank": jacobian_rank,
        "collision_family_dimension_lower_bound": collision_dimension,
        "gallant_required_exceptional_dimension": required_dimension,
        "dimension_excess": collision_dimension - required_dimension,
        "standard_type_ii_moment_exception_count_can_hold": (
            collision_dimension <= required_dimension
        ),
    }


def rank_one_type_ii_resonance_audit(
    *,
    modulus: int,
    direct_coefficient: int,
    inverse_coefficient: int,
    shifts: tuple[int, ...],
    first_dilations: tuple[int, ...],
    second_dilations: tuple[int, ...],
) -> dict[str, object]:
    """Classify the constant-phase part of a rank-one Type-II moment.

    Put ``eps=(1,...,1,-1,...,-1)`` and

    ``A_j=eps_j*(a_j-b_j)``,
    ``R_j=eps_j*(inverse(a_j)-inverse(b_j))``.

    The complete one-variable phase is constant away from its poles if
    and only if ``sum A_j=0`` and, for every distinct shift ``rho``,
    ``sum_(r_j=rho) R_j=0``.  On that locus its exact contribution is

    ``(q-number_of_distinct_poles)*e_q(B*sum A_j*r_j)``.

    This is the resonant term that must be removed before a square-root
    estimate can be applied to the remaining rational phase.
    """

    q = int(modulus)
    if q < 3 or any(q % p == 0 for p in range(2, isqrt(q) + 1)):
        raise ValueError("modulus must be an odd prime")
    if direct_coefficient % q == 0 or inverse_coefficient % q == 0:
        raise ValueError("both phase coefficients must be units modulo q")
    if not (
        len(shifts) == len(first_dilations) == len(second_dilations)
    ):
        raise ValueError("shift and dilation families must have equal length")
    if len(shifts) == 0 or len(shifts) % 2:
        raise ValueError("families must have positive even length")

    first = tuple(value % q for value in first_dilations)
    second = tuple(value % q for value in second_dilations)
    reduced_shifts = tuple(value % q for value in shifts)
    if any(value == 0 for value in first + second):
        raise ValueError("all dilations must be units")

    moment_order = len(shifts) // 2
    signs = (1,) * moment_order + (-1,) * moment_order
    linear_terms = tuple(
        sign * (a - b) % q
        for sign, a, b in zip(signs, first, second)
    )
    reciprocal_terms = tuple(
        sign * (pow(a, -1, q) - pow(b, -1, q)) % q
        for sign, a, b in zip(signs, first, second)
    )
    distinct_shifts = tuple(sorted(set(reduced_shifts)))
    residues_by_shift = {
        shift: sum(
            reciprocal_terms[index]
            for index, value in enumerate(reduced_shifts)
            if value == shift
        )
        % q
        for shift in distinct_shifts
    }
    linear_slope = sum(linear_terms) % q
    constant_phase = sum(
        coefficient * shift
        for coefficient, shift in zip(linear_terms, reduced_shifts)
    ) % q
    resonance_conditions_hold = (
        linear_slope == 0
        and all(residue == 0 for residue in residues_by_shift.values())
    )

    phases: dict[int, int] = {}
    poles = {(-shift) % q for shift in distinct_shifts}
    for variable in range(q):
        if variable in poles:
            continue
        phase = direct_coefficient * sum(
            coefficient * (variable + shift)
            for coefficient, shift in zip(linear_terms, reduced_shifts)
        )
        phase += inverse_coefficient * sum(
            coefficient * pow((variable + shift) % q, -1, q)
            for coefficient, shift in zip(
                reciprocal_terms, reduced_shifts
            )
        )
        phases[variable] = phase % q

    root = cmath.exp(2j * cmath.pi / q)
    complete_sum = sum(root**phase for phase in phases.values())
    resonant_main = (
        len(phases) * root ** (direct_coefficient * constant_phase % q)
        if resonance_conditions_hold
        else 0j
    )
    centered_sum = complete_sum - resonant_main
    finite_values_are_constant = len(set(phases.values())) == 1
    tolerance = 1e-9
    return {
        "modulus": q,
        "moment_order": moment_order,
        "signs": signs,
        "pointwise_type_ii_exclusion_holds": all(
            a != b for a, b in zip(first, second)
        ),
        "distinct_shifts": distinct_shifts,
        "distinct_pole_count": len(poles),
        "linear_slope_mod_modulus": linear_slope,
        "reciprocal_residues_by_shift": residues_by_shift,
        "constant_phase_mod_modulus": (
            direct_coefficient * constant_phase % q
        ),
        "resonance_conditions_hold": resonance_conditions_hold,
        "rational_function_is_constant": resonance_conditions_hold,
        "rational_function_resonance_classification_exact": True,
        "finite_nonpole_values_are_constant": finite_values_are_constant,
        "finite_value_aliasing_detected": (
            finite_values_are_constant and not resonance_conditions_hold
        ),
        "nonpole_term_count": len(phases),
        "complete_sum": complete_sum,
        "resonant_main": resonant_main,
        "centered_sum": centered_sum,
        "resonant_main_exact": (
            abs(complete_sum - resonant_main) < tolerance
            if resonance_conditions_hold
            else True
        ),
        "centered_sum_vanishes_on_resonance": (
            abs(centered_sum) < tolerance
            if resonance_conditions_hold
            else False
        ),
        "square_root_bound_for_nonresonance_requires_weil": True,
    }


def rank_one_type_ii_resonance_partition_audit(
    *,
    moment_order: int,
    shift_block_sizes: tuple[int, ...],
) -> dict[str, object]:
    """Audit the dimension of every constant-phase shift partition.

    On a stratum with ``k`` distinct shifts, the resonance equations are
    one global linear-slope equation and one reciprocal-residue equation
    per shift block.  There are ``4m+k`` dilation/shift variables, hence
    every nonempty component has dimension at least ``4m-1``.  A
    singleton block is incompatible with the pointwise Type-II
    condition ``a_j != b_j``.
    """

    m = int(moment_order)
    blocks = tuple(int(size) for size in shift_block_sizes)
    if m < 1 or not blocks or any(size < 1 for size in blocks):
        raise ValueError("moment order and block sizes must be positive")
    if sum(blocks) != 2 * m:
        raise ValueError("shift block sizes must sum to 2*m")

    block_count = len(blocks)
    ambient_dimension = 4 * m + block_count
    resonance_equation_count = block_count + 1
    dimension_lower_bound = ambient_dimension - resonance_equation_count
    required_dimension = 3 * m
    compatible = all(size >= 2 for size in blocks)
    return {
        "moment_order": m,
        "shift_block_sizes": blocks,
        "shift_block_count": block_count,
        "has_singleton_block": any(size == 1 for size in blocks),
        "compatible_with_pointwise_type_ii": compatible,
        "active_admissible_resonant_stratum": compatible,
        "ambient_stratum_dimension": ambient_dimension,
        "resonance_equation_count": resonance_equation_count,
        "resonance_dimension_lower_bound": dimension_lower_bound,
        "gallant_required_exceptional_dimension": required_dimension,
        "dimension_excess": dimension_lower_bound - required_dimension,
        "standard_type_ii_exception_count_can_hold": (
            not compatible or dimension_lower_bound <= required_dimension
        ),
        "resonant_term_requires_separate_global_estimate": (
            compatible and dimension_lower_bound > required_dimension
        ),
    }


def rank_one_resonance_orthogonality_audit(
    *,
    modulus: int,
    shifts: tuple[int, ...],
    left_coefficient_families: tuple[dict[int, complex], ...],
    right_coefficient_families: tuple[dict[int, complex], ...],
) -> dict[str, object]:
    """Split the exact resonance projector into dual frequency modes.

    For every local Type-II pair ``a_j != b_j``, use the increment

    ``(eps_j*(a_j-b_j),``
    `` eps_j*(inverse(a_j)-inverse(b_j))*unit_shift_block_j)``.

    Additive orthogonality on the global linear coordinate and on every
    shift-block reciprocal coordinate reconstructs the direct resonant
    sum exactly.  The zero dual frequency is returned separately from
    all centered frequencies.  Both supplied coefficient families stay
    in every local factor; no absolute value is taken.
    """

    q = int(modulus)
    if q < 3 or any(q % p == 0 for p in range(2, isqrt(q) + 1)):
        raise ValueError("modulus must be an odd prime")
    entry_count = len(shifts)
    if entry_count == 0 or entry_count % 2:
        raise ValueError("the shift family must have positive even length")
    if not (
        len(left_coefficient_families)
        == len(right_coefficient_families)
        == entry_count
    ):
        raise ValueError("one left and right coefficient family is required per shift")

    def normalize(family: dict[int, complex]) -> dict[int, complex]:
        if not family:
            raise ValueError("coefficient families must be nonempty")
        normalized: dict[int, complex] = {}
        for residue, coefficient in family.items():
            reduced = int(residue) % q
            if reduced == 0:
                raise ValueError("coefficient support must consist of units")
            normalized[reduced] = normalized.get(reduced, 0j) + complex(
                coefficient
            )
        return normalized

    left = tuple(normalize(family) for family in left_coefficient_families)
    right = tuple(normalize(family) for family in right_coefficient_families)
    reduced_shifts = tuple(value % q for value in shifts)
    distinct_shifts = tuple(sorted(set(reduced_shifts)))
    block_index = {
        shift: index for index, shift in enumerate(distinct_shifts)
    }
    moment_order = entry_count // 2
    signs = (1,) * moment_order + (-1,) * moment_order
    coordinate_count = 1 + len(distinct_shifts)
    zero_state = (0,) * coordinate_count

    local_transitions: list[dict[tuple[int, ...], complex]] = []
    local_zero_frequency_factors: list[complex] = []
    local_zero_frequency_formula_factors: list[complex] = []
    for index, (sign, shift) in enumerate(zip(signs, reduced_shifts)):
        transitions: dict[tuple[int, ...], complex] = {}
        for a, alpha in left[index].items():
            for b, beta in right[index].items():
                if a == b:
                    continue
                delta = [0] * coordinate_count
                delta[0] = sign * (a - b) % q
                delta[1 + block_index[shift]] = sign * (
                    pow(a, -1, q) - pow(b, -1, q)
                ) % q
                key = tuple(delta)
                transitions[key] = transitions.get(key, 0j) + alpha * beta
        local_transitions.append(transitions)
        direct_local_total = sum(transitions.values(), 0j)
        local_zero_frequency_factors.append(direct_local_total)
        diagonal = sum(
            left[index].get(unit, 0j) * right[index].get(unit, 0j)
            for unit in range(1, q)
        )
        formula_total = (
            sum(left[index].values(), 0j)
            * sum(right[index].values(), 0j)
            - diagonal
        )
        local_zero_frequency_formula_factors.append(formula_total)

    state_weights: dict[tuple[int, ...], complex] = {zero_state: 1 + 0j}
    for transitions in local_transitions:
        updated: dict[tuple[int, ...], complex] = {}
        for state, state_weight in state_weights.items():
            for delta, local_weight in transitions.items():
                target = tuple(
                    (state[coordinate] + delta[coordinate]) % q
                    for coordinate in range(coordinate_count)
                )
                updated[target] = (
                    updated.get(target, 0j) + state_weight * local_weight
                )
        state_weights = updated
    direct_resonance_sum = state_weights.get(zero_state, 0j)

    root = cmath.exp(2j * cmath.pi / q)
    dual_total = 0j
    principal_numerator = 1 + 0j
    for factor in local_zero_frequency_factors:
        principal_numerator *= factor
    for frequency in product(range(q), repeat=coordinate_count):
        frequency_product = 1 + 0j
        for transitions in local_transitions:
            local_transform = sum(
                weight
                * root
                ** (
                    sum(
                        frequency[coordinate] * delta[coordinate]
                        for coordinate in range(coordinate_count)
                    )
                    % q
                )
                for delta, weight in transitions.items()
            )
            frequency_product *= local_transform
        dual_total += frequency_product
    normalization = q**coordinate_count
    reconstructed = dual_total / normalization
    principal_mode = principal_numerator / normalization
    centered_modes = reconstructed - principal_mode
    tolerance = 1e-8
    return {
        "modulus": q,
        "moment_order": moment_order,
        "signs": signs,
        "distinct_shifts": distinct_shifts,
        "dual_coordinate_count": coordinate_count,
        "dual_frequency_count": normalization,
        "direct_state_count": len(state_weights),
        "direct_resonance_sum": direct_resonance_sum,
        "dual_reconstructed_resonance_sum": reconstructed,
        "principal_dual_mode": principal_mode,
        "centered_dual_modes": centered_modes,
        "principal_plus_centered_exact": (
            abs(reconstructed - principal_mode - centered_modes) < tolerance
        ),
        "additive_orthogonality_reconstruction_exact": (
            abs(direct_resonance_sum - reconstructed) < tolerance
        ),
        "local_zero_frequency_factors": tuple(
            local_zero_frequency_factors
        ),
        "local_zero_frequency_formula_factors": tuple(
            local_zero_frequency_formula_factors
        ),
        "type_ii_diagonal_removal_formula_exact": all(
            abs(direct - formula) < tolerance
            for direct, formula in zip(
                local_zero_frequency_factors,
                local_zero_frequency_formula_factors,
            )
        ),
        "both_coefficient_families_retained": True,
        "absolute_values_taken_before_reconstruction": False,
        "principal_dual_mode_is_nonoscillatory": True,
        "principal_dual_mode_globally_evaluated": False,
        "centered_dual_operator_bound_proved": False,
    }


def squarefree_product_trace_crt_character_audit(
    *,
    prime_modulus: int,
    squarefree_cofactor: int,
    direct_coefficient: int,
    inverse_coefficient: int,
    residue: int,
    left_coefficients: dict[int, complex],
    right_coefficients: dict[int, complex],
) -> dict[str, object]:
    """Verify CRT and cofactor-character splitting for ``s=q*r``.

    For a prime ``q`` and a coprime squarefree ``r``, with
    ``K_s(x)=e_s(Bx+C/x)``, CRT gives

    ``K_s(x)=K_q^(r)(x) K_r^(q)(x)``.

    Multiplicative Fourier inversion on
    ``U(r) = product_(p|r) F_p^*`` then separates the cofactor trace in
    a bilinear product:

    ``B_s=phi(r)^(-1) sum_chi Khat_r(chi)``
    ``      * sum_(d,p) alpha_d chi(d) beta_p chi(p) K_q^(r)(dp)``.

    This keeps both coefficient families intact.  Parseval also records
    the unavoidable generic triangle/Cauchy cost
    ``phi(r)^(-1) sum |Khat_r| <= sqrt(phi(r))``.
    """

    q = int(prime_modulus)
    r = int(squarefree_cofactor)

    def is_prime(value: int) -> bool:
        return value >= 2 and not any(
            value % divisor == 0
            for divisor in range(2, isqrt(value) + 1)
        )

    r_factorization = _finite_prime_exponents(r) if r > 1 else {}
    if not is_prime(q):
        raise ValueError("q must be prime")
    if (
        r <= 1
        or any(exponent != 1 for exponent in r_factorization.values())
        or gcd(q, r) != 1
    ):
        raise ValueError("r must be a squarefree cofactor coprime to q")
    if not left_coefficients or not right_coefficients:
        raise ValueError("both coefficient families must be nonempty")

    s = q * r
    if gcd(residue, s) != 1:
        raise ValueError("residue must be a unit modulo q*r")
    b = direct_coefficient % s
    c = inverse_coefficient % s
    inv_r_q = pow(r, -1, q)
    inv_q_r = pow(q, -1, r)
    x_s = residue % s
    x_inverse_s = pow(x_s, -1, s)

    direct_q = inv_r_q * b * (x_s % q) % q
    direct_r = inv_q_r * b * (x_s % r) % r
    inverse_q = inv_r_q * c * pow(x_s % q, -1, q) % q
    inverse_r = inv_q_r * c * pow(x_s % r, -1, r) % r
    direct_recombined = (r * direct_q + q * direct_r) % s
    inverse_recombined = (r * inverse_q + q * inverse_r) % s

    root_s = cmath.exp(2j * cmath.pi / s)

    def product_trace(value: int, modulus: int, twist: int = 1) -> complex:
        reduced = value % modulus
        if gcd(reduced, modulus) != 1:
            return 0j
        phase = twist * (
            direct_coefficient * reduced
            + inverse_coefficient * pow(reduced, -1, modulus)
        ) % modulus
        root = cmath.exp(2j * cmath.pi / modulus)
        return root**phase

    full_value = root_s ** (
        (b * x_s + c * x_inverse_s) % s
    )
    q_value = product_trace(x_s, q, inv_r_q)
    r_value = product_trace(x_s, r, inv_q_r)

    cofactor_primes = tuple(sorted(r_factorization))
    primitive_roots: dict[int, int] = {}
    discrete_logs: dict[int, dict[int, int]] = {}
    character_roots: dict[int, complex] = {}
    for prime in cofactor_primes:
        order = prime - 1
        if prime == 2:
            generator = 1
        else:
            order_prime_factors = tuple(_finite_prime_exponents(order))
            generator = next(
                candidate
                for candidate in range(2, prime)
                if all(
                    pow(candidate, order // divisor, prime) != 1
                    for divisor in order_prime_factors
                )
            )
        primitive_roots[prime] = generator
        local_logs: dict[int, int] = {}
        current = 1
        for exponent in range(order):
            local_logs[current] = exponent
            current = current * generator % prime
        discrete_logs[prime] = local_logs
        character_roots[prime] = cmath.exp(2j * cmath.pi / order)

    character_indices = tuple(
        product(*(range(prime - 1) for prime in cofactor_primes))
    )
    unit_residues = tuple(
        value for value in range(1, r) if gcd(value, r) == 1
    )
    character_count = len(character_indices)

    def character(index: tuple[int, ...], value: int) -> complex:
        if gcd(value, r) != 1:
            return 0j
        result = 1 + 0j
        for component, prime in zip(index, cofactor_primes):
            exponent = discrete_logs[prime][value % prime]
            result *= character_roots[prime] ** (
                (component * exponent) % (prime - 1)
            )
        return result

    cofactor_kernel = {
        value: product_trace(value, r, inv_q_r)
        for value in unit_residues
    }
    fourier = [
        sum(
            cofactor_kernel[value] * character(index, value).conjugate()
            for value in unit_residues
        )
        for index in character_indices
    ]
    reconstructed = {
        value: sum(
            coefficient * character(index, value)
            for coefficient, index in zip(fourier, character_indices)
        )
        / character_count
        for value in unit_residues
    }

    atoms = [
        (d, p, complex(alpha) * complex(beta))
        for d, alpha in left_coefficients.items()
        for p, beta in right_coefficients.items()
    ]
    direct_bilinear = sum(
        weight * product_trace(d * p, s)
        for d, p, weight in atoms
    )
    character_twisted_forms = [
        sum(
            weight
            * character(index, d)
            * character(index, p)
            * product_trace(d * p, q, inv_r_q)
            for d, p, weight in atoms
        )
        for index in character_indices
    ]
    split_bilinear = sum(
        coefficient * twisted_form
        for coefficient, twisted_form in zip(
            fourier, character_twisted_forms
        )
    ) / character_count

    fourier_energy = sum(abs(value) ** 2 for value in fourier)
    kernel_energy = character_count * sum(
        abs(value) ** 2 for value in cofactor_kernel.values()
    )
    normalized_l1 = sum(abs(value) for value in fourier) / character_count
    normalized_multiplier_l2 = (
        fourier_energy / character_count**2
    )
    character_square_function_energy = sum(
        abs(value) ** 2 for value in character_twisted_forms
    )
    atom_trace_values = [
        (
            d * p % r,
            weight * product_trace(d * p, q, inv_r_q),
            gcd(d * p, r) == 1,
        )
        for d, p, weight in atoms
    ]
    product_residue_incidence_energy = character_count * sum(
        first_value * second_value.conjugate()
        for first_residue, first_value, first_unit in atom_trace_values
        for second_residue, second_value, second_unit in atom_trace_values
        if first_unit and second_unit and first_residue == second_residue
    )
    product_residue_clusters = {
        residue: sum(
            value
            for atom_residue, value, is_unit in atom_trace_values
            if is_unit and atom_residue == residue
        )
        for residue in unit_residues
    }
    total_unit_product_mass = sum(product_residue_clusters.values(), 0j)
    uniform_product_residue_mean = (
        total_unit_product_mass / character_count
    )
    uniform_product_residue_principal_energy = abs(
        total_unit_product_mass
    ) ** 2
    centered_product_residue_energy = character_count * sum(
        abs(value - uniform_product_residue_mean) ** 2
        for value in product_residue_clusters.values()
    )
    tolerance = 1e-9
    return {
        "squarefree_modulus": s,
        "squarefree_two_prime_modulus": s,
        "cofactor_prime_factors": cofactor_primes,
        "inverse_cofactor_mod_prime": inv_r_q,
        "inverse_prime_mod_cofactor": inv_q_r,
        "crt_direct_phase_exact": direct_recombined == b * x_s % s,
        "crt_inverse_phase_exact": (
            inverse_recombined == c * x_inverse_s % s
        ),
        "product_trace_factorization_exact": (
            abs(full_value - q_value * r_value) < tolerance
        ),
        "cofactor_primitive_roots": primitive_roots,
        "cofactor_primitive_root": (
            primitive_roots[cofactor_primes[0]]
            if len(cofactor_primes) == 1
            else None
        ),
        "cofactor_character_count": character_count,
        "cofactor_character_reconstruction_exact": max(
            abs(reconstructed[value] - cofactor_kernel[value])
            for value in unit_residues
        )
        < tolerance,
        "bilinear_character_split_exact": (
            abs(direct_bilinear - split_bilinear) < tolerance
        ),
        "cofactor_character_parseval_exact": (
            abs(fourier_energy - kernel_energy) < tolerance
        ),
        "normalized_character_multiplier_l2": normalized_multiplier_l2,
        "normalized_character_multiplier_l2_is_one": (
            abs(normalized_multiplier_l2 - 1) < tolerance
        ),
        "character_square_function_energy": (
            character_square_function_energy
        ),
        "product_residue_incidence_energy": (
            product_residue_incidence_energy
        ),
        "product_residue_clusters": product_residue_clusters,
        "uniform_product_residue_mean": uniform_product_residue_mean,
        "uniform_product_residue_principal_energy": (
            uniform_product_residue_principal_energy
        ),
        "centered_product_residue_energy": centered_product_residue_energy,
        "product_incidence_principal_centered_split_exact": (
            abs(
                character_square_function_energy
                - uniform_product_residue_principal_energy
                - centered_product_residue_energy
            )
            < tolerance
        ),
        "character_square_function_incidence_exact": (
            abs(
                character_square_function_energy
                - product_residue_incidence_energy
            )
            < tolerance
        ),
        "crt_bilinear_energy_le_character_square_function": (
            abs(split_bilinear) ** 2
            <= character_square_function_energy + tolerance
        ),
        "normalized_character_l1": normalized_l1,
        "normalized_character_l1_bound": character_count**0.5,
        "normalized_character_l1_bound_holds": (
            normalized_l1 <= character_count**0.5 + tolerance
        ),
        "both_mobius_weights_retained": True,
        "retained_mobius_factors": ("mu(q*r)", "mu(d)"),
        "h_delta_factor_retained": True,
        "crt_iteration_covers_squarefree_cofactor": True,
        "global_product_incidence_bound_proved": False,
    }


def hdelta_product_incidence_fourier_audit(
    *,
    squarefree_modulus: int,
    selected_divisor: int,
    first_product_residue: int,
    second_product_residue: int,
    h_coefficients: dict[int, complex],
    delta_coefficients: dict[int, complex],
) -> dict[str, object]:
    """Audit the pre-h-Poisson Fourier gain on one CRT square term.

    Write ``s=q*r`` with ``s`` squarefree and ``(q,r)=1``.  On the
    equal-outer-label slice, a cofactor character square forces
    ``x1 == x2 (mod r)``.  The inverse part of the two product traces
    then leaves

    ``e_q(-inverse(r)*h*delta*(inverse(x1)-inverse(x2)))``.

    If ``g=gcd(x1-x2,q)`` and ``Q=q/g``, this is a primitive product
    phase modulo ``Q``.  Grouping ``h`` and ``delta`` by residues modulo
    ``Q`` and applying Parseval gives the exact finite operator bound

    ``|sum f_h g_delta e_Q(c*h*delta)|``
    ``    <= sqrt(Q * sum_a |F_a|^2 * sum_b |G_b|^2)``.

    This is an alternative use of the h-orthogonality underlying the
    determinant-line identity: it is valid before completing h, not an
    additional oscillator after h-Poisson.
    """

    s = int(squarefree_modulus)
    q = int(selected_divisor)
    if s <= 1 or q <= 1 or s % q:
        raise ValueError("q must be a nontrivial divisor of s")
    factorization = _finite_prime_exponents(s)
    if any(exponent != 1 for exponent in factorization.values()):
        raise ValueError("s must be squarefree")
    r = s // q
    if gcd(q, r) != 1:
        raise ValueError("q and its complementary divisor must be coprime")
    x1 = int(first_product_residue) % s
    x2 = int(second_product_residue) % s
    if gcd(x1 * x2, s) != 1:
        raise ValueError("both product residues must be units modulo s")
    if (x1 - x2) % r:
        raise ValueError("the cofactor product-incidence condition is required")
    if not h_coefficients or not delta_coefficients:
        raise ValueError("both finite coefficient families must be nonempty")

    inverse_r_mod_q = pow(r, -1, q) if r > 1 else 1
    inverse_difference = (pow(x1, -1, q) - pow(x2, -1, q)) % q
    phase_coefficient_mod_q = (-inverse_r_mod_q * inverse_difference) % q
    coefficient_gcd = gcd(phase_coefficient_mod_q, q)
    conductor = q // coefficient_gcd
    reduced_phase_coefficient = (
        phase_coefficient_mod_q // coefficient_gcd % conductor
        if conductor > 1
        else 0
    )
    collision_modulus = r * coefficient_gcd

    h_data = {int(index): complex(value) for index, value in h_coefficients.items()}
    delta_data = {
        int(index): complex(value) for index, value in delta_coefficients.items()
    }

    def phase(modulus: int, coefficient: int, h: int, delta: int) -> complex:
        if modulus == 1:
            return 1 + 0j
        root = cmath.exp(2j * cmath.pi / modulus)
        return root ** (coefficient * h * delta % modulus)

    direct_mod_q_sum = sum(
        f_h
        * g_delta
        * phase(q, phase_coefficient_mod_q, h, delta)
        for h, f_h in h_data.items()
        for delta, g_delta in delta_data.items()
    )
    reduced_conductor_sum = sum(
        f_h
        * g_delta
        * phase(conductor, reduced_phase_coefficient, h, delta)
        for h, f_h in h_data.items()
        for delta, g_delta in delta_data.items()
    )

    grouped_h = {
        residue: sum(
            value for index, value in h_data.items() if index % conductor == residue
        )
        for residue in range(conductor)
    }
    grouped_delta = {
        residue: sum(
            value
            for index, value in delta_data.items()
            if index % conductor == residue
        )
        for residue in range(conductor)
    }
    grouped_sum = sum(
        grouped_h[a]
        * grouped_delta[b]
        * phase(conductor, reduced_phase_coefficient, a, b)
        for a in range(conductor)
        for b in range(conductor)
    )
    h_residue_energy = sum(abs(value) ** 2 for value in grouped_h.values())
    delta_residue_energy = sum(
        abs(value) ** 2 for value in grouped_delta.values()
    )
    fourier_operator_bound = (
        conductor * h_residue_energy * delta_residue_energy
    ) ** 0.5

    h_multiplicities = tuple(
        sum(1 for index in h_data if index % conductor == residue)
        for residue in range(conductor)
    )
    delta_multiplicities = tuple(
        sum(1 for index in delta_data if index % conductor == residue)
        for residue in range(conductor)
    )
    h_l2 = sum(abs(value) ** 2 for value in h_data.values())
    delta_l2 = sum(abs(value) ** 2 for value in delta_data.values())
    multiplicity_bound = (
        conductor
        * max(h_multiplicities, default=0)
        * h_l2
        * max(delta_multiplicities, default=0)
        * delta_l2
    ) ** 0.5

    def consecutive(indices: tuple[int, ...]) -> bool:
        ordered = sorted(indices)
        return ordered == list(range(ordered[0], ordered[0] + len(ordered)))

    h_is_interval = consecutive(tuple(h_data))
    delta_is_interval = consecutive(tuple(delta_data))
    one_bounded = all(abs(value) <= 1 + 1e-12 for value in h_data.values()) and all(
        abs(value) <= 1 + 1e-12 for value in delta_data.values()
    )
    interval_one_bounded_ceiling = (
        (
            conductor
            * len(h_data)
            * len(delta_data)
            * ((len(h_data) + conductor - 1) // conductor)
            * ((len(delta_data) + conductor - 1) // conductor)
        )
        ** 0.5
        if h_is_interval and delta_is_interval and one_bounded
        else None
    )
    tolerance = 1e-8
    return {
        "squarefree_modulus": s,
        "selected_divisor": q,
        "cofactor": r,
        "cofactor_product_incidence_holds": True,
        "inverse_cofactor_mod_selected_divisor": inverse_r_mod_q,
        "inverse_difference_mod_selected_divisor": inverse_difference,
        "phase_coefficient_mod_selected_divisor": phase_coefficient_mod_q,
        "phase_coefficient_gcd": coefficient_gcd,
        "reduced_conductor": conductor,
        "reduced_phase_coefficient": reduced_phase_coefficient,
        "reduced_phase_is_primitive": (
            conductor == 1 or gcd(reduced_phase_coefficient, conductor) == 1
        ),
        "collision_modulus": collision_modulus,
        "collision_modulus_equals_s_over_conductor": (
            collision_modulus == s // conductor
        ),
        "stronger_product_collision_holds": (
            (x1 - x2) % collision_modulus == 0
        ),
        "full_product_diagonal": (x1 - x2) % s == 0,
        "conductor_one_iff_full_product_diagonal": (
            (conductor == 1) == ((x1 - x2) % s == 0)
        ),
        "direct_mod_selected_divisor_sum": direct_mod_q_sum,
        "reduced_conductor_sum": reduced_conductor_sum,
        "grouped_residue_sum": grouped_sum,
        "conductor_reduction_exact": (
            abs(direct_mod_q_sum - reduced_conductor_sum) < tolerance
        ),
        "residue_grouping_exact": (
            abs(reduced_conductor_sum - grouped_sum) < tolerance
        ),
        "h_residue_energy": h_residue_energy,
        "delta_residue_energy": delta_residue_energy,
        "fourier_operator_bound": fourier_operator_bound,
        "fourier_operator_bound_holds": (
            abs(grouped_sum) <= fourier_operator_bound + tolerance
        ),
        "h_max_residue_multiplicity": max(h_multiplicities, default=0),
        "delta_max_residue_multiplicity": max(
            delta_multiplicities, default=0
        ),
        "multiplicity_l2_bound": multiplicity_bound,
        "multiplicity_l2_bound_holds": (
            fourier_operator_bound <= multiplicity_bound + tolerance
        ),
        "h_support_is_integer_interval": h_is_interval,
        "delta_support_is_integer_interval": delta_is_interval,
        "coefficients_are_one_bounded": one_bounded,
        "interval_one_bounded_ceiling": interval_one_bounded_ceiling,
        "interval_one_bounded_ceiling_holds": (
            interval_one_bounded_ceiling is not None
            and fourier_operator_bound <= interval_one_bounded_ceiling + tolerance
        ),
        "equal_outer_label_slice_only": True,
        "unequal_outer_label_gram_proved": False,
        "uses_h_orthogonality_before_h_poisson": True,
        "additional_post_h_poisson_saving_claimed": False,
        "low_conductor_collision_strata_globally_bounded": False,
        "afe_smooth_packet_adapter_proved": False,
        "coupled_kernel_gate_closed": False,
    }


def hdelta_fourier_exponent_audit(
    *,
    conductor_exponent: Fraction,
    h_length_exponent: Fraction,
    delta_length_exponent: Fraction,
    required_saving_exponent: Fraction = F(1, 2),
) -> dict[str, Fraction | bool]:
    """Record the exponent saving of the finite product-phase operator."""

    lam = F(conductor_exponent)
    h = F(h_length_exponent)
    ell = F(delta_length_exponent)
    required = F(required_saving_exponent)
    if min(lam, h, ell, required) < 0:
        raise ValueError("all exponents must be nonnegative")
    h_multiplicity = max(F(0), h - lam)
    delta_multiplicity = max(F(0), ell - lam)
    bound = (lam + h + ell + h_multiplicity + delta_multiplicity) / 2
    trivial = h + ell
    saving = trivial - bound
    return {
        "conductor_exponent": lam,
        "h_length_exponent": h,
        "delta_length_exponent": ell,
        "h_residue_multiplicity_exponent": h_multiplicity,
        "delta_residue_multiplicity_exponent": delta_multiplicity,
        "trivial_bilinear_exponent": trivial,
        "fourier_operator_bound_exponent": bound,
        "relative_saving_exponent": saving,
        "required_saving_exponent": required,
        "reaches_required_saving_on_this_conductor": saving >= required,
        "compatibility_with_preceding_reductions_proved": False,
        "unequal_outer_label_gram_proved": False,
        "low_conductor_strata_covered": False,
        "analytic_packet_adapter_proved": False,
        "coupled_kernel_gate_closed": False,
    }


def squarefree_crt_unequal_outer_character_gram_audit(
    *,
    prime_modulus: int,
    squarefree_cofactor: int,
    direct_coefficient: int,
    outer_product_coefficients: dict[int, dict[int, complex]],
) -> dict[str, object]:
    """Collapse the full unequal-outer-label CRT character square.

    The outer key is the retained product label ``a=h*delta``.  For
    ``s=q*r``, expand the cofactor kernel for every ``a`` in multiplicative
    characters modulo ``r`` and make one Cauchy step only after summing all
    outer labels inside each character.

    Character orthogonality then converts the full square exactly into the
    cross kernel

    ``C_r(a1,a2;y) = sum_v K_(r,a1)(v*y) conjugate(K_(r,a2)(v))``

    with ``y=x1/inverse(x2)``.  This is the Kloosterman-type trace with
    direct coefficient ``B*(y-1)`` and inverse coefficient
    ``a2-a1*inverse(y)``.  Its principal mode is therefore
    ``y=1`` and ``a1=a2 (mod r)`` when ``B`` is a unit.
    """

    q = int(prime_modulus)
    r = int(squarefree_cofactor)

    def is_prime(value: int) -> bool:
        return value >= 2 and not any(
            value % divisor == 0
            for divisor in range(2, isqrt(value) + 1)
        )

    r_factorization = _finite_prime_exponents(r) if r > 1 else {}
    if not is_prime(q):
        raise ValueError("q must be prime")
    if (
        r <= 1
        or any(exponent != 1 for exponent in r_factorization.values())
        or gcd(q, r) != 1
    ):
        raise ValueError("r must be a squarefree cofactor coprime to q")
    s = q * r
    b = int(direct_coefficient) % s
    if gcd(b, s) != 1:
        raise ValueError("the direct coefficient must be a unit modulo q*r")
    if not outer_product_coefficients or any(
        not family for family in outer_product_coefficients.values()
    ):
        raise ValueError("every outer product label needs a coefficient family")

    normalized_coefficients: dict[int, dict[int, complex]] = {}
    for outer_label, family in outer_product_coefficients.items():
        normalized_family: dict[int, complex] = {}
        for residue, coefficient in family.items():
            reduced = int(residue) % s
            if gcd(reduced, s) != 1:
                raise ValueError("all product residues must be units modulo q*r")
            normalized_family[reduced] = normalized_family.get(
                reduced, 0j
            ) + complex(coefficient)
        normalized_coefficients[int(outer_label)] = normalized_family

    inv_r_q = pow(r, -1, q)
    inv_q_r = pow(q, -1, r)
    cofactor_primes = tuple(sorted(r_factorization))
    discrete_logs: dict[int, dict[int, int]] = {}
    character_roots: dict[int, complex] = {}
    for prime in cofactor_primes:
        order = prime - 1
        if prime == 2:
            generator = 1
        else:
            order_prime_factors = tuple(_finite_prime_exponents(order))
            generator = next(
                candidate
                for candidate in range(2, prime)
                if all(
                    pow(candidate, order // divisor, prime) != 1
                    for divisor in order_prime_factors
                )
            )
        local_logs: dict[int, int] = {}
        current = 1
        for exponent in range(order):
            local_logs[current] = exponent
            current = current * generator % prime
        discrete_logs[prime] = local_logs
        character_roots[prime] = cmath.exp(2j * cmath.pi / order)

    character_indices = tuple(
        product(*(range(prime - 1) for prime in cofactor_primes))
    )
    unit_residues = tuple(
        value for value in range(1, r) if gcd(value, r) == 1
    )
    phi_r = len(unit_residues)

    def character(index: tuple[int, ...], value: int) -> complex:
        if gcd(value, r) != 1:
            return 0j
        result = 1 + 0j
        for component, prime in zip(index, cofactor_primes):
            exponent = discrete_logs[prime][value % prime]
            result *= character_roots[prime] ** (
                component * exponent % (prime - 1)
            )
        return result

    def kernel(modulus: int, twist: int, outer_label: int, value: int) -> complex:
        reduced = value % modulus
        if gcd(reduced, modulus) != 1:
            return 0j
        phase = twist * (
            direct_coefficient * reduced
            - outer_label * pow(reduced, -1, modulus)
        ) % modulus
        root = cmath.exp(2j * cmath.pi / modulus)
        return root**phase

    def squarefree_phi(value: int) -> int:
        return_value = 1
        for prime in cofactor_primes:
            if value % prime == 0:
                return_value *= prime - 1
        return return_value

    cofactor_fourier: dict[int, list[complex]] = {}
    prime_character_forms: dict[int, list[complex]] = {}
    for outer_label, family in normalized_coefficients.items():
        cofactor_values = {
            value: kernel(r, inv_q_r, outer_label, value)
            for value in unit_residues
        }
        cofactor_fourier[outer_label] = [
            sum(
                cofactor_values[value]
                * character(index, value).conjugate()
                for value in unit_residues
            )
            for index in character_indices
        ]
        prime_character_forms[outer_label] = [
            sum(
                coefficient
                * character(index, value)
                * kernel(q, inv_r_q, outer_label, value)
                for value, coefficient in family.items()
            )
            for index in character_indices
        ]

    direct_full_sum = sum(
        coefficient * kernel(s, 1, outer_label, value)
        for outer_label, family in normalized_coefficients.items()
        for value, coefficient in family.items()
    )
    character_totals = [
        sum(
            cofactor_fourier[outer_label][character_position]
            * prime_character_forms[outer_label][character_position]
            for outer_label in normalized_coefficients
        )
        for character_position in range(phi_r)
    ]
    character_reconstruction = sum(character_totals, 0j) / phi_r
    global_character_square = sum(
        abs(value) ** 2 for value in character_totals
    ) / phi_r

    correlation_rows: list[dict[str, object]] = []
    collapsed_character_square = 0j
    for outer_label_1, family_1 in normalized_coefficients.items():
        for outer_label_2, family_2 in normalized_coefficients.items():
            for x1, coefficient_1 in family_1.items():
                for x2, coefficient_2 in family_2.items():
                    y = x1 * pow(x2, -1, r) % r
                    cofactor_correlation = sum(
                        kernel(r, inv_q_r, outer_label_1, v * y)
                        * kernel(r, inv_q_r, outer_label_2, v).conjugate()
                        for v in unit_residues
                    )
                    direct_phase_coefficient = (
                        inv_q_r * direct_coefficient * (y - 1)
                    ) % r
                    inverse_phase_coefficient = (
                        inv_q_r
                        * (outer_label_2 - outer_label_1 * pow(y, -1, r))
                    ) % r
                    root_r = cmath.exp(2j * cmath.pi / r)
                    kloosterman_formula = sum(
                        root_r
                        ** (
                            direct_phase_coefficient * v
                            + inverse_phase_coefficient * pow(v, -1, r)
                        )
                        for v in unit_residues
                    )
                    local_factor_rows: list[dict[str, object]] = []
                    local_factor_product = 1 + 0j
                    principal_divisor = 1
                    for prime in cofactor_primes:
                        local_twist = pow(r // prime, -1, prime)
                        local_direct = (
                            local_twist * direct_phase_coefficient
                        ) % prime
                        local_inverse = (
                            local_twist * inverse_phase_coefficient
                        ) % prime
                        root_prime = cmath.exp(2j * cmath.pi / prime)
                        local_factor = sum(
                            root_prime
                            ** (
                                local_direct * unit
                                + local_inverse * pow(unit, -1, prime)
                            )
                            for unit in range(1, prime)
                        )
                        local_principal = (
                            local_direct == 0 and local_inverse == 0
                        )
                        exactly_one_zero = (
                            (local_direct == 0) != (local_inverse == 0)
                        )
                        if local_principal:
                            principal_divisor *= prime
                            local_ceiling = float(prime - 1)
                        elif exactly_one_zero:
                            local_ceiling = 1.0
                        else:
                            local_ceiling = min(
                                float(prime - 1), 2 * prime**0.5
                            )
                        local_factor_product *= local_factor
                        local_factor_rows.append(
                            {
                                "prime": prime,
                                "crt_twist": local_twist,
                                "local_direct_coefficient": local_direct,
                                "local_inverse_coefficient": local_inverse,
                                "local_factor": local_factor,
                                "local_principal": local_principal,
                                "exactly_one_local_coefficient_zero": (
                                    exactly_one_zero
                                ),
                                "one_zero_ramanujan_value_exact": (
                                    not exactly_one_zero
                                    or abs(local_factor + 1) < 1e-8
                                ),
                                "local_weil_or_trivial_ceiling": local_ceiling,
                                "local_weil_or_trivial_bound_holds": (
                                    abs(local_factor) <= local_ceiling + 1e-8
                                ),
                            }
                        )
                    nonprincipal_conductor = r // principal_divisor
                    small_alias_part = gcd(nonprincipal_conductor, 6)
                    large_nonprincipal_part = (
                        nonprincipal_conductor // small_alias_part
                    )
                    large_prime_count = sum(
                        1
                        for prime in cofactor_primes
                        if large_nonprincipal_part % prime == 0
                    )
                    conductor_ceiling = (
                        squarefree_phi(principal_divisor)
                        * squarefree_phi(small_alias_part)
                        * 2**large_prime_count
                        * large_nonprincipal_part**0.5
                    )
                    principal = (
                        direct_phase_coefficient == 0
                        and inverse_phase_coefficient == 0
                    )
                    expected_principal = (
                        y == 1 and (outer_label_1 - outer_label_2) % r == 0
                    )
                    q_cross = (
                        coefficient_1
                        * coefficient_2.conjugate()
                        * kernel(q, inv_r_q, outer_label_1, x1)
                        * kernel(q, inv_r_q, outer_label_2, x2).conjugate()
                    )
                    collapsed_character_square += q_cross * cofactor_correlation
                    correlation_rows.append(
                        {
                            "outer_label_1": outer_label_1,
                            "outer_label_2": outer_label_2,
                            "first_product_residue": x1,
                            "second_product_residue": x2,
                            "product_ratio_mod_cofactor": y,
                            "direct_phase_coefficient_mod_cofactor": (
                                direct_phase_coefficient
                            ),
                            "inverse_phase_coefficient_mod_cofactor": (
                                inverse_phase_coefficient
                            ),
                            "cofactor_correlation": cofactor_correlation,
                            "kloosterman_formula": kloosterman_formula,
                            "kloosterman_formula_exact": (
                                abs(cofactor_correlation - kloosterman_formula)
                                < 1e-8
                            ),
                            "local_factor_rows": tuple(local_factor_rows),
                            "local_crt_factorization": local_factor_product,
                            "local_crt_factorization_exact": (
                                abs(cofactor_correlation - local_factor_product)
                                < 1e-8
                            ),
                            "principal_divisor": principal_divisor,
                            "nonprincipal_conductor": nonprincipal_conductor,
                            "small_alias_part": small_alias_part,
                            "large_nonprincipal_part": (
                                large_nonprincipal_part
                            ),
                            "large_nonprincipal_prime_count": (
                                large_prime_count
                            ),
                            "cofactor_conductor_ceiling": conductor_ceiling,
                            "cofactor_conductor_bound_holds": (
                                abs(cofactor_correlation)
                                <= conductor_ceiling + 1e-8
                            ),
                            "low_conductor_forces_principal_congruences": (
                                (y - 1) % principal_divisor == 0
                                and (outer_label_1 - outer_label_2)
                                % principal_divisor
                                == 0
                            ),
                            "principal_cofactor_mode": principal,
                            "expected_principal_condition": expected_principal,
                            "principal_condition_exact": (
                                principal == expected_principal
                            ),
                            "principal_kernel_equals_phi": (
                                not principal
                                or abs(cofactor_correlation - phi_r) < 1e-8
                            ),
                        }
                    )

    tolerance = 1e-8
    nonprincipal_full_amplitude_alias_rows = tuple(
        row
        for row in correlation_rows
        if not bool(row["principal_cofactor_mode"])
        and abs(abs(complex(row["cofactor_correlation"])) - phi_r) < tolerance
    )
    return {
        "squarefree_modulus": s,
        "prime_modulus": q,
        "squarefree_cofactor": r,
        "outer_product_labels": tuple(normalized_coefficients),
        "cofactor_character_count": phi_r,
        "direct_full_sum": direct_full_sum,
        "character_reconstruction": character_reconstruction,
        "crt_character_reconstruction_exact": (
            abs(direct_full_sum - character_reconstruction) < tolerance
        ),
        "direct_full_energy": abs(direct_full_sum) ** 2,
        "global_character_square": global_character_square,
        "global_character_cauchy_bound_holds": (
            abs(direct_full_sum) ** 2
            <= global_character_square + tolerance
        ),
        "collapsed_character_square": collapsed_character_square,
        "character_square_collapse_exact": (
            abs(global_character_square - collapsed_character_square)
            < tolerance
        ),
        "correlation_rows": tuple(correlation_rows),
        "all_kloosterman_formulas_exact": all(
            bool(row["kloosterman_formula_exact"])
            for row in correlation_rows
        ),
        "all_local_crt_factorizations_exact": all(
            bool(row["local_crt_factorization_exact"])
            for row in correlation_rows
        ),
        "all_local_weil_or_trivial_bounds_hold": all(
            bool(local_row["local_weil_or_trivial_bound_holds"])
            for row in correlation_rows
            for local_row in row["local_factor_rows"]
        ),
        "all_one_zero_ramanujan_values_exact": all(
            bool(local_row["one_zero_ramanujan_value_exact"])
            for row in correlation_rows
            for local_row in row["local_factor_rows"]
        ),
        "all_cofactor_conductor_bounds_hold": all(
            bool(row["cofactor_conductor_bound_holds"])
            for row in correlation_rows
        ),
        "all_low_conductor_principal_congruences_hold": all(
            bool(row["low_conductor_forces_principal_congruences"])
            for row in correlation_rows
        ),
        "all_principal_conditions_exact": all(
            bool(row["principal_condition_exact"])
            for row in correlation_rows
        ),
        "all_principal_kernels_equal_phi": all(
            bool(row["principal_kernel_equals_phi"])
            for row in correlation_rows
        ),
        "nonprincipal_full_amplitude_alias_rows": (
            nonprincipal_full_amplitude_alias_rows
        ),
        "nonprincipal_finite_aliases_may_exist_for_composite_cofactor": True,
        "unequal_outer_product_labels_retained_inside_character_square": True,
        "pointwise_cofactor_l1_cost_paid": False,
        "principal_cofactor_mode_globally_reassembled": False,
        "centered_cofactor_kloosterman_operator_bound_proved": False,
        "coupled_kernel_gate_closed": False,
    }


def cofactor_outer_product_fourier_operator_audit(
    *,
    prime_modulus: int,
    squarefree_cofactor: int,
    direct_coefficient: int,
    product_ratio: int,
    left_outer_coefficients: dict[int, complex],
    right_outer_coefficients: dict[int, complex],
) -> dict[str, object]:
    """Diagonalize the full outer-product-label cofactor matrix.

    For fixed product ratio ``y``, the matrix is

    ``C_y(a,b)=sum_v e_r(qbar*(B*(y-1)*v``
    ``                         +(b-a/y)/v))``.

    Its additive Fourier basis is mapped by a signed permutation on unit
    frequencies, with multiplier of modulus ``r``; nonunit frequencies
    vanish.  Thus every nonzero singular value is exactly ``r``.  In
    particular the complete matrix has zero row and column sums even when
    individual composite-modulus entries are full-amplitude aliases.
    """

    q = int(prime_modulus)
    r = int(squarefree_cofactor)
    if q < 2 or any(q % divisor == 0 for divisor in range(2, isqrt(q) + 1)):
        raise ValueError("q must be prime")
    factorization = _finite_prime_exponents(r) if r > 1 else {}
    if (
        r <= 1
        or any(exponent != 1 for exponent in factorization.values())
        or gcd(q, r) != 1
    ):
        raise ValueError("r must be squarefree and coprime to q")
    if gcd(direct_coefficient, r) != 1:
        raise ValueError("the direct coefficient must be a unit modulo r")
    y = int(product_ratio) % r
    if gcd(y, r) != 1:
        raise ValueError("the product ratio must be a unit modulo r")
    if not left_outer_coefficients or not right_outer_coefficients:
        raise ValueError("both outer coefficient families must be nonempty")

    inv_q_r = pow(q, -1, r)
    inv_y_r = pow(y, -1, r)
    root = cmath.exp(2j * cmath.pi / r)
    units = tuple(value for value in range(1, r) if gcd(value, r) == 1)
    matrix = tuple(
        tuple(
            sum(
                root
                ** (
                    inv_q_r
                    * (
                        direct_coefficient * (y - 1) * v
                        + (b - a * inv_y_r) * pow(v, -1, r)
                    )
                    % r
                )
                for v in units
            )
            for b in range(r)
        )
        for a in range(r)
    )
    row_sums = tuple(sum(row, 0j) for row in matrix)
    column_sums = tuple(
        sum(matrix[a][b] for a in range(r)) for b in range(r)
    )

    fourier_action_rows: list[dict[str, object]] = []
    for frequency in range(r):
        action = tuple(
            sum(
                matrix[a][b] * root ** (frequency * b % r)
                for b in range(r)
            )
            for a in range(r)
        )
        if gcd(frequency, r) == 1:
            constant_phase = (
                -direct_coefficient
                * (y - 1)
                * pow(frequency, -1, r)
                * pow(inv_q_r, 2, r)
            ) % r
            output_frequency = inv_y_r * frequency % r
            expected = tuple(
                r * root ** ((constant_phase + output_frequency * a) % r)
                for a in range(r)
            )
        else:
            constant_phase = None
            output_frequency = None
            expected = (0j,) * r
        fourier_action_rows.append(
            {
                "input_frequency": frequency,
                "input_frequency_is_unit": gcd(frequency, r) == 1,
                "constant_phase": constant_phase,
                "output_frequency": output_frequency,
                "action": action,
                "expected_action": expected,
                "fourier_action_exact": all(
                    abs(actual - target) < 1e-8
                    for actual, target in zip(action, expected)
                ),
            }
        )

    def aggregate(family: dict[int, complex]) -> tuple[complex, ...]:
        return tuple(
            sum(
                complex(coefficient)
                for label, coefficient in family.items()
                if int(label) % r == residue
            )
            for residue in range(r)
        )

    left = aggregate(left_outer_coefficients)
    right = aggregate(right_outer_coefficients)
    bilinear_form = sum(
        left[a] * right[b].conjugate() * matrix[a][b]
        for a in range(r)
        for b in range(r)
    )
    left_energy = sum(abs(value) ** 2 for value in left)
    right_energy = sum(abs(value) ** 2 for value in right)
    left_primitive_fourier_energy = sum(
        abs(sum(left[a] * root ** (frequency * a % r) for a in range(r)))
        ** 2
        for frequency in units
    ) / r
    right_primitive_fourier_energy = sum(
        abs(sum(right[b] * root ** (frequency * b % r) for b in range(r)))
        ** 2
        for frequency in units
    ) / r
    operator_bound = r * (
        left_primitive_fourier_energy * right_primitive_fourier_energy
    ) ** 0.5
    tolerance = 1e-8
    return {
        "prime_modulus": q,
        "squarefree_cofactor": r,
        "product_ratio": y,
        "matrix": matrix,
        "row_sums": row_sums,
        "column_sums": column_sums,
        "all_row_sums_zero": all(abs(value) < tolerance for value in row_sums),
        "all_column_sums_zero": all(
            abs(value) < tolerance for value in column_sums
        ),
        "fourier_action_rows": tuple(fourier_action_rows),
        "all_fourier_actions_exact": all(
            bool(row["fourier_action_exact"])
            for row in fourier_action_rows
        ),
        "nonzero_singular_value": r,
        "nonzero_singular_value_multiplicity": len(units),
        "zero_singular_value_multiplicity": r - len(units),
        "exact_operator_norm": r,
        "left_residue_energy": left_energy,
        "right_residue_energy": right_energy,
        "left_primitive_fourier_energy": left_primitive_fourier_energy,
        "right_primitive_fourier_energy": right_primitive_fourier_energy,
        "bilinear_form": bilinear_form,
        "operator_bound": operator_bound,
        "operator_bound_holds": abs(bilinear_form) <= operator_bound + tolerance,
        "principal_and_alias_entries_cancel_in_complete_rows": (
            all(abs(value) < tolerance for value in row_sums)
            and all(abs(value) < tolerance for value in column_sums)
        ),
        "outer_product_residue_operator_bound_proved": True,
        "analytic_packet_residue_energy_bound_proved": False,
        "coupled_kernel_gate_closed": False,
    }


def primitive_product_residue_energy_audit(
    *,
    squarefree_modulus: int,
    h_coefficients: dict[int, complex],
    delta_coefficients: dict[int, complex],
) -> dict[str, object]:
    """Isolate the primitive additive spectrum of ``a=h*delta``.

    The cofactor matrix in
    :func:`cofactor_outer_product_fourier_operator_audit` annihilates every
    nonunit additive frequency.  This helper computes the surviving
    projection exactly and records the elementary Cauchy--Parseval ceiling.
    The latter deliberately uses no Möbius cancellation.
    """

    r = int(squarefree_modulus)
    factorization = _finite_prime_exponents(r) if r > 1 else {}
    if r <= 1 or any(exponent != 1 for exponent in factorization.values()):
        raise ValueError("the modulus must be squarefree and greater than one")
    if not h_coefficients or not delta_coefficients:
        raise ValueError("both coefficient families must be nonempty")

    h_family = {
        int(label): complex(coefficient)
        for label, coefficient in h_coefficients.items()
        if complex(coefficient) != 0
    }
    delta_family = {
        int(label): complex(coefficient)
        for label, coefficient in delta_coefficients.items()
        if complex(coefficient) != 0
    }
    if not h_family or not delta_family:
        raise ValueError("both coefficient families must have nonzero support")

    root = cmath.exp(2j * cmath.pi / r)
    units = tuple(value for value in range(1, r) if gcd(value, r) == 1)
    product_residue_coefficients = tuple(
        sum(
            h_coefficient * delta_coefficient
            for h, h_coefficient in h_family.items()
            for delta, delta_coefficient in delta_family.items()
            if h * delta % r == residue
        )
        for residue in range(r)
    )
    product_fourier_coefficients = tuple(
        sum(
            product_residue_coefficients[residue]
            * root ** (frequency * residue % r)
            for residue in range(r)
        )
        for frequency in range(r)
    )
    primitive_projection = tuple(
        sum(
            product_fourier_coefficients[frequency]
            * root ** (-frequency * residue % r)
            for frequency in units
        )
        / r
        for residue in range(r)
    )
    direct_primitive_energy = sum(
        abs(value) ** 2 for value in primitive_projection
    )
    parseval_primitive_energy = sum(
        abs(product_fourier_coefficients[frequency]) ** 2
        for frequency in units
    ) / r

    h_energy = sum(abs(value) ** 2 for value in h_family.values())
    delta_energy = sum(abs(value) ** 2 for value in delta_family.values())

    def maximum_residue_multiplicity(
        labels: tuple[int, ...], modulus: int
    ) -> int:
        return max(
            sum(1 for label in labels if label % modulus == residue)
            for residue in range(modulus)
        )

    h_labels = tuple(h_family)
    delta_labels = tuple(delta_family)
    left_alias_multiplicity = sum(
        maximum_residue_multiplicity(delta_labels, r // gcd(h, r))
        for h in h_labels
    )
    right_alias_multiplicity = sum(
        maximum_residue_multiplicity(h_labels, r // gcd(delta, r))
        for delta in delta_labels
    )
    elementary_alias_bound = (
        h_energy
        * delta_energy
        * min(left_alias_multiplicity, right_alias_multiplicity)
    )

    h_span = max(h_labels) - min(h_labels) + 1
    delta_span = max(delta_labels) - min(delta_labels) + 1
    left_interval_ceiling = sum(
        (delta_span + r // gcd(h, r) - 1) // (r // gcd(h, r))
        for h in h_labels
    )
    right_interval_ceiling = sum(
        (h_span + r // gcd(delta, r) - 1) // (r // gcd(delta, r))
        for delta in delta_labels
    )
    interval_span_bound = (
        h_energy
        * delta_energy
        * min(left_interval_ceiling, right_interval_ceiling)
    )
    tolerance = 1e-8
    return {
        "squarefree_modulus": r,
        "unit_frequencies": units,
        "product_residue_coefficients": product_residue_coefficients,
        "product_fourier_coefficients": product_fourier_coefficients,
        "primitive_projection": primitive_projection,
        "direct_primitive_energy": direct_primitive_energy,
        "parseval_primitive_energy": parseval_primitive_energy,
        "primitive_parseval_identity_exact": abs(
            direct_primitive_energy - parseval_primitive_energy
        )
        < tolerance,
        "h_coefficient_energy": h_energy,
        "delta_coefficient_energy": delta_energy,
        "left_alias_multiplicity": left_alias_multiplicity,
        "right_alias_multiplicity": right_alias_multiplicity,
        "elementary_alias_bound": elementary_alias_bound,
        "elementary_alias_bound_holds": (
            direct_primitive_energy <= elementary_alias_bound + tolerance
        ),
        "h_support_span": h_span,
        "delta_support_span": delta_span,
        "left_interval_ceiling": left_interval_ceiling,
        "right_interval_ceiling": right_interval_ceiling,
        "interval_span_bound": interval_span_bound,
        "interval_span_bound_holds": (
            direct_primitive_energy <= interval_span_bound + tolerance
        ),
        "constant_frequency_annihilated_by_cofactor_operator": True,
        "nonunit_frequencies_annihilated_by_cofactor_operator": True,
        "mobius_cancellation_used_in_elementary_bound": False,
        "analytic_primitive_product_spectrum_bound_proved": False,
        "coupled_kernel_gate_closed": False,
    }


def primitive_product_spectrum_exponent_audit(
    *,
    h_length_exponent: Fraction,
    delta_length_exponent: Fraction,
    modulus_exponent: Fraction,
) -> dict[str, object]:
    """Record the exponent loss in the elementary primitive-energy bound."""

    h = F(h_length_exponent)
    delta = F(delta_length_exponent)
    modulus = F(modulus_exponent)
    if min(h, delta, modulus) < 0:
        raise ValueError("all length and modulus exponents must be nonnegative")
    coefficient_energy = h + delta
    elementary_alias_factor = max(h, delta, h + delta - modulus)
    elementary_primitive_energy = coefficient_energy + elementary_alias_factor
    product_density_factor = max(F(0), h + delta - modulus)
    product_density_energy = coefficient_energy + product_density_factor
    return {
        "h_length_exponent": h,
        "delta_length_exponent": delta,
        "modulus_exponent": modulus,
        "coefficient_energy_exponent": coefficient_energy,
        "elementary_alias_factor_exponent": elementary_alias_factor,
        "elementary_primitive_energy_exponent": elementary_primitive_energy,
        "product_density_factor_exponent": product_density_factor,
        "product_density_energy_exponent": product_density_energy,
        "elementary_primitive_energy_deficit": max(
            F(0), elementary_primitive_energy - product_density_energy
        ),
        "mobius_cancellation_used": False,
        "primitive_product_spectrum_power_saving_proved": False,
        "coupled_kernel_gate_closed": False,
    }


def cochrane_shi_unit_product_spectrum_audit(
    *,
    h_length_exponent: Fraction,
    delta_length_exponent: Fraction,
    squarefree_modulus_exponent: Fraction,
) -> dict[str, object]:
    """Map the unit-label primitive spectrum to a published fourth moment.

    Cochrane--Shi Theorem 1 bounds the normalized nonprincipal fourth
    moment of a character sum on an arbitrary translated interval by
    ``r^epsilon * B^2`` for squarefree ``r``.  Multiplicative Plancherel
    and the squarefree Gauss bound ``|tau_r(chi)|^2 <= r`` therefore give

    ``E_prim(I,J) << r^epsilon*H*L + H^2*L^2/(r*phi(r))``

    when both outer variables are units modulo ``r`` and the weights are
    sharp interval indicators.  This adapter does not handle nonunit gcd
    strata or the actual smooth, nonseparable AFE packet.
    """

    h = F(h_length_exponent)
    delta = F(delta_length_exponent)
    modulus = F(squarefree_modulus_exponent)
    if min(h, delta, modulus) < 0:
        raise ValueError("all length and modulus exponents must be nonnegative")

    nonprincipal_fourth_moment_h = 2 * h
    nonprincipal_fourth_moment_delta = 2 * delta
    nonprincipal_primitive_energy = h + delta
    principal_primitive_energy = 2 * h + 2 * delta - 2 * modulus
    published_unit_interval_bound = max(
        nonprincipal_primitive_energy,
        principal_primitive_energy,
    )
    elementary = primitive_product_spectrum_exponent_audit(
        h_length_exponent=h,
        delta_length_exponent=delta,
        modulus_exponent=modulus,
    )
    product_density = F(elementary["product_density_energy_exponent"])
    return {
        "h_length_exponent": h,
        "delta_length_exponent": delta,
        "squarefree_modulus_exponent": modulus,
        "cochrane_shi_normalized_fourth_moment_h_exponent": (
            nonprincipal_fourth_moment_h
        ),
        "cochrane_shi_normalized_fourth_moment_delta_exponent": (
            nonprincipal_fourth_moment_delta
        ),
        "squarefree_gauss_weight_ceiling_exponent": modulus,
        "nonprincipal_primitive_energy_exponent": (
            nonprincipal_primitive_energy
        ),
        "principal_primitive_energy_exponent": principal_primitive_energy,
        "published_unit_interval_bound_exponent": published_unit_interval_bound,
        "elementary_primitive_energy_exponent": F(
            elementary["elementary_primitive_energy_exponent"]
        ),
        "saving_over_elementary_bound": max(
            F(0),
            F(elementary["elementary_primitive_energy_exponent"])
            - published_unit_interval_bound,
        ),
        "product_density_energy_exponent": product_density,
        "margin_below_product_density_energy": (
            product_density - published_unit_interval_bound
        ),
        "cochrane_shi_theorem_one_applies": True,
        "arbitrary_translated_sharp_intervals_covered": True,
        "squarefree_arithmetic_factor_absorbed_in_t_epsilon": True,
        "unit_outer_product_stratum_covered": True,
        "nonunit_gcd_strata_reduced_and_covered": False,
        "smooth_afe_packet_adapter_proved": False,
        "joint_q_phase_and_mobius_packet_bound_proved": False,
        "coupled_kernel_gate_closed": False,
    }


def nonunit_product_gcd_strata_audit(
    *,
    squarefree_modulus: int,
    h_labels: tuple[int, ...],
    delta_labels: tuple[int, ...],
) -> dict[str, object]:
    """Verify the exact reduced conductor on every nonunit product stratum."""

    r = int(squarefree_modulus)
    factorization = _finite_prime_exponents(r) if r > 1 else {}
    if r <= 1 or any(exponent != 1 for exponent in factorization.values()):
        raise ValueError("the modulus must be squarefree and greater than one")
    if not h_labels or not delta_labels:
        raise ValueError("both label families must be nonempty")

    units_r = tuple(value for value in range(1, r) if gcd(value, r) == 1)
    root_r = cmath.exp(2j * cmath.pi / r)
    rows: list[dict[str, object]] = []
    for h in tuple(int(value) for value in h_labels):
        for delta in tuple(int(value) for value in delta_labels):
            d = gcd(h, r)
            e = gcd(delta, r)
            w = d * e // gcd(d, e)
            reduced_modulus = r // w
            reduced_h = h // d
            reduced_delta = delta // e
            phase_multiplier = gcd(d, e)
            if reduced_modulus == 1:
                reduction_counts = {0: len(units_r)}
                expected_lift_count = len(units_r)
                phase_reduction_exact = all(
                    abs(root_r ** (k * h * delta % r) - 1) < 1e-8
                    for k in units_r
                )
            else:
                units_reduced = tuple(
                    value
                    for value in range(1, reduced_modulus)
                    if gcd(value, reduced_modulus) == 1
                )
                reduction_counts = {
                    residue: sum(1 for k in units_r if k % reduced_modulus == residue)
                    for residue in units_reduced
                }
                expected_lift_count = len(units_r) // len(units_reduced)
                root_reduced = cmath.exp(2j * cmath.pi / reduced_modulus)
                phase_reduction_exact = all(
                    abs(
                        root_r ** (k * h * delta % r)
                        - root_reduced
                        ** (
                            k
                            * phase_multiplier
                            * reduced_h
                            * reduced_delta
                            % reduced_modulus
                        )
                    )
                    < 1e-8
                    for k in units_r
                )
            rows.append(
                {
                    "h": h,
                    "delta": delta,
                    "h_modulus_gcd": d,
                    "delta_modulus_gcd": e,
                    "product_gcd_lcm": w,
                    "reduced_modulus": reduced_modulus,
                    "reduced_h": reduced_h,
                    "reduced_delta": reduced_delta,
                    "phase_multiplier": phase_multiplier,
                    "reduced_variables_are_units": (
                        gcd(reduced_h, reduced_modulus) == 1
                        and gcd(reduced_delta, reduced_modulus) == 1
                    ),
                    "phase_reduction_exact": phase_reduction_exact,
                    "frequency_reduction_counts": reduction_counts,
                    "expected_frequency_lift_count": expected_lift_count,
                    "uniform_frequency_lifts": all(
                        count == expected_lift_count
                        for count in reduction_counts.values()
                    ),
                    "fully_resonant_product": reduced_modulus == 1,
                    "fully_resonant_iff_modulus_divides_product": (
                        (reduced_modulus == 1) == (h * delta % r == 0)
                    ),
                }
            )

    return {
        "squarefree_modulus": r,
        "rows": tuple(rows),
        "all_reduced_variables_are_units": all(
            bool(row["reduced_variables_are_units"]) for row in rows
        ),
        "all_phase_reductions_exact": all(
            bool(row["phase_reduction_exact"]) for row in rows
        ),
        "all_frequency_lifts_uniform": all(
            bool(row["uniform_frequency_lifts"]) for row in rows
        ),
        "all_fully_resonant_conditions_exact": all(
            bool(row["fully_resonant_iff_modulus_divides_product"])
            for row in rows
        ),
        "nonunit_gcd_stratification_identity_proved": True,
        "cochrane_shi_reapplies_on_every_reduced_modulus_above_one": True,
        "fully_resonant_divisor_incidence_analytic_bound_proved": False,
        "smooth_afe_packet_adapter_proved": False,
        "coupled_kernel_gate_closed": False,
    }


def cochrane_shi_all_gcd_product_spectrum_audit(
    *,
    h_length_exponent: Fraction,
    delta_length_exponent: Fraction,
    squarefree_modulus_exponent: Fraction,
) -> dict[str, object]:
    """Record the sharp-interval bound after all nonunit gcd strata.

    Exact gcd splitting reduces every nonresonant stratum to the unit-label
    Cochrane--Shi fourth moment.  The reduced-modulus-one strata satisfy
    ``r | h*delta`` and have total interval mass
    ``r^epsilon*(H+L+H*L/r)``.  Cauchy over the divisor strata costs only
    ``r^epsilon`` for squarefree ``r``.
    """

    h = F(h_length_exponent)
    delta = F(delta_length_exponent)
    modulus = F(squarefree_modulus_exponent)
    if min(h, delta, modulus) < 0:
        raise ValueError("all length and modulus exponents must be nonnegative")

    unit = cochrane_shi_unit_product_spectrum_audit(
        h_length_exponent=h,
        delta_length_exponent=delta,
        squarefree_modulus_exponent=modulus,
    )
    fully_resonant_mass = max(F(0), h, delta, h + delta - modulus)
    fully_resonant_energy = 2 * fully_resonant_mass
    all_gcd_bound = max(
        F(unit["published_unit_interval_bound_exponent"]),
        fully_resonant_energy,
    )
    return {
        "h_length_exponent": h,
        "delta_length_exponent": delta,
        "squarefree_modulus_exponent": modulus,
        "unit_stratum_bound_exponent": F(
            unit["published_unit_interval_bound_exponent"]
        ),
        "fully_resonant_mass_exponent": fully_resonant_mass,
        "fully_resonant_energy_exponent": fully_resonant_energy,
        "all_gcd_sharp_interval_bound_exponent": all_gcd_bound,
        "product_density_energy_exponent": F(
            unit["product_density_energy_exponent"]
        ),
        "margin_below_product_density_energy": (
            F(unit["product_density_energy_exponent"]) - all_gcd_bound
        ),
        "squarefree_divisor_strata_cost_only_t_epsilon": True,
        "nonresonant_reduced_moduli_use_cochrane_shi": True,
        "fully_resonant_divisor_incidence_bound_proved": True,
        "all_sharp_interval_gcd_strata_covered": True,
        "smooth_afe_packet_adapter_proved": False,
        "joint_q_phase_and_mobius_packet_bound_proved": False,
        "coupled_kernel_gate_closed": False,
    }


def finite_two_variable_fourier_projective_audit(
    weight_rows: tuple[tuple[complex, ...], ...],
) -> dict[str, object]:
    """Check exact finite tensor Fourier reconstruction of a coupled weight.

    The continuous adapter in Section 9.88 uses a Fourier series with a
    variation-weighted Wiener norm.  On a finite ``H`` by ``L`` grid, this
    helper records the directly formalizable discrete identity and the
    corresponding weighted projective norm.
    """

    if not weight_rows or not weight_rows[0]:
        raise ValueError("the finite weight grid must be nonempty")
    h_size = len(weight_rows)
    delta_size = len(weight_rows[0])
    if any(len(row) != delta_size for row in weight_rows):
        raise ValueError("all finite weight-grid rows must have equal length")
    weights = tuple(tuple(complex(value) for value in row) for row in weight_rows)
    h_root = cmath.exp(2j * cmath.pi / h_size)
    delta_root = cmath.exp(2j * cmath.pi / delta_size)
    coefficients = tuple(
        tuple(
            sum(
                weights[h][delta]
                * h_root ** (-frequency_h * h % h_size)
                * delta_root ** (-frequency_delta * delta % delta_size)
                for h in range(h_size)
                for delta in range(delta_size)
            )
            / (h_size * delta_size)
            for frequency_delta in range(delta_size)
        )
        for frequency_h in range(h_size)
    )
    reconstruction = tuple(
        tuple(
            sum(
                coefficients[frequency_h][frequency_delta]
                * h_root ** (frequency_h * h % h_size)
                * delta_root ** (frequency_delta * delta % delta_size)
                for frequency_h in range(h_size)
                for frequency_delta in range(delta_size)
            )
            for delta in range(delta_size)
        )
        for h in range(h_size)
    )
    maximum_reconstruction_error = max(
        abs(reconstruction[h][delta] - weights[h][delta])
        for h in range(h_size)
        for delta in range(delta_size)
    )
    unweighted_projective_norm = sum(
        abs(coefficients[frequency_h][frequency_delta])
        for frequency_h in range(h_size)
        for frequency_delta in range(delta_size)
    )
    weighted_projective_norm = sum(
        abs(coefficients[frequency_h][frequency_delta])
        * (1 + min(frequency_h, h_size - frequency_h))
        * (1 + min(frequency_delta, delta_size - frequency_delta))
        for frequency_h in range(h_size)
        for frequency_delta in range(delta_size)
    )
    return {
        "h_grid_size": h_size,
        "delta_grid_size": delta_size,
        "fourier_coefficients": coefficients,
        "reconstruction": reconstruction,
        "maximum_reconstruction_error": maximum_reconstruction_error,
        "exact_reconstruction": maximum_reconstruction_error < 1e-8,
        "unweighted_projective_norm": unweighted_projective_norm,
        "variation_weighted_projective_norm": weighted_projective_norm,
        "finite_tensor_fourier_identity_proved": True,
        "continuous_sobolev_wiener_bound_proved_by_finite_check": False,
        "coupled_kernel_gate_closed": False,
    }


def smooth_projective_product_spectrum_audit(
    *,
    h_length_exponent: Fraction,
    delta_length_exponent: Fraction,
    squarefree_modulus_exponent: Fraction,
    weighted_projective_norm_exponent: Fraction = F(0),
    epsilon_budget: Fraction = F(1, 1000),
) -> dict[str, object]:
    """Propagate the all-gcd interval bound through the smooth adapter.

    Minkowski is used on the primitive-projection Hilbert norm, so a
    projective norm of size ``T^p`` costs ``T^(2p)`` in the energy.  The
    polylogarithmic core has ``p=0``; the power-enlarged core chooses its
    derivative slack small enough that ``2p`` fits inside the requested
    epsilon budget.
    """

    projective = F(weighted_projective_norm_exponent)
    epsilon = F(epsilon_budget)
    if projective < 0 or epsilon < 0:
        raise ValueError("projective loss and epsilon budget must be nonnegative")
    sharp = cochrane_shi_all_gcd_product_spectrum_audit(
        h_length_exponent=h_length_exponent,
        delta_length_exponent=delta_length_exponent,
        squarefree_modulus_exponent=squarefree_modulus_exponent,
    )
    sharp_exponent = F(sharp["all_gcd_sharp_interval_bound_exponent"])
    smooth_exponent = sharp_exponent + 2 * projective
    return {
        "h_length_exponent": F(h_length_exponent),
        "delta_length_exponent": F(delta_length_exponent),
        "squarefree_modulus_exponent": F(squarefree_modulus_exponent),
        "sharp_interval_energy_exponent": sharp_exponent,
        "weighted_projective_norm_exponent": projective,
        "minkowski_energy_cost_exponent": 2 * projective,
        "smooth_packet_energy_exponent": smooth_exponent,
        "epsilon_budget": epsilon,
        "projective_cost_absorbed_in_epsilon_budget": 2 * projective <= epsilon,
        "four_variable_sobolev_order_required_strictly_above_four": True,
        "bounded_variation_character_fourth_moment_adapter_proved": True,
        "smooth_archimedean_afe_packet_adapter_proved": True,
        "joint_q_phase_and_mobius_packet_bound_proved": False,
        "reflection_and_global_packet_map_proved": False,
        "coupled_kernel_gate_closed": False,
    }


def global_ratio_frequency_square_audit(
    *,
    squarefree_modulus: int,
    direct_coefficient: int,
    type_left_coefficients: dict[int, complex],
    type_right_coefficients: dict[int, complex],
    outer_product_coefficients: dict[int, complex],
) -> dict[str, object]:
    """Verify the global ratio-frequency and character-square identities.

    For the rank-one packet ``c_x(a)=C(x)U(a)``, where ``C`` is the product
    residue convolution of two Type coefficient families, Section 9.89
    rewrites the complete unequal-label cofactor Gram in three exact ways:

    * the direct four-label Kloosterman kernel;
    * one positive primitive ratio-frequency square;
    * one multiplicative-character Parseval moment.

    This helper checks all three finite identities and the exact factorization
    of the product-residue character transform.  It does not estimate the
    resulting determinant family.
    """

    s = int(squarefree_modulus)
    factorization = _finite_prime_exponents(s) if s > 1 else {}
    if s <= 1 or any(exponent != 1 for exponent in factorization.values()):
        raise ValueError("the modulus must be squarefree and greater than one")
    b_direct = int(direct_coefficient) % s
    if gcd(b_direct, s) != 1:
        raise ValueError("the direct coefficient must be a unit modulo s")
    if (
        not type_left_coefficients
        or not type_right_coefficients
        or not outer_product_coefficients
    ):
        raise ValueError("all three coefficient families must be nonempty")

    left = {int(label): complex(value) for label, value in type_left_coefficients.items()}
    right = {
        int(label): complex(value)
        for label, value in type_right_coefficients.items()
    }
    outer: dict[int, complex] = {}
    for label, value in outer_product_coefficients.items():
        residue = int(label) % s
        outer[residue] = outer.get(residue, 0j) + complex(value)
    if any(gcd(label, s) != 1 for label in (*left, *right)):
        raise ValueError("all Type labels must be units modulo s")

    units = tuple(value for value in range(1, s) if gcd(value, s) == 1)
    phi_s = len(units)
    root = cmath.exp(2j * cmath.pi / s)
    product_residue_coefficients = {
        residue: sum(
            left_value * right_value
            for d, left_value in left.items()
            for p, right_value in right.items()
            if d * p % s == residue
        )
        for residue in units
    }
    packet = {
        x: {
            a: product_residue_coefficients[x] * outer_value
            for a, outer_value in outer.items()
        }
        for x in units
    }
    additive_fourier = {
        x: {
            frequency: sum(
                coefficient * root ** (-frequency * a % s)
                for a, coefficient in packet[x].items()
            )
            for frequency in units
        }
        for x in units
    }

    direct_gram = 0j
    for x1 in units:
        for x2 in units:
            y = x1 * pow(x2, -1, s) % s
            inverse_y = pow(y, -1, s)
            for a, coefficient_a in packet[x1].items():
                for a2, coefficient_b in packet[x2].items():
                    kernel = sum(
                        root
                        ** (
                            b_direct * (y - 1) * value
                            + (a2 - a * inverse_y) * pow(value, -1, s)
                        )
                        for value in units
                    )
                    direct_gram += coefficient_a * coefficient_b.conjugate() * kernel

    frequency_square = sum(
        abs(
            sum(
                root ** (b_direct * x * pow(frequency, -1, s) % s)
                * additive_fourier[x][frequency * pow(x, -1, s) % s]
                for x in units
            )
        )
        ** 2
        for frequency in units
    )
    ratio_square = sum(
        abs(
            sum(
                root ** (b_direct * t % s)
                * additive_fourier[t * frequency % s][pow(t, -1, s)]
                for t in units
            )
        )
        ** 2
        for frequency in units
    )

    outer_fourier = {
        frequency: sum(
            coefficient * root ** (-frequency * a % s)
            for a, coefficient in outer.items()
        )
        for frequency in units
    }
    trace_vector = {
        t: root ** (b_direct * t % s) * outer_fourier[pow(t, -1, s)]
        for t in units
    }
    convolution_square = sum(
        abs(
            sum(
                trace_vector[t]
                * product_residue_coefficients[t * frequency % s]
                for t in units
            )
        )
        ** 2
        for frequency in units
    )

    primes = tuple(sorted(factorization))
    discrete_logs: dict[int, dict[int, int]] = {}
    character_roots: dict[int, complex] = {}
    for prime in primes:
        order = prime - 1
        if prime == 2:
            generator = 1
        else:
            order_prime_factors = tuple(_finite_prime_exponents(order))
            generator = next(
                candidate
                for candidate in range(2, prime)
                if all(
                    pow(candidate, order // divisor, prime) != 1
                    for divisor in order_prime_factors
                )
            )
        local_logs: dict[int, int] = {}
        current = 1
        for exponent in range(order):
            local_logs[current] = exponent
            current = current * generator % prime
        discrete_logs[prime] = local_logs
        character_roots[prime] = cmath.exp(2j * cmath.pi / order)

    character_indices = tuple(product(*(range(prime - 1) for prime in primes)))

    def character(index: tuple[int, ...], value: int) -> complex:
        result = 1 + 0j
        for component, prime in zip(index, primes):
            exponent = discrete_logs[prime][value % prime]
            result *= character_roots[prime] ** (
                component * exponent % (prime - 1)
            )
        return result

    character_rows: list[dict[str, object]] = []
    character_parseval = 0.0
    for index in character_indices:
        c_transform = sum(
            product_residue_coefficients[x] * character(index, x).conjugate()
            for x in units
        )
        left_transform = sum(
            coefficient * character(index, d).conjugate()
            for d, coefficient in left.items()
        )
        right_transform = sum(
            coefficient * character(index, p).conjugate()
            for p, coefficient in right.items()
        )
        trace_transform = sum(
            trace_vector[t] * character(index, t)
            for t in units
        )
        factorized = left_transform * right_transform
        character_parseval += abs(trace_transform) ** 2 * abs(c_transform) ** 2 / phi_s
        character_rows.append(
            {
                "character_index": index,
                "product_residue_transform": c_transform,
                "factorized_type_transform": factorized,
                "type_factorization_exact": abs(c_transform - factorized) < 1e-8,
                "trace_transform": trace_transform,
            }
        )

    tolerance = 1e-7
    return {
        "squarefree_modulus": s,
        "unit_residues": units,
        "product_residue_coefficients": product_residue_coefficients,
        "outer_product_residue_coefficients": outer,
        "direct_gram": direct_gram,
        "frequency_square": frequency_square,
        "ratio_square": ratio_square,
        "convolution_square": convolution_square,
        "character_parseval_square": character_parseval,
        "direct_gram_is_real": abs(direct_gram.imag) < tolerance,
        "direct_equals_frequency_square": abs(direct_gram.real - frequency_square)
        < tolerance,
        "frequency_equals_ratio_square": abs(frequency_square - ratio_square)
        < tolerance,
        "ratio_equals_rank_one_convolution_square": abs(
            ratio_square - convolution_square
        )
        < tolerance,
        "multiplicative_parseval_identity_exact": abs(
            convolution_square - character_parseval
        )
        < tolerance,
        "character_rows": tuple(character_rows),
        "all_type_character_transforms_factor_exactly": all(
            bool(row["type_factorization_exact"]) for row in character_rows
        ),
        "all_outer_cross_terms_retained": True,
        "absolute_values_taken_before_global_square": False,
        "type_mobius_weight_retained_inside_fixed_modulus_square": True,
        "outer_modulus_mobius_weight_retained_after_fixed_modulus_square": False,
        "cross_modulus_two_mobius_dispersion_proved": False,
        "type_i_ii_determinant_estimate_proved": False,
        "outer_modulus_average_proved": False,
        "coupled_kernel_gate_closed": False,
    }


def global_two_mobius_character_master_audit(
    *,
    squarefree_moduli: tuple[int, ...],
    direct_coefficient: int,
    type_base_coefficients: dict[int, complex],
    companion_type_coefficients: dict[int, complex],
    outer_product_coefficients: dict[int, complex],
    short_cutoff_u: int,
    short_cutoff_v: int,
) -> dict[str, object]:
    """Verify the global linear character master and exact Type split.

    Unlike :func:`global_ratio_frequency_square_audit`, this identity is
    kept linear in the squarefree modulus.  Hence the two application signs
    ``mu(s)`` and ``mu(d)`` are both present before any global dispersion.
    The inner ``mu(d)`` is split by the remainder-free two-cutoff identity,
    with ``d <= max(U,V)`` retained as an explicit boundary term.
    """

    moduli = tuple(int(value) for value in squarefree_moduli)
    if not moduli:
        raise ValueError("at least one squarefree modulus is required")
    for modulus in moduli:
        factors = _finite_prime_exponents(modulus) if modulus > 1 else {}
        if modulus <= 1 or any(exponent != 1 for exponent in factors.values()):
            raise ValueError("every modulus must be squarefree and greater than one")
        if gcd(int(direct_coefficient), modulus) != 1:
            raise ValueError("the direct coefficient must be a unit for every modulus")
    if (
        not type_base_coefficients
        or not companion_type_coefficients
        or not outer_product_coefficients
    ):
        raise ValueError("all coefficient families must be nonempty")
    cutoff_u = int(short_cutoff_u)
    cutoff_v = int(short_cutoff_v)
    if cutoff_u < 1 or cutoff_v < 1:
        raise ValueError("both Type cutoffs must be positive")
    boundary = max(cutoff_u, cutoff_v)

    base = {int(label): complex(value) for label, value in type_base_coefficients.items()}
    companion = {
        int(label): complex(value)
        for label, value in companion_type_coefficients.items()
    }
    outer = {
        int(label): complex(value)
        for label, value in outer_product_coefficients.items()
    }

    def character_data(modulus: int):
        factors = _finite_prime_exponents(modulus)
        primes = tuple(sorted(factors))
        discrete_logs: dict[int, dict[int, int]] = {}
        character_roots: dict[int, complex] = {}
        for prime in primes:
            order = prime - 1
            if prime == 2:
                generator = 1
            else:
                order_prime_factors = tuple(_finite_prime_exponents(order))
                generator = next(
                    candidate
                    for candidate in range(2, prime)
                    if all(
                        pow(candidate, order // divisor, prime) != 1
                        for divisor in order_prime_factors
                    )
                )
            logs: dict[int, int] = {}
            current = 1
            for exponent in range(order):
                logs[current] = exponent
                current = current * generator % prime
            discrete_logs[prime] = logs
            character_roots[prime] = cmath.exp(2j * cmath.pi / order)
        indices = tuple(product(*(range(prime - 1) for prime in primes)))
        units = tuple(
            value for value in range(1, modulus) if gcd(value, modulus) == 1
        )

        def evaluate(index: tuple[int, ...], value: int) -> complex:
            if gcd(value, modulus) != 1:
                return 0j
            result = 1 + 0j
            for component, prime in zip(index, primes):
                exponent = discrete_logs[prime][value % prime]
                result *= character_roots[prime] ** (
                    component * exponent % (prime - 1)
                )
            return result

        return units, indices, evaluate

    direct_packet = 0j
    character_master = 0j
    modulus_rows: list[dict[str, object]] = []
    for modulus in moduli:
        root = cmath.exp(2j * cmath.pi / modulus)
        mu_modulus = _finite_mobius(modulus)
        units, indices, character = character_data(modulus)
        for d, base_value in base.items():
            mu_d = _finite_mobius(d)
            if mu_d == 0:
                continue
            for p, companion_value in companion.items():
                product_label = d * p % modulus
                if gcd(product_label, modulus) != 1:
                    continue
                inverse_product = pow(product_label, -1, modulus)
                for a, outer_value in outer.items():
                    direct_packet += (
                        mu_modulus
                        * mu_d
                        * base_value
                        * companion_value
                        * outer_value
                        * root
                        ** (
                            int(direct_coefficient) * product_label
                            - a * inverse_product
                        )
                    )

        character_rows: list[dict[str, object]] = []
        modulus_master = 0j
        for index in indices:
            trace_transform = sum(
                root ** (int(direct_coefficient) * t % modulus)
                * character(index, t).conjugate()
                * sum(
                    coefficient
                    * root ** (-a * pow(t, -1, modulus) % modulus)
                    for a, coefficient in outer.items()
                )
                for t in units
            )
            d_transform = sum(
                _finite_mobius(d) * coefficient * character(index, d)
                for d, coefficient in base.items()
            )
            p_transform = sum(
                coefficient * character(index, p)
                for p, coefficient in companion.items()
            )
            small_transform = sum(
                _finite_mobius(d) * coefficient * character(index, d)
                for d, coefficient in base.items()
                if d <= boundary
            )
            type_i_transform = 0j
            type_ii_transform = 0j
            for d, coefficient in base.items():
                if d <= boundary:
                    continue
                divisors = _positive_divisors(d)
                short_short = sum(
                    _finite_mobius(b) * _finite_mobius(c)
                    for b in divisors
                    if b <= cutoff_u
                    for c in _positive_divisors(d // b)
                    if c <= cutoff_v
                )
                long_long = sum(
                    _finite_mobius(b) * _finite_mobius(c)
                    for b in divisors
                    if b > cutoff_u
                    for c in _positive_divisors(d // b)
                    if c > cutoff_v
                )
                type_i_transform += (
                    coefficient * character(index, d) * short_short
                )
                type_ii_transform += (
                    coefficient * character(index, d) * long_long
                )
            reconstructed_d = small_transform - type_i_transform + type_ii_transform
            term = trace_transform * d_transform * p_transform
            modulus_master += term
            character_rows.append(
                {
                    "character_index": index,
                    "trace_transform": trace_transform,
                    "mobius_type_transform": d_transform,
                    "companion_type_transform": p_transform,
                    "small_d_transform": small_transform,
                    "type_i_transform": type_i_transform,
                    "type_ii_transform": type_ii_transform,
                    "reconstructed_mobius_type_transform": reconstructed_d,
                    "type_split_exact": abs(d_transform - reconstructed_d) < 1e-8,
                }
            )
        modulus_master *= mu_modulus / len(units)
        character_master += modulus_master
        modulus_rows.append(
            {
                "modulus": modulus,
                "outer_mobius_weight": mu_modulus,
                "character_rows": tuple(character_rows),
                "all_character_type_splits_exact": all(
                    bool(row["type_split_exact"]) for row in character_rows
                ),
                "linear_character_master_contribution": modulus_master,
            }
        )

    tolerance = 1e-7
    return {
        "squarefree_moduli": moduli,
        "short_cutoff_u": cutoff_u,
        "short_cutoff_v": cutoff_v,
        "small_d_boundary": boundary,
        "direct_two_mobius_packet": direct_packet,
        "linear_character_master": character_master,
        "global_linear_character_identity_exact": abs(
            direct_packet - character_master
        )
        < tolerance,
        "modulus_rows": tuple(modulus_rows),
        "all_character_type_splits_exact": all(
            bool(row["all_character_type_splits_exact"]) for row in modulus_rows
        ),
        "outer_modulus_mobius_weight_retained_linearly": True,
        "inner_type_mobius_weight_retained_linearly": True,
        "small_d_boundary_retained_exactly": True,
        "mixed_type_rectangles_cancel_exactly": True,
        "absolute_values_taken_before_global_master": False,
        "global_cross_modulus_dispersion_proved": False,
        "exhaustive_afe_packet_map_proved": False,
        "coupled_kernel_gate_closed": False,
    }


def primitive_product_farey_collision_audit(
    *,
    moduli: tuple[int, ...],
    h_length_exponent: Fraction = F(5, 2),
    delta_length_exponent: Fraction = F(5, 2),
    modulus_exponent: Fraction = F(3),
) -> dict[str, object]:
    """Classify cross-modulus primitive product-frequency collisions.

    For ``t`` a unit modulo ``s``, the frequency ``inverse(t)/s`` is a
    reduced fraction.  Equality is therefore exactly equality of ``(s,t)``;
    distinct frequencies have circular spacing at least ``1/(s1*s2)``.
    The exponent ledger records the ordinary additive-large-sieve ceiling
    for the balanced product sequence.
    """

    modulus_family = tuple(int(value) for value in moduli)
    if not modulus_family:
        raise ValueError("at least one modulus is required")
    frequencies: list[dict[str, object]] = []
    for modulus in modulus_family:
        if modulus <= 1:
            raise ValueError("all moduli must be greater than one")
        for t in range(1, modulus):
            if gcd(t, modulus) != 1:
                continue
            numerator = pow(t, -1, modulus)
            frequencies.append(
                {
                    "modulus": modulus,
                    "unit_label": t,
                    "numerator": numerator,
                    "frequency": F(numerator, modulus),
                }
            )

    collision_rows: list[dict[str, object]] = []
    minimum_circular_spacing: Fraction | None = None
    for first_position, first in enumerate(frequencies):
        for second_position, second in enumerate(frequencies[first_position:], start=first_position):
            difference = abs(F(first["frequency"]) - F(second["frequency"]))
            circular = min(difference, 1 - difference)
            same_pair = (
                int(first["modulus"]) == int(second["modulus"])
                and int(first["unit_label"]) == int(second["unit_label"])
            )
            equal_frequency = difference == 0
            if not equal_frequency and (
                minimum_circular_spacing is None
                or circular < minimum_circular_spacing
            ):
                minimum_circular_spacing = circular
            denominator_product = int(first["modulus"]) * int(second["modulus"])
            collision_rows.append(
                {
                    "first": first,
                    "second": second,
                    "same_pair": same_pair,
                    "equal_frequency": equal_frequency,
                    "zero_frequency_collision_exact": equal_frequency == same_pair,
                    "circular_spacing": circular,
                    "farey_spacing_bound_holds": (
                        equal_frequency or circular >= F(1, denominator_product)
                    ),
                }
            )

    h = F(h_length_exponent)
    delta = F(delta_length_exponent)
    sigma = F(modulus_exponent)
    if min(h, delta, sigma) < 0:
        raise ValueError("all exponent inputs must be nonnegative")
    product_length = h + delta
    coefficient_energy = product_length
    large_sieve_energy = max(product_length, 2 * sigma) + coefficient_energy
    fixed_modulus_energy = cochrane_shi_all_gcd_product_spectrum_audit(
        h_length_exponent=h,
        delta_length_exponent=delta,
        squarefree_modulus_exponent=sigma,
    )["all_gcd_sharp_interval_bound_exponent"]
    fixed_moduli_aggregate = sigma + sigma + F(fixed_modulus_energy)
    return {
        "moduli": modulus_family,
        "frequencies": tuple(frequencies),
        "collision_rows": tuple(collision_rows),
        "all_zero_frequency_collisions_diagonal": all(
            bool(row["zero_frequency_collision_exact"]) for row in collision_rows
        ),
        "all_distinct_frequencies_obey_farey_spacing": all(
            bool(row["farey_spacing_bound_holds"]) for row in collision_rows
        ),
        "minimum_circular_spacing": minimum_circular_spacing,
        "product_length_exponent": product_length,
        "coefficient_energy_exponent": coefficient_energy,
        "additive_large_sieve_energy_exponent": large_sieve_energy,
        "summed_fixed_modulus_cochrane_shi_exponent": fixed_moduli_aggregate,
        "large_sieve_improves_summed_fixed_modulus_exponent": (
            large_sieve_energy < fixed_moduli_aggregate
        ),
        "zero_frequency_projector_classified": True,
        "same_diagonal_globally_reassembled": False,
        "signed_nonzero_frequency_estimate_proved": False,
        "coupled_kernel_gate_closed": False,
    }


def cross_modulus_product_frequency_density_audit(
    *,
    left_modulus: int,
    right_modulus: int,
) -> dict[str, object]:
    """Verify the exact local density and centering of product frequencies.

    Write ``s1=g*r1`` and ``s2=g*r2``.  Squarefreeness makes ``g``, ``r1``
    and ``r2`` pairwise coprime.  For inverse labels ``u_i`` the circular
    frequency difference has numerator

    ``kappa = r2*u1-r1*u2 (mod lcm(s1,s2))``.

    CRT gives one local unit restriction at primes dividing ``r1*r2`` and
    ``p-1`` or ``p-2`` choices at primes dividing ``g``.  The same product
    has an exact constant-density plus mean-zero local expansion.
    """

    s1 = int(left_modulus)
    s2 = int(right_modulus)
    factors1 = _finite_prime_exponents(s1) if s1 > 1 else {}
    factors2 = _finite_prime_exponents(s2) if s2 > 1 else {}
    if (
        s1 <= 1
        or s2 <= 1
        or any(exponent != 1 for exponent in (*factors1.values(), *factors2.values()))
    ):
        raise ValueError("both moduli must be squarefree and greater than one")

    common = gcd(s1, s2)
    left_cofactor = s1 // common
    right_cofactor = s2 // common
    lcm_modulus = common * left_cofactor * right_cofactor
    common_primes = tuple(sorted(_finite_prime_exponents(common)))
    cofactor_primes = tuple(
        sorted(_finite_prime_exponents(left_cofactor * right_cofactor))
    )
    all_primes = tuple(sorted((*common_primes, *cofactor_primes)))

    left_units = tuple(value for value in range(1, s1) if gcd(value, s1) == 1)
    right_units = tuple(value for value in range(1, s2) if gcd(value, s2) == 1)
    direct_multiplicities = {residue: 0 for residue in range(lcm_modulus)}
    for left_inverse in left_units:
        for right_inverse in right_units:
            residue = (
                right_cofactor * left_inverse
                - left_cofactor * right_inverse
            ) % lcm_modulus
            direct_multiplicities[residue] += 1

    formula_multiplicities: dict[int, int] = {}
    centered_factorizations: dict[int, Fraction] = {}
    expansion_values: dict[int, Fraction] = {}
    expansion_coefficients: dict[int, Fraction] = {}
    for divisor in _positive_divisors(lcm_modulus):
        coefficient = F(1)
        for prime in all_primes:
            if divisor % prime == 0:
                coefficient *= -1 if prime in cofactor_primes else 1
            elif prime in cofactor_primes:
                coefficient *= F(prime - 1, prime)
            else:
                coefficient *= F((prime - 1) ** 2, prime)
        expansion_coefficients[divisor] = coefficient

    for residue in range(lcm_modulus):
        if gcd(residue, left_cofactor * right_cofactor) != 1:
            formula = 0
        else:
            formula = 1
            for prime in common_primes:
                formula *= prime - 1 if residue % prime == 0 else prime - 2
        formula_multiplicities[residue] = formula

        centered_product = F(1)
        for prime in cofactor_primes:
            local_center = F(int(residue % prime == 0)) - F(1, prime)
            centered_product *= F(prime - 1, prime) - local_center
        for prime in common_primes:
            local_center = F(int(residue % prime == 0)) - F(1, prime)
            centered_product *= F((prime - 1) ** 2, prime) + local_center
        centered_factorizations[residue] = centered_product

        expansion = F(0)
        for divisor, coefficient in expansion_coefficients.items():
            basis = F(1)
            for prime in _finite_prime_exponents(divisor):
                basis *= F(int(residue % prime == 0)) - F(1, prime)
            expansion += coefficient * basis
        expansion_values[residue] = expansion

    def finite_totient(value: int) -> int:
        result = value
        for prime in _finite_prime_exponents(value):
            result = result // prime * (prime - 1)
        return result

    principal_density = F(
        finite_totient(s1) * finite_totient(s2),
        lcm_modulus,
    )
    centered_multiplicities = {
        residue: F(value) - principal_density
        for residue, value in formula_multiplicities.items()
    }
    zero_multiplicity = direct_multiplicities[0]
    tolerance_free_zero_diagonal = (
        zero_multiplicity > 0
    ) == (s1 == s2)
    return {
        "left_modulus": s1,
        "right_modulus": s2,
        "common_modulus_factor": common,
        "left_coprime_cofactor": left_cofactor,
        "right_coprime_cofactor": right_cofactor,
        "lcm_modulus": lcm_modulus,
        "direct_frequency_multiplicities": direct_multiplicities,
        "local_product_formula_multiplicities": formula_multiplicities,
        "direct_equals_local_product_formula": (
            direct_multiplicities == formula_multiplicities
        ),
        "centered_local_factorizations": centered_factorizations,
        "centered_local_factorization_exact": all(
            centered_factorizations[residue] == formula_multiplicities[residue]
            for residue in range(lcm_modulus)
        ),
        "centered_basis_expansion_coefficients": expansion_coefficients,
        "centered_basis_expansion_values": expansion_values,
        "centered_basis_expansion_exact": all(
            expansion_values[residue] == formula_multiplicities[residue]
            for residue in range(lcm_modulus)
        ),
        "principal_local_density": principal_density,
        "principal_density_equals_average_multiplicity": (
            principal_density
            == F(sum(direct_multiplicities.values()), lcm_modulus)
        ),
        "centered_frequency_multiplicities": centered_multiplicities,
        "centered_frequency_sum_is_zero": (
            sum(centered_multiplicities.values(), F(0)) == 0
        ),
        "zero_frequency_multiplicity": zero_multiplicity,
        "zero_frequency_occurs_exactly_on_same_modulus": (
            tolerance_free_zero_diagonal
        ),
        "outer_mobius_product": _finite_mobius(s1) * _finite_mobius(s2),
        "cofactor_mobius_product": (
            _finite_mobius(left_cofactor) * _finite_mobius(right_cofactor)
        ),
        "common_factor_mobius_sign_cancels": (
            _finite_mobius(s1) * _finite_mobius(s2)
            == _finite_mobius(left_cofactor) * _finite_mobius(right_cofactor)
        ),
        "weighted_type_packet_centered": False,
        "signed_nonzero_frequency_estimate_proved": False,
        "coupled_kernel_gate_closed": False,
    }


def weighted_cross_modulus_hoeffding_audit(
    *,
    left_modulus: int,
    right_modulus: int,
    inverse_pair_weights: dict[tuple[int, int], Fraction],
) -> dict[str, object]:
    """Decompose an arbitrary inverse-label packet by CRT coordinates."""

    s1 = int(left_modulus)
    s2 = int(right_modulus)
    factors1 = _finite_prime_exponents(s1) if s1 > 1 else {}
    factors2 = _finite_prime_exponents(s2) if s2 > 1 else {}
    if (
        s1 <= 1
        or s2 <= 1
        or any(exponent != 1 for exponent in (*factors1.values(), *factors2.values()))
    ):
        raise ValueError("both moduli must be squarefree and greater than one")

    common = gcd(s1, s2)
    lcm_modulus = s1 * s2 // common
    primes = tuple(sorted(_finite_prime_exponents(lcm_modulus)))
    states = tuple(
        (left_inverse, right_inverse)
        for left_inverse in range(1, s1)
        if gcd(left_inverse, s1) == 1
        for right_inverse in range(1, s2)
        if gcd(right_inverse, s2) == 1
    )
    supplied_states = set(inverse_pair_weights)
    if supplied_states != set(states):
        raise ValueError("weights must be supplied for every unit inverse-label pair")
    weights = {state: F(inverse_pair_weights[state]) for state in states}

    local_coordinates = {
        state: {
            prime: (
                (state[0] % prime, state[1] % prime)
                if s1 % prime == 0 and s2 % prime == 0
                else state[0] % prime
                if s1 % prime == 0
                else state[1] % prime
            )
            for prime in primes
        }
        for state in states
    }

    def conditional_average(
        values: dict[tuple[int, int], Fraction],
        prime: int,
    ) -> dict[tuple[int, int], Fraction]:
        groups: dict[tuple[object, ...], list[tuple[int, int]]] = {}
        other_primes = tuple(value for value in primes if value != prime)
        for state in states:
            key = tuple(local_coordinates[state][value] for value in other_primes)
            groups.setdefault(key, []).append(state)
        result: dict[tuple[int, int], Fraction] = {}
        for group in groups.values():
            average = sum((values[state] for state in group), F(0)) / len(group)
            for state in group:
                result[state] = average
        return result

    component_values: dict[int, dict[tuple[int, int], Fraction]] = {}
    for divisor in _positive_divisors(lcm_modulus):
        values = dict(weights)
        for prime in primes:
            averaged = conditional_average(values, prime)
            if divisor % prime == 0:
                values = {
                    state: values[state] - averaged[state] for state in states
                }
            else:
                values = averaged
        component_values[divisor] = values

    reconstructed = {
        state: sum(
            (component_values[divisor][state] for divisor in component_values),
            F(0),
        )
        for state in states
    }
    original_energy = sum((value * value for value in weights.values()), F(0))
    component_energies = {
        divisor: sum((value * value for value in values.values()), F(0))
        for divisor, values in component_values.items()
    }
    component_energy_sum = sum(component_energies.values(), F(0))
    pairwise_inner_products: dict[tuple[int, int], Fraction] = {}
    component_divisors = tuple(component_values)
    for left_position, left_divisor in enumerate(component_divisors):
        for right_divisor in component_divisors[left_position + 1 :]:
            pairwise_inner_products[(left_divisor, right_divisor)] = sum(
                (
                    component_values[left_divisor][state]
                    * component_values[right_divisor][state]
                    for state in states
                ),
                F(0),
            )

    active_prime_marginal_sums: dict[
        tuple[int, int], tuple[Fraction, ...]
    ] = {}
    for divisor, values in component_values.items():
        for prime in primes:
            if divisor % prime != 0:
                continue
            other_primes = tuple(value for value in primes if value != prime)
            groups: dict[tuple[object, ...], list[tuple[int, int]]] = {}
            for state in states:
                key = tuple(local_coordinates[state][value] for value in other_primes)
                groups.setdefault(key, []).append(state)
            active_prime_marginal_sums[(divisor, prime)] = tuple(
                sum((values[state] for state in group), F(0))
                for group in groups.values()
            )

    left_cofactor = s1 // common
    right_cofactor = s2 // common
    frequency_residues = {
        state: (
            right_cofactor * state[0] - left_cofactor * state[1]
        )
        % lcm_modulus
        for state in states
    }
    unweighted_fibre_multiplicities = {
        residue: sum(
            1 for state in states if frequency_residues[state] == residue
        )
        for residue in range(lcm_modulus)
    }
    weighted_fibre_sums = {
        residue: sum(
            (
                weights[state]
                for state in states
                if frequency_residues[state] == residue
            ),
            F(0),
        )
        for residue in range(lcm_modulus)
    }
    component_fibre_sums = {
        divisor: {
            residue: sum(
                (
                    values[state]
                    for state in states
                    if frequency_residues[state] == residue
                ),
                F(0),
            )
            for residue in range(lcm_modulus)
        }
        for divisor, values in component_values.items()
    }
    packet_mean = sum(weights.values(), F(0)) / len(states)
    principal_density = F(len(states), lcm_modulus)
    principal_weighted_density = packet_mean * principal_density
    constant_centered_fibre_sums = {
        residue: packet_mean
        * (F(unweighted_fibre_multiplicities[residue]) - principal_density)
        for residue in range(lcm_modulus)
    }
    nonconstant_fibre_sums = {
        residue: sum(
            (
                component_fibre_sums[divisor][residue]
                for divisor in component_fibre_sums
                if divisor > 1
            ),
            F(0),
        )
        for residue in range(lcm_modulus)
    }
    weighted_fibre_reassembly = {
        residue: (
            principal_weighted_density
            + constant_centered_fibre_sums[residue]
            + nonconstant_fibre_sums[residue]
        )
        for residue in range(lcm_modulus)
    }
    constant_component_matches = all(
        component_fibre_sums[1][residue]
        == packet_mean * unweighted_fibre_multiplicities[residue]
        for residue in range(lcm_modulus)
    )
    constant_centered_zero = (
        sum(constant_centered_fibre_sums.values(), F(0)) == 0
    )
    nonconstant_zero = sum(nonconstant_fibre_sums.values(), F(0)) == 0
    weighted_reassembly_exact = weighted_fibre_reassembly == weighted_fibre_sums
    energy_identity_exact = component_energy_sum == original_energy
    pairwise_orthogonal = all(
        value == 0 for value in pairwise_inner_products.values()
    )
    active_marginals_zero = all(
        value == 0
        for marginal_sums in active_prime_marginal_sums.values()
        for value in marginal_sums
    )
    return {
        "left_modulus": s1,
        "right_modulus": s2,
        "lcm_modulus": lcm_modulus,
        "component_point_values": component_values,
        "reconstructed_point_values": reconstructed,
        "pointwise_reconstruction_exact": reconstructed == weights,
        "original_l2_energy": original_energy,
        "component_l2_energies": component_energies,
        "component_energy_sum": component_energy_sum,
        "orthogonal_energy_identity_exact": energy_identity_exact,
        "pairwise_component_inner_products": pairwise_inner_products,
        "all_distinct_components_pairwise_orthogonal": pairwise_orthogonal,
        "active_prime_conditional_marginal_sums": active_prime_marginal_sums,
        "all_active_prime_conditional_marginals_zero": active_marginals_zero,
        "frequency_residue_by_inverse_pair": frequency_residues,
        "unweighted_frequency_fibre_multiplicities": (
            unweighted_fibre_multiplicities
        ),
        "weighted_frequency_fibre_sums": weighted_fibre_sums,
        "component_frequency_fibre_sums": component_fibre_sums,
        "packet_global_mean": packet_mean,
        "principal_local_density": principal_density,
        "principal_weighted_density": principal_weighted_density,
        "constant_centered_frequency_fibre_sums": (
            constant_centered_fibre_sums
        ),
        "nonconstant_component_frequency_fibre_sums": nonconstant_fibre_sums,
        "weighted_fibre_reassembly": weighted_fibre_reassembly,
        "weighted_fibre_reassembly_exact": weighted_reassembly_exact,
        "constant_component_matches_mean_times_unweighted_multiplicity": (
            constant_component_matches
        ),
        "constant_centered_frequency_sum_is_zero": constant_centered_zero,
        "nonconstant_component_frequency_sum_is_zero": nonconstant_zero,
        "arbitrary_fixed_modulus_pair_packet_centered_exactly": (
            weighted_reassembly_exact
            and constant_component_matches
            and constant_centered_zero
            and nonconstant_zero
            and energy_identity_exact
            and pairwise_orthogonal
            and active_marginals_zero
        ),
        "outer_mobius_pair_weight_retained_linearly": True,
        "inner_type_mobius_weights_retained_linearly": True,
        "h_delta_product_packet_retained_linearly": True,
        "afe_reflection_principal_density_reassembled": False,
        "signed_centered_dispersion_estimate_proved": False,
        "coupled_kernel_gate_closed": False,
    }


def weighted_principal_density_normalization_audit(
    *,
    modulus_packets: dict[int, dict[int, Fraction]],
) -> dict[str, object]:
    """Check whether the kappa ledger contains an LCM normalization."""

    if not modulus_packets:
        raise ValueError("at least one squarefree modulus packet is required")
    packets: dict[int, dict[int, Fraction]] = {}
    unit_rows: dict[int, tuple[int, ...]] = {}
    for raw_modulus, raw_packet in modulus_packets.items():
        modulus = int(raw_modulus)
        factors = _finite_prime_exponents(modulus) if modulus > 1 else {}
        if modulus <= 1 or any(exponent != 1 for exponent in factors.values()):
            raise ValueError("every packet modulus must be squarefree and greater than one")
        units = tuple(value for value in range(1, modulus) if gcd(value, modulus) == 1)
        if set(raw_packet) != set(units):
            raise ValueError("each packet must contain every unit inverse label")
        packets[modulus] = {unit: F(raw_packet[unit]) for unit in units}
        unit_rows[modulus] = units

    totals = {
        modulus: sum(packet.values(), F(0))
        for modulus, packet in packets.items()
    }
    signed_totals = {
        modulus: _finite_mobius(modulus) * total
        for modulus, total in totals.items()
    }
    global_total = sum(signed_totals.values(), F(0))
    global_square = global_total * global_total

    reciprocal_lcm_candidate = F(0)
    unnormalized_principal = F(0)
    explicit_normalized_kappa_average = F(0)
    pair_rows: list[dict[str, object]] = []
    for left_modulus, left_total in totals.items():
        for right_modulus, right_total in totals.items():
            lcm_modulus = left_modulus * right_modulus // gcd(
                left_modulus, right_modulus
            )
            left_phi = len(unit_rows[left_modulus])
            right_phi = len(unit_rows[right_modulus])
            packet_pair_mean = F(left_total, left_phi) * F(
                right_total, right_phi
            )
            principal_density = F(left_phi * right_phi, lcm_modulus)
            per_frequency_principal = packet_pair_mean * principal_density
            outer_sign = _finite_mobius(left_modulus) * _finite_mobius(
                right_modulus
            )
            direct_reciprocal_lcm_contribution = F(
                outer_sign * left_total * right_total,
                lcm_modulus,
            )
            unnormalized_contribution = sum(
                (
                    outer_sign * per_frequency_principal
                    for _ in range(lcm_modulus)
                ),
                F(0),
            )
            explicit_normalized_kappa_average_contribution = F(
                unnormalized_contribution,
                lcm_modulus,
            )
            reciprocal_lcm_candidate += direct_reciprocal_lcm_contribution
            explicit_normalized_kappa_average += (
                explicit_normalized_kappa_average_contribution
            )
            unnormalized_principal += unnormalized_contribution
            pair_rows.append(
                {
                    "left_modulus": left_modulus,
                    "right_modulus": right_modulus,
                    "lcm_modulus": lcm_modulus,
                    "packet_pair_mean": packet_pair_mean,
                    "principal_density": principal_density,
                    "per_frequency_principal": per_frequency_principal,
                    "direct_reciprocal_lcm_contribution": (
                        direct_reciprocal_lcm_contribution
                    ),
                    "explicit_normalized_kappa_average_contribution": (
                        explicit_normalized_kappa_average_contribution
                    ),
                    "unnormalized_kappa_sum_contribution": (
                        unnormalized_contribution
                    ),
                }
            )

    return {
        "packet_totals": totals,
        "outer_signed_packet_totals": signed_totals,
        "global_linear_packet_total": global_total,
        "global_square": global_square,
        "pair_rows": tuple(pair_rows),
        "reciprocal_lcm_density_candidate": reciprocal_lcm_candidate,
        "explicit_normalized_kappa_average_principal_total": (
            explicit_normalized_kappa_average
        ),
        "unnormalized_kappa_principal_total": unnormalized_principal,
        "unnormalized_principal_recovers_global_square": (
            unnormalized_principal == global_square
        ),
        "reciprocal_lcm_candidate_requires_kappa_average": (
            reciprocal_lcm_candidate == explicit_normalized_kappa_average
        ),
        "reciprocal_lcm_saving_present_in_original_square": False,
        "afe_ttstar_extra_lcm_normalization_proved": False,
        "principal_density_bound_proved": False,
        "coupled_kernel_gate_closed": False,
    }


def weighted_frequency_multiplier_centering_audit(
    *,
    left_modulus: int,
    right_modulus: int,
    inverse_pair_weights: dict[tuple[int, int], Fraction],
    frequency_multiplier: dict[int, Fraction],
) -> dict[str, object]:
    """Center both a weighted CRT packet and its frequency multiplier."""

    packet = weighted_cross_modulus_hoeffding_audit(
        left_modulus=left_modulus,
        right_modulus=right_modulus,
        inverse_pair_weights=inverse_pair_weights,
    )
    lcm_modulus = int(packet["lcm_modulus"])
    residues = tuple(range(lcm_modulus))
    if set(frequency_multiplier) != set(residues):
        raise ValueError("the multiplier must contain every frequency residue")
    multiplier = {
        residue: F(frequency_multiplier[residue]) for residue in residues
    }
    multiplier_mean = sum(multiplier.values(), F(0)) / lcm_modulus
    centered_multiplier = {
        residue: value - multiplier_mean
        for residue, value in multiplier.items()
    }

    weighted_fibres = packet["weighted_frequency_fibre_sums"]
    constant_centered_fibres = packet[
        "constant_centered_frequency_fibre_sums"
    ]
    component_fibres = packet["component_frequency_fibre_sums"]
    direct_pairing = sum(
        (
            multiplier[residue] * weighted_fibres[residue]
            for residue in residues
        ),
        F(0),
    )
    total_packet_weight = sum(
        (F(value) for value in inverse_pair_weights.values()),
        F(0),
    )
    principal_mean_term = multiplier_mean * total_packet_weight
    constant_centered_pairing = sum(
        (
            centered_multiplier[residue]
            * constant_centered_fibres[residue]
            for residue in residues
        ),
        F(0),
    )
    component_pairings = {
        divisor: sum(
            (
                centered_multiplier[residue] * fibre_values[residue]
                for residue in residues
            ),
            F(0),
        )
        for divisor, fibre_values in component_fibres.items()
        if divisor > 1
    }
    nonconstant_pairing = sum(component_pairings.values(), F(0))
    centered_pairing = constant_centered_pairing + nonconstant_pairing
    reassembly = principal_mean_term + centered_pairing

    full_multiplier_constant_pairing = sum(
        (
            multiplier[residue] * constant_centered_fibres[residue]
            for residue in residues
        ),
        F(0),
    )
    full_multiplier_component_pairings = {
        divisor: sum(
            (
                multiplier[residue] * fibre_values[residue]
                for residue in residues
            ),
            F(0),
        )
        for divisor, fibre_values in component_fibres.items()
        if divisor > 1
    }

    fibre_multiplicities = packet[
        "unweighted_frequency_fibre_multiplicities"
    ]
    maximum_fibre_multiplicity = max(fibre_multiplicities.values())
    common_modulus = gcd(int(left_modulus), int(right_modulus))
    common_phi = sum(
        1
        for value in range(1, common_modulus + 1)
        if gcd(value, common_modulus) == 1
    )
    centered_multiplier_energy = sum(
        (value * value for value in centered_multiplier.values()),
        F(0),
    )
    constant_centered_fibre_energy = sum(
        (value * value for value in constant_centered_fibres.values()),
        F(0),
    )
    component_fibre_energies = {
        divisor: sum((value * value for value in values.values()), F(0))
        for divisor, values in component_fibres.items()
        if divisor > 1
    }
    centered_output_energy_sum = (
        constant_centered_fibre_energy
        + sum(component_fibre_energies.values(), F(0))
    )
    active_centered_term_count = int(constant_centered_fibre_energy != 0) + sum(
        energy != 0 for energy in component_fibre_energies.values()
    )
    observed_cauchy_squared_upper_bound = (
        centered_multiplier_energy
        * active_centered_term_count
        * centered_output_energy_sum
    )
    component_input_energies = packet["component_l2_energies"]
    component_incidence_bounds = {
        1: (
            constant_centered_fibre_energy
            <= maximum_fibre_multiplicity * component_input_energies[1]
        ),
        **{
            divisor: (
                energy
                <= maximum_fibre_multiplicity
                * component_input_energies[divisor]
            )
            for divisor, energy in component_fibre_energies.items()
        },
    }
    divisor_count = len(_positive_divisors(lcm_modulus))
    universal_incidence_squared_upper_bound = (
        centered_multiplier_energy
        * divisor_count
        * common_phi
        * F(packet["original_l2_energy"])
    )
    centered_pairing_square = centered_pairing * centered_pairing

    return {
        "left_modulus": int(left_modulus),
        "right_modulus": int(right_modulus),
        "common_modulus": common_modulus,
        "lcm_modulus": lcm_modulus,
        "weighted_frequency_fibre_sums": weighted_fibres,
        "frequency_multiplier": multiplier,
        "multiplier_global_mean": multiplier_mean,
        "centered_frequency_multiplier": centered_multiplier,
        "centered_multiplier_sum_is_zero": (
            sum(centered_multiplier.values(), F(0)) == 0
        ),
        "direct_multiplier_pairing": direct_pairing,
        "principal_multiplier_mean_term": principal_mean_term,
        "constant_fibre_centered_pairing": constant_centered_pairing,
        "nonconstant_component_pairings": component_pairings,
        "nonconstant_packet_component_pairing": nonconstant_pairing,
        "double_centered_pairing": centered_pairing,
        "double_centered_reassembly": reassembly,
        "double_centered_reassembly_exact": reassembly == direct_pairing,
        "all_centered_fibre_terms_ignore_multiplier_mean": (
            full_multiplier_constant_pairing == constant_centered_pairing
            and full_multiplier_component_pairings == component_pairings
        ),
        "maximum_frequency_fibre_multiplicity": maximum_fibre_multiplicity,
        "common_gcd_euler_phi": common_phi,
        "maximum_fibre_multiplicity_equals_common_gcd_phi": (
            maximum_fibre_multiplicity == common_phi
        ),
        "centered_multiplier_l2_energy": centered_multiplier_energy,
        "constant_centered_fibre_l2_energy": constant_centered_fibre_energy,
        "nonconstant_component_fibre_l2_energies": component_fibre_energies,
        "centered_output_energy_sum": centered_output_energy_sum,
        "active_centered_term_count": active_centered_term_count,
        "observed_cauchy_squared_upper_bound": (
            observed_cauchy_squared_upper_bound
        ),
        "universal_incidence_squared_upper_bound": (
            universal_incidence_squared_upper_bound
        ),
        "double_centered_pairing_obeys_observed_cauchy_bound": (
            centered_pairing_square <= observed_cauchy_squared_upper_bound
        ),
        "component_incidence_bounds": component_incidence_bounds,
        "every_component_obeys_common_gcd_incidence_bound": all(
            component_incidence_bounds.values()
        ),
        "double_centered_pairing_obeys_universal_incidence_bound": (
            centered_pairing_square <= universal_incidence_squared_upper_bound
        ),
        "zero_mean_multiplier_eliminates_bare_principal_term": (
            multiplier_mean != 0 or principal_mean_term == 0
        ),
        "zero_mean_multiplier_eliminates_centered_pairing": (
            multiplier_mean == 0 and centered_pairing == 0
        ),
        "outer_mobius_pair_weight_retained_linearly": True,
        "inner_type_mobius_weights_retained_linearly": True,
        "h_delta_product_packet_retained_linearly": True,
        "physical_afe_ttstar_multiplier_derived_exhaustively": False,
        "principal_multiplier_mean_reassembled": False,
        "signed_double_centered_dispersion_estimate_proved": False,
        "coupled_kernel_gate_closed": False,
    }


def cross_modulus_product_label_phase_audit(
    *,
    left_modulus: int,
    right_modulus: int,
    left_product_label: int,
    right_product_label: int,
) -> dict[str, object]:
    """Classify when two product-label phases depend only on kappa."""

    s1 = int(left_modulus)
    s2 = int(right_modulus)
    factors1 = _finite_prime_exponents(s1) if s1 > 1 else {}
    factors2 = _finite_prime_exponents(s2) if s2 > 1 else {}
    if (
        s1 <= 1
        or s2 <= 1
        or any(exponent != 1 for exponent in (*factors1.values(), *factors2.values()))
    ):
        raise ValueError("both moduli must be squarefree and greater than one")

    a1 = int(left_product_label)
    a2 = int(right_product_label)
    common = gcd(s1, s2)
    left_cofactor = s1 // common
    right_cofactor = s2 // common
    lcm_modulus = common * left_cofactor * right_cofactor
    compatible = (a1 - a2) % common == 0

    circular_coefficient: int | None = None
    coefficient_congruences_hold = False
    if compatible:
        if right_cofactor == 1:
            lift = 0
        else:
            lift = (
                F(a1 - a2, common)
                * pow(left_cofactor, -1, right_cofactor)
            ) % right_cofactor
            lift = int(lift)
        circular_coefficient = (-a1 + s1 * lift) % lcm_modulus
        coefficient_congruences_hold = (
            (circular_coefficient + a1) % s1 == 0
            and (circular_coefficient + a2) % s2 == 0
        )

    unit_pairs = tuple(
        (left_unit, right_unit)
        for left_unit in range(1, s1)
        if gcd(left_unit, s1) == 1
        for right_unit in range(1, s2)
        if gcd(right_unit, s2) == 1
    )
    original_phase_exponents = {
        pair: (
            -a1 * right_cofactor * pair[0]
            + a2 * left_cofactor * pair[1]
        )
        % lcm_modulus
        for pair in unit_pairs
    }
    circular_frequency_residues = {
        pair: (
            right_cofactor * pair[0] - left_cofactor * pair[1]
        )
        % lcm_modulus
        for pair in unit_pairs
    }
    factored_phase_exponents = (
        {
            pair: circular_coefficient * circular_frequency_residues[pair]
            % lcm_modulus
            for pair in unit_pairs
        }
        if circular_coefficient is not None
        else None
    )
    all_phase_exponents_match = (
        factored_phase_exponents == original_phase_exponents
        if factored_phase_exponents is not None
        else False
    )
    left_divides = a1 % s1 == 0
    right_divides = a2 % s2 == 0
    principal_mode = circular_coefficient == 0

    return {
        "left_modulus": s1,
        "right_modulus": s2,
        "common_modulus": common,
        "left_cofactor": left_cofactor,
        "right_cofactor": right_cofactor,
        "lcm_modulus": lcm_modulus,
        "left_product_label": a1,
        "right_product_label": a2,
        "product_labels_congruent_mod_common_modulus": compatible,
        "circular_frequency_coefficient": circular_coefficient,
        "coefficient_crt_congruences_hold": coefficient_congruences_hold,
        "circular_frequency_residues": circular_frequency_residues,
        "original_phase_exponents": original_phase_exponents,
        "factored_phase_exponents": factored_phase_exponents,
        "all_unit_pair_phase_exponents_match": all_phase_exponents_match,
        "phase_factors_through_single_circular_character": (
            compatible
            and coefficient_congruences_hold
            and all_phase_exponents_match
        ),
        "circular_multiplier_mean_classified": compatible,
        "circular_multiplier_has_zero_mean": (
            compatible and circular_coefficient != 0
        ),
        "left_modulus_divides_left_product_label": left_divides,
        "right_modulus_divides_right_product_label": right_divides,
        "principal_circular_multiplier_mode": principal_mode,
        "principal_mode_iff_both_product_labels_divisible": (
            principal_mode == (left_divides and right_divides)
        ),
        "h_delta_product_labels_retained_exactly": True,
        "outer_mobius_pair_weight_retained_linearly": True,
        "inner_type_mobius_weights_retained_linearly": True,
        "physical_afe_ttstar_packet_map_exhaustive": False,
        "double_divisibility_resonant_sum_bounded": False,
        "signed_nonfactorable_label_dispersion_proved": False,
        "coupled_kernel_gate_closed": False,
    }


def product_label_divisibility_gcd_split_audit(
    *,
    modulus: int,
    h: int,
    delta: int,
) -> dict[str, object]:
    """Verify 1_(s|h*delta) by the unique d=(h,s) stratum."""

    s = int(modulus)
    factors = _finite_prime_exponents(s) if s > 1 else {}
    if s <= 1 or any(exponent != 1 for exponent in factors.values()):
        raise ValueError("the modulus must be squarefree and greater than one")
    h_value = int(h)
    delta_value = int(delta)
    h_modulus_gcd = gcd(h_value, s)
    divisor_rows = tuple(
        {
            "divisor": divisor,
            "h_gcd_matches": h_modulus_gcd == divisor,
            "complement_divides_delta": delta_value % (s // divisor) == 0,
            "stratum_active": (
                h_modulus_gcd == divisor
                and delta_value % (s // divisor) == 0
            ),
        }
        for divisor in _positive_divisors(s)
    )
    active_strata = tuple(
        int(row["divisor"])
        for row in divisor_rows
        if bool(row["stratum_active"])
    )
    split_total = sum(bool(row["stratum_active"]) for row in divisor_rows)
    direct = h_value * delta_value % s == 0
    return {
        "modulus": s,
        "h": h_value,
        "delta": delta_value,
        "h_modulus_gcd": h_modulus_gcd,
        "divisor_rows": divisor_rows,
        "active_divisor_strata": active_strata,
        "direct_modulus_divides_product": direct,
        "gcd_divisibility_split_total": split_total,
        "gcd_divisibility_split_exact": split_total == int(direct),
        "active_stratum_is_unique_when_product_divisible": (
            not direct or active_strata == (h_modulus_gcd,)
        ),
        "h_delta_product_structure_retained": True,
        "resonant_sum_bounded": False,
        "coupled_kernel_gate_closed": False,
    }


def product_label_resonant_pair_count_audit(
    *,
    modulus: int,
    h_radius: int,
    delta_radius: int,
) -> dict[str, object]:
    """Count signed product labels satisfying s | h*delta."""

    s = int(modulus)
    factors = _finite_prime_exponents(s) if s > 1 else {}
    if s <= 1 or any(exponent != 1 for exponent in factors.values()):
        raise ValueError("the modulus must be squarefree and greater than one")
    h_bound = int(h_radius)
    delta_bound = int(delta_radius)
    if h_bound <= 0 or delta_bound <= 0:
        raise ValueError("both signed radii must be positive")

    divisors = _positive_divisors(s)
    h_counts = {
        divisor: sum(
            1
            for h_value in range(-h_bound, h_bound + 1)
            if h_value != 0 and gcd(h_value, s) == divisor
        )
        for divisor in divisors
    }
    delta_multiple_counts = {
        divisor: 2 * (delta_bound // (s // divisor))
        for divisor in divisors
    }
    stratum_counts = {
        divisor: h_counts[divisor] * delta_multiple_counts[divisor]
        for divisor in divisors
    }
    direct_count = sum(
        1
        for h_value in range(-h_bound, h_bound + 1)
        if h_value != 0
        for delta_value in range(-delta_bound, delta_bound + 1)
        if delta_value != 0 and h_value * delta_value % s == 0
    )
    stratum_count_sum = sum(stratum_counts.values())
    reciprocal_modulus_bound = F(
        4 * len(divisors) * h_bound * delta_bound,
        s,
    )
    per_stratum_bounds = {
        divisor: (
            h_counts[divisor] <= F(2 * h_bound, divisor)
            and delta_multiple_counts[divisor]
            <= F(2 * delta_bound * divisor, s)
            and stratum_counts[divisor]
            <= F(4 * h_bound * delta_bound, s)
        )
        for divisor in divisors
    }
    return {
        "modulus": s,
        "h_radius": h_bound,
        "delta_radius": delta_bound,
        "divisor_count": len(divisors),
        "h_gcd_stratum_counts": h_counts,
        "delta_complement_multiple_counts": delta_multiple_counts,
        "gcd_stratum_pair_counts": stratum_counts,
        "direct_resonant_pair_count": direct_count,
        "gcd_stratum_count_sum": stratum_count_sum,
        "exact_gcd_stratum_count_identity": (
            direct_count == stratum_count_sum
        ),
        "per_stratum_reciprocal_modulus_bounds": per_stratum_bounds,
        "every_stratum_obeys_reciprocal_modulus_bound": all(
            per_stratum_bounds.values()
        ),
        "reciprocal_modulus_upper_bound": reciprocal_modulus_bound,
        "resonant_count_obeys_reciprocal_modulus_bound": (
            F(direct_count) <= reciprocal_modulus_bound
        ),
        "h_delta_product_structure_retained": True,
        "principal_afe_weighted_sum_bounded": False,
        "coupled_kernel_gate_closed": False,
    }


def principal_product_label_additive_master_audit(
    *,
    squarefree_moduli: tuple[int, ...],
    dyadic_modulus_lower: int,
    direct_coefficient: int,
    h_coefficients: dict[int, Fraction],
    delta_coefficients: dict[int, Fraction],
    type_base_coefficients: dict[int, Fraction],
    companion_type_coefficients: dict[int, Fraction],
) -> dict[str, object]:
    """Audit the finite unit-mask/Farey bound for the principal master.

    The returned identities retain ``mu(s)``, the Type factor ``mu(d)``,
    and the divisibility condition ``s | h*delta``.  They do not supply
    the packet-exhaustive physical AFE normalization or a bound for the
    nonprincipal double-centered dispersion.
    """

    moduli = tuple(int(value) for value in squarefree_moduli)
    scale = int(dyadic_modulus_lower)
    direct = int(direct_coefficient)
    if not moduli or scale <= 0:
        raise ValueError("a nonempty positive dyadic modulus block is required")
    if len(set(moduli)) != len(moduli):
        raise ValueError("the dyadic modulus block must not contain duplicates")
    if direct == 0:
        raise ValueError("the direct coefficient must be nonzero")
    for modulus in moduli:
        factors = _finite_prime_exponents(modulus) if modulus > 1 else {}
        if (
            modulus <= scale
            or modulus > 2 * scale
            or any(exponent != 1 for exponent in factors.values())
        ):
            raise ValueError("every modulus must be squarefree and in (S,2S]")
    if (
        not h_coefficients
        or not delta_coefficients
        or not type_base_coefficients
        or not companion_type_coefficients
    ):
        raise ValueError("all four coefficient families must be nonempty")
    if any(int(label) == 0 for label in (*h_coefficients, *delta_coefficients)):
        raise ValueError("the h and delta labels must be nonzero")
    if any(
        int(label) <= 0
        for label in (*type_base_coefficients, *companion_type_coefficients)
    ):
        raise ValueError("both Type coefficient families require positive labels")

    h_coeffs = {int(label): F(value) for label, value in h_coefficients.items()}
    delta_coeffs = {
        int(label): F(value) for label, value in delta_coefficients.items()
    }
    base_coeffs = {
        int(label): F(value) for label, value in type_base_coefficients.items()
    }
    companion_coeffs = {
        int(label): F(value)
        for label, value in companion_type_coefficients.items()
    }
    principal_weights = {
        modulus: sum(
            (
                h_coefficient * delta_coefficient
                for h_label, h_coefficient in h_coeffs.items()
                for delta_label, delta_coefficient in delta_coeffs.items()
                if h_label * delta_label % modulus == 0
            ),
            F(0),
        )
        for modulus in moduli
    }
    signed_modulus_weights = {
        modulus: _finite_mobius(modulus) * principal_weights[modulus]
        for modulus in moduli
    }

    product_coefficients: dict[int, Fraction] = {}
    for d, base_coefficient in base_coeffs.items():
        mobius_d = _finite_mobius(d)
        if mobius_d == 0:
            continue
        for p, companion_coefficient in companion_coeffs.items():
            product_coefficients[d * p] = product_coefficients.get(
                d * p,
                F(0),
            ) + mobius_d * base_coefficient * companion_coefficient
    product_coefficients = {
        label: value for label, value in product_coefficients.items() if value != 0
    }

    direct_master = 0j
    divisor_farey_expansion = 0j
    unit_mask_rows: dict[tuple[int, int], dict[str, object]] = {}
    for modulus in moduli:
        root = cmath.exp(2j * cmath.pi / modulus)
        signed_weight = signed_modulus_weights[modulus]
        for product_label, coefficient in product_coefficients.items():
            unit_indicator = int(gcd(product_label, modulus) == 1)
            mask_expansion = sum(
                _finite_mobius(divisor)
                for divisor in _positive_divisors(gcd(product_label, modulus))
            )
            unit_mask_rows[(modulus, product_label)] = {
                "unit_indicator": unit_indicator,
                "divisor_expansion": mask_expansion,
                "identity_holds": unit_indicator == mask_expansion,
            }
            direct_master += (
                signed_weight
                * coefficient
                * unit_indicator
                * root ** (direct * product_label % modulus)
            )
            for divisor in _positive_divisors(gcd(product_label, modulus)):
                quotient = modulus // divisor
                quotient_root = cmath.exp(2j * cmath.pi / quotient)
                divisor_farey_expansion += (
                    signed_weight
                    * _finite_mobius(divisor)
                    * coefficient
                    * quotient_root
                    ** (direct * (product_label // divisor) % quotient)
                )

    divisor_rows: list[dict[str, object]] = []
    repeated_modulus_weight_energy = F(0)
    farey_row_bound_sum = F(0)
    relevant_divisors = tuple(
        sorted(
            {
                divisor
                for modulus in moduli
                for divisor in _positive_divisors(modulus)
            }
        )
    )
    for divisor in relevant_divisors:
        quotient_pairs = tuple(
            (modulus, modulus // divisor)
            for modulus in moduli
            if modulus % divisor == 0
        )
        dilated_coefficients = {
            product_label // divisor: coefficient
            for product_label, coefficient in product_coefficients.items()
            if product_label % divisor == 0
        }
        coefficient_energy = sum(
            (value * value for value in dilated_coefficients.values()),
            F(0),
        )
        direct_gcd_groups: dict[int, list[tuple[int, int]]] = {}
        for modulus, quotient in quotient_pairs:
            direct_gcd_groups.setdefault(
                gcd(abs(direct), quotient),
                [],
            ).append((modulus, quotient))
        for direct_gcd, group in sorted(direct_gcd_groups.items()):
            quotient_moduli = tuple(quotient for _, quotient in group)
            reduced_quotient_moduli = tuple(
                quotient // direct_gcd for quotient in quotient_moduli
            )
            reduced_direct = direct // direct_gcd
            modulus_weight_energy = sum(
                (
                    signed_modulus_weights[modulus]
                    * signed_modulus_weights[modulus]
                    for modulus, _ in group
                ),
                F(0),
            )
            repeated_modulus_weight_energy += modulus_weight_energy
            if not dilated_coefficients:
                large_sieve_factor = F(0)
                direct_row_energy = 0.0
            else:
                frequencies = tuple(
                    F(reduced_direct % reduced_modulus, reduced_modulus)
                    if reduced_modulus > 1
                    else F(0)
                    for reduced_modulus in reduced_quotient_moduli
                )
                if len(frequencies) == 1:
                    inverse_spacing = F(1)
                else:
                    spacings = []
                    for first_position, first in enumerate(frequencies):
                        for second in frequencies[first_position + 1 :]:
                            difference = abs(first - second)
                            spacings.append(min(difference, 1 - difference))
                    minimum_spacing = min(spacings)
                    inverse_spacing = 1 / minimum_spacing
                interval_length = max(dilated_coefficients)
                large_sieve_factor = F(interval_length - 1) + inverse_spacing
                direct_row_energy = sum(
                    abs(
                        sum(
                            complex(coefficient)
                            * cmath.exp(
                                2j
                                * cmath.pi
                                * direct
                                * reduced_label
                                / quotient
                            )
                            for reduced_label, coefficient in dilated_coefficients.items()
                        )
                    )
                    ** 2
                    for quotient in quotient_moduli
                )
            farey_row_bound = large_sieve_factor * coefficient_energy
            farey_row_bound_sum += farey_row_bound
            divisor_rows.append(
                {
                    "divisor": divisor,
                    "direct_gcd": direct_gcd,
                    "reduced_direct_coefficient": reduced_direct,
                    "quotient_moduli": quotient_moduli,
                    "reduced_quotient_moduli": reduced_quotient_moduli,
                    "modulus_weight_l2_energy": modulus_weight_energy,
                    "dilated_product_coefficients": dilated_coefficients,
                    "dilated_coefficient_l2_energy": coefficient_energy,
                    "large_sieve_factor": large_sieve_factor,
                    "direct_farey_row_energy": direct_row_energy,
                    "farey_row_upper_bound": farey_row_bound,
                    "farey_row_bound_holds": (
                        direct_row_energy <= float(farey_row_bound) + 1e-8
                    ),
                }
            )

    finite_farey_upper_bound = (
        repeated_modulus_weight_energy * farey_row_bound_sum
    )
    direct_master_energy = abs(direct_master) ** 2
    type_product_energy = sum(
        (value * value for value in product_coefficients.values()),
        F(0),
    )
    base_energy = sum((value * value for value in base_coeffs.values()), F(0))
    companion_energy = sum(
        (value * value for value in companion_coeffs.values()),
        F(0),
    )
    maximum_product_divisor_count = max(
        (
            len(_positive_divisors(label))
            for label in product_coefficients
        ),
        default=0,
    )
    type_convolution_divisor_bound = (
        maximum_product_divisor_count * base_energy * companion_energy
    )
    product_pair_energy = sum(
        (
            h_coefficient
            * h_coefficient
            * delta_coefficient
            * delta_coefficient
            for h_coefficient in h_coeffs.values()
            for delta_coefficient in delta_coeffs.values()
        ),
        F(0),
    )
    principal_weight_cauchy_rows = {
        modulus: {
            "resonant_pair_count": sum(
                1
                for h_label in h_coeffs
                for delta_label in delta_coeffs
                if h_label * delta_label % modulus == 0
            ),
            "principal_weight_square": principal_weights[modulus]
            * principal_weights[modulus],
        }
        for modulus in moduli
    }
    for row in principal_weight_cauchy_rows.values():
        row["cauchy_upper_bound"] = (
            int(row["resonant_pair_count"]) * product_pair_energy
        )
        row["cauchy_bound_holds"] = (
            F(row["principal_weight_square"])
            <= F(row["cauchy_upper_bound"])
        )

    tolerance = 1e-7
    return {
        "squarefree_moduli": moduli,
        "dyadic_modulus_lower": scale,
        "direct_coefficient": direct,
        "principal_product_label_weights": principal_weights,
        "outer_signed_principal_weights": signed_modulus_weights,
        "type_product_convolution_coefficients": product_coefficients,
        "direct_principal_additive_master": direct_master,
        "unit_mask_divisor_farey_expansion": divisor_farey_expansion,
        "unit_mask_rows": unit_mask_rows,
        "all_unit_masks_equal_divisor_expansions": all(
            bool(row["identity_holds"]) for row in unit_mask_rows.values()
        ),
        "direct_principal_master_equals_divisor_farey_expansion": (
            abs(direct_master - divisor_farey_expansion) < tolerance
        ),
        "divisor_farey_rows": tuple(divisor_rows),
        "every_farey_row_bound_holds": all(
            bool(row["farey_row_bound_holds"]) for row in divisor_rows
        ),
        "repeated_modulus_weight_l2_energy": repeated_modulus_weight_energy,
        "farey_row_bound_sum": farey_row_bound_sum,
        "finite_farey_large_sieve_upper_bound": finite_farey_upper_bound,
        "finite_farey_large_sieve_bound_holds": (
            direct_master_energy <= float(finite_farey_upper_bound) + tolerance
        ),
        "type_product_convolution_l2_energy": type_product_energy,
        "type_convolution_divisor_bound": type_convolution_divisor_bound,
        "type_convolution_energy_obeys_divisor_bound": (
            type_product_energy <= type_convolution_divisor_bound
        ),
        "principal_weight_cauchy_rows": principal_weight_cauchy_rows,
        "all_principal_weight_cauchy_bounds_hold": all(
            bool(row["cauchy_bound_holds"])
            for row in principal_weight_cauchy_rows.values()
        ),
        "outer_mobius_weight_retained_linearly": True,
        "inner_type_mobius_weight_retained_linearly": True,
        "h_delta_product_structure_retained": True,
        "nonunit_direct_frequency_stratified_exactly": True,
        "full_afe_norm_adapter_proved": False,
        "principal_twisted_moment_contribution_in_target_proved": False,
        "nonprincipal_signed_dispersion_proved": False,
        "coupled_kernel_gate_closed": False,
    }


def sector_fourier_nonboundary_truncation_audit(
    *,
    sector_modulus: int,
    sector_frequency: int,
    residue_numerator: int,
    residue_modulus: int,
    harmonic_cutoff: int,
) -> dict[str, object]:
    """Audit the logarithmic-cost truncation of a nonboundary sector mode."""

    q = int(sector_modulus)
    xi = int(sector_frequency)
    w = int(residue_numerator)
    s = int(residue_modulus)
    cutoff = int(harmonic_cutoff)
    if q <= 1 or not 0 < xi < q:
        raise ValueError("the sector frequency must satisfy 0 < xi < Q")
    if s <= 1 or not 0 <= w < s or gcd(w, s) != 1:
        raise ValueError("w/s must be a reduced residue in [0,1)")
    if cutoff < 1:
        raise ValueError("the harmonic cutoff must be positive")
    remainder = (q * w) % s
    if remainder == 0:
        raise ValueError("the nonboundary audit excludes s dividing Q*w")

    x = F(w, s)
    sector_value = cmath.exp(
        2j * cmath.pi * xi * ((q * w) // s) / q
    )
    coefficients: dict[int, complex] = {}
    partial_sum = 0j
    for harmonic_index in range(-cutoff, cutoff + 1):
        direct = xi + harmonic_index * q
        coefficient = (
            q
            * (1 - cmath.exp(-2j * cmath.pi * xi / q))
            / (2j * cmath.pi * direct)
        )
        coefficients[harmonic_index] = coefficient
        partial_sum += coefficient * cmath.exp(
            2j * cmath.pi * direct * float(x)
        )

    circular_distance = F(min(remainder, s - remainder), s)
    power_tail_bound = 1 / (cutoff * float(circular_distance))
    truncation_error = abs(sector_value - partial_sum)
    coefficient_l1 = sum(abs(value) for value in coefficients.values())
    logarithmic_l1_bound = 2 + 2 * (1 + log(cutoff + 1)) / pi
    direct_coefficients = tuple(
        xi + harmonic_index * q
        for harmonic_index in range(-cutoff, cutoff + 1)
    )
    tolerance = 1e-10
    return {
        "sector_modulus": q,
        "sector_frequency": xi,
        "residue_fraction": x,
        "nonboundary": True,
        "circular_boundary_distance": circular_distance,
        "harmonic_cutoff": cutoff,
        "continuous_harmonic_coefficients": coefficients,
        "finite_harmonic_sum": partial_sum,
        "exact_sector_value": sector_value,
        "truncation_error": truncation_error,
        "power_tail_upper_bound": power_tail_bound,
        "truncation_error_obeys_power_tail": (
            truncation_error <= power_tail_bound + tolerance
        ),
        "coefficient_l1_norm": coefficient_l1,
        "logarithmic_l1_upper_bound": logarithmic_l1_bound,
        "coefficient_l1_obeys_logarithmic_bound": (
            coefficient_l1 <= logarithmic_l1_bound + tolerance
        ),
        "minimum_direct_coefficient": min(direct_coefficients),
        "maximum_direct_coefficient": max(abs(value) for value in direct_coefficients),
        "all_direct_coefficients_nonzero": all(
            value != 0 for value in direct_coefficients
        ),
        "harmonic_projective_cost_is_logarithmic": True,
        "nonunit_farey_stratification_available": True,
        "physical_principal_norm_adapter_proved": False,
        "coupled_kernel_gate_closed": False,
    }


def sector_harmonic_farey_operator_audit(
    *,
    squarefree_moduli: tuple[int, ...],
    dyadic_modulus_lower: int,
    sector_modulus: int,
    harmonic_cutoff: int,
    reduced_fraction_coefficients: dict[tuple[int, int], Fraction],
) -> dict[str, object]:
    """Audit the normalized sector-harmonic large-sieve operator."""

    moduli = tuple(int(value) for value in squarefree_moduli)
    scale = int(dyadic_modulus_lower)
    q = int(sector_modulus)
    cutoff = int(harmonic_cutoff)
    if not moduli or scale <= 0 or len(set(moduli)) != len(moduli):
        raise ValueError("a distinct nonempty dyadic modulus block is required")
    for modulus in moduli:
        factors = _finite_prime_exponents(modulus) if modulus > 1 else {}
        if (
            modulus <= scale
            or modulus > 2 * scale
            or any(exponent != 1 for exponent in factors.values())
        ):
            raise ValueError("every modulus must be squarefree and in (S,2S]")
    if q <= 1 or cutoff < 1:
        raise ValueError("Q and the harmonic cutoff must be positive")
    if not reduced_fraction_coefficients:
        raise ValueError("at least one reduced Farey coefficient is required")

    farey_coefficients: dict[tuple[int, int], Fraction] = {}
    farey_points: list[Fraction] = []
    for (modulus, numerator), coefficient in reduced_fraction_coefficients.items():
        modulus = int(modulus)
        numerator = int(numerator)
        if (
            modulus not in moduli
            or not 0 < numerator < modulus
            or gcd(numerator, modulus) != 1
        ):
            raise ValueError("every label must be a reduced t/s in the block")
        farey_coefficients[(modulus, numerator)] = F(coefficient)
        farey_points.append(F(numerator, modulus))
    distinct_farey_points = len(set(farey_points)) == len(farey_points)
    if not distinct_farey_points:
        raise ValueError("the reduced Farey points must be distinct")

    coefficient_energy = sum(
        (coefficient * coefficient for coefficient in farey_coefficients.values()),
        F(0),
    )

    def harmonic_coefficient(xi: int, harmonic_index: int) -> complex:
        direct = xi + harmonic_index * q
        return (
            q
            * (1 - cmath.exp(-2j * cmath.pi * xi / q))
            / (2j * cmath.pi * direct)
        )

    def direct_transform(direct: int) -> complex:
        return sum(
            complex(coefficient)
            * cmath.exp(2j * cmath.pi * direct * numerator / modulus)
            for (modulus, numerator), coefficient in farey_coefficients.items()
        )

    harmonic_labels = tuple(
        (xi, harmonic_index, xi + harmonic_index * q)
        for xi in range(1, q)
        for harmonic_index in range(-cutoff, cutoff + 1)
    )
    direct_labels = tuple(label[2] for label in harmonic_labels)
    direct_transforms = {
        direct: direct_transform(direct) for direct in direct_labels
    }
    sector_rows = {
        xi: sum(
            harmonic_coefficient(xi, harmonic_index)
            * direct_transforms[xi + harmonic_index * q]
            for harmonic_index in range(-cutoff, cutoff + 1)
        )
        for xi in range(1, q)
    }
    normalized_sector_energy = sum(
        abs(value) ** 2 for value in sector_rows.values()
    ) / q
    maximum_harmonic_l1 = max(
        sum(
            abs(harmonic_coefficient(xi, harmonic_index))
            for harmonic_index in range(-cutoff, cutoff + 1)
        )
        for xi in range(1, q)
    )

    harmonic_blocks: list[tuple[int, ...]] = [(-1, 0)]
    positive_start = 1
    while positive_start <= cutoff:
        positive_end = min(2 * positive_start - 1, cutoff)
        harmonic_blocks.append(tuple(range(positive_start, positive_end + 1)))
        positive_start *= 2
    negative_start = 2
    while negative_start <= cutoff:
        negative_end = min(2 * negative_start - 1, cutoff)
        harmonic_blocks.append(
            tuple(-index for index in range(negative_start, negative_end + 1))
        )
        negative_start *= 2

    block_rows: list[dict[str, object]] = []
    weighted_direct_sum = 0.0
    weighted_large_sieve_upper_sum = 0.0
    inverse_spacing_ceiling = 4 * scale * scale
    for harmonic_block in harmonic_blocks:
        labels = tuple(
            (xi, harmonic_index, xi + harmonic_index * q)
            for xi in range(1, q)
            for harmonic_index in harmonic_block
        )
        weights = tuple(
            abs(harmonic_coefficient(xi, harmonic_index))
            for xi, harmonic_index, _ in labels
        )
        block_direct_labels = tuple(direct for _, _, direct in labels)
        interval_length = max(block_direct_labels) - min(block_direct_labels) + 1
        maximum_weight = max(weights)
        direct_weighted_energy = sum(
            weight * abs(direct_transforms[direct]) ** 2
            for weight, direct in zip(weights, block_direct_labels, strict=True)
        )
        large_sieve_upper_bound = float(
            F(interval_length - 1 + inverse_spacing_ceiling)
            * coefficient_energy
        )
        weighted_upper_bound = maximum_weight * large_sieve_upper_bound
        weighted_direct_sum += direct_weighted_energy
        weighted_large_sieve_upper_sum += weighted_upper_bound
        block_rows.append(
            {
                "harmonic_indices": harmonic_block,
                "direct_frequency_interval_length": interval_length,
                "maximum_harmonic_weight": maximum_weight,
                "direct_weighted_energy": direct_weighted_energy,
                "weighted_large_sieve_upper_bound": weighted_upper_bound,
                "bound_holds": (
                    direct_weighted_energy <= weighted_upper_bound + 1e-8
                ),
            }
        )

    cauchy_intermediate = maximum_harmonic_l1 * weighted_direct_sum / q
    operator_upper_bound = (
        maximum_harmonic_l1 * weighted_large_sieve_upper_sum / q
    )
    return {
        "squarefree_moduli": moduli,
        "dyadic_modulus_lower": scale,
        "sector_modulus": q,
        "harmonic_cutoff": cutoff,
        "reduced_fraction_coefficients": farey_coefficients,
        "reduced_farey_points_are_distinct": distinct_farey_points,
        "harmonic_labels_are_globally_unique": (
            len(set(direct_labels)) == len(direct_labels)
        ),
        "coefficient_l2_energy": coefficient_energy,
        "maximum_harmonic_l1_norm": maximum_harmonic_l1,
        "sector_rows": sector_rows,
        "normalized_sector_energy": normalized_sector_energy,
        "weighted_direct_frequency_energy": weighted_direct_sum,
        "cauchy_intermediate_upper_bound": cauchy_intermediate,
        "harmonic_blocks": tuple(block_rows),
        "weighted_block_large_sieve_bound_holds": all(
            bool(row["bound_holds"]) for row in block_rows
        ),
        "operator_upper_bound": operator_upper_bound,
        "normalized_sector_energy_obeys_operator_bound": (
            normalized_sector_energy <= operator_upper_bound + 1e-8
            and normalized_sector_energy <= cauchy_intermediate + 1e-8
        ),
        "frequency_normalization_gain_recorded": True,
        "fixed_coefficient_operator_proved": True,
        "physical_sector_support_condition_holds": all(
            modulus <= q for modulus in moduli
        ),
        "original_long_modulus_principal_adapter_proved": False,
        "physical_coefficient_energy_target_proved": False,
        "coupled_kernel_gate_closed": False,
    }


def squarefree_prime_factor_transfer_audit(
    *,
    modulus_exponent: Fraction,
    prime_factor_exponent: Fraction,
    prime_relative_saving_exponent: Fraction,
    required_unsquared_saving: Fraction,
) -> dict[str, object]:
    """Audit the cost of transferring a prime trace bound through CRT.

    If ``s=q*r``, a prime-modulus theorem saving ``q^(-kappa)``
    contributes ``T^(-lambda*kappa)`` when ``q=T^lambda``.  Separating
    the cofactor kernel by multiplicative Fourier inversion costs at
    most ``phi(r)^(1/2)``, i.e. ``T^((sigma-lambda)/2)``.  The transfer
    therefore saves a power only when

    ``lambda > sigma/(1+2*kappa)``.

    This is a pointwise diagnostic only; it provides no outer modulus,
    sector, or ``h*delta`` moment.
    """

    sigma = F(modulus_exponent)
    prime = F(prime_factor_exponent)
    kappa = F(prime_relative_saving_exponent)
    required = F(required_unsquared_saving)
    if sigma <= 0:
        raise ValueError("modulus_exponent must be positive")
    if prime < 0 or prime > sigma:
        raise ValueError("prime factor exponent must lie in [0,sigma]")
    if kappa < 0 or required < 0:
        raise ValueError("saving exponents must be nonnegative")

    prime_saving = prime * kappa
    cofactor_cost = (sigma - prime) / 2
    signed_net = prime_saving - cofactor_cost
    net = max(F(0), signed_net)
    threshold = sigma / (1 + 2 * kappa) if kappa > 0 else sigma
    return {
        "modulus_exponent": sigma,
        "prime_factor_exponent": prime,
        "cofactor_exponent": sigma - prime,
        "prime_relative_saving_exponent": kappa,
        "prime_bound_saving_in_T_exponent": prime_saving,
        "cofactor_character_l1_cost_exponent": cofactor_cost,
        "signed_net_transfer_saving_exponent": signed_net,
        "net_transfer_saving_exponent": net,
        "large_prime_threshold_exponent": threshold,
        "strict_power_saving_after_transfer": signed_net > 0,
        "required_unsquared_saving": required,
        "remaining_unsquared_deficit": max(F(0), required - net),
        "pointwise_transfer_meets_required_saving": net >= required,
        "transfer_closes_coupled_gate": False,
        "multiplicative_character_twist_preserves_l2_coefficients": True,
        "both_mobius_weights_retained": True,
        "h_delta_factor_retained": True,
        "outer_modulus_average_provided": False,
        "joint_sector_character_moment_provided": False,
        "joint_h_delta_moment_provided": False,
    }


def squarefree_prime_factor_polytope_audit(
    *,
    modulus_exponent: Fraction,
    prime_factor_exponents: tuple[Fraction, ...],
    prime_relative_saving_exponent: Fraction,
    required_unsquared_saving: Fraction,
) -> dict[str, object]:
    """Optimize one-prime CRT transfer over a squarefree factorization.

    Each factor ``q_i=T^(lambda_i)`` can be selected as the prime
    modulus and the product of the other factors as its cofactor.  This
    helper evaluates every such choice using

    ``kappa*lambda_i-(sigma-lambda_i)/2``

    and records the best pointwise transfer.  On the continuous
    polytope ``sum lambda_i=sigma``, the supremum is only
    ``kappa*sigma``, approached when one prime factor carries the whole
    modulus.  Thus a fixed-prime theorem with ``kappa<1/2`` cannot by
    itself supply a half-power global saving even in that limiting
    corner.
    """

    sigma = F(modulus_exponent)
    factors = tuple(F(value) for value in prime_factor_exponents)
    kappa = F(prime_relative_saving_exponent)
    required = F(required_unsquared_saving)
    if sigma <= 0 or not factors or any(value <= 0 for value in factors):
        raise ValueError("modulus and prime-factor exponents must be positive")
    if sum(factors, F(0)) != sigma:
        raise ValueError("prime-factor exponents must sum to the modulus exponent")
    if kappa < 0 or required < 0:
        raise ValueError("saving exponents must be nonnegative")

    signed_savings = tuple(
        kappa * value - (sigma - value) / 2 for value in factors
    )
    net_savings = tuple(max(F(0), value) for value in signed_savings)
    best_index = max(range(len(factors)), key=net_savings.__getitem__)
    best_net = net_savings[best_index]
    continuous_supremum = kappa * sigma
    return {
        "modulus_exponent": sigma,
        "prime_factor_exponents": factors,
        "prime_relative_saving_exponent": kappa,
        "signed_transfer_savings": signed_savings,
        "net_transfer_savings": net_savings,
        "best_prime_factor_index": best_index,
        "best_prime_factor_exponent": factors[best_index],
        "best_net_transfer_saving": best_net,
        "continuous_polytope_supremum": continuous_supremum,
        "finite_nontrivial_factorization_is_below_supremum": (
            best_net < continuous_supremum if len(factors) > 1 else False
        ),
        "required_unsquared_saving": required,
        "remaining_unsquared_deficit": max(F(0), required - best_net),
        "continuous_pointwise_supremum_meets_required_saving": (
            continuous_supremum >= required
        ),
        "selected_pointwise_factor_meets_required_saving": (
            best_net >= required
        ),
        "transfer_closes_coupled_gate": False,
        "only_extreme_large_prime_subface_can_save_power": all(
            signed <= 0
            for exponent, signed in zip(factors, signed_savings)
            if exponent <= sigma / (1 + 2 * kappa)
        ),
        "outer_modulus_average_provided": False,
        "joint_character_moment_provided": False,
        "joint_h_delta_moment_provided": False,
    }


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


def published_mobius_fourth_moment_coverage_audit(
    *,
    target_length_exponent: Fraction,
) -> PublishedMobiusFourthMomentCoverageAudit:
    """Audit two recent moment results against the top DCV gate.

    The target is the normalized multiplicative Dirichlet polynomial

    ``sum_{n asymp T} mu(n) U(n/T) n^(-1/2-it)``

    at physical height ``T``.  Its required pure fourth moment has exponent
    one.  Bui--Hall--Subira Jorge Theorem 1.1 instead treats the fourth power
    of an amplifier inside a zeta fourth moment, with divisor coefficients
    and strict length hypothesis ``vartheta < 1/8``.  All three interfaces
    (length, coefficient class, and integrand) must match before it can be
    counted as direct coverage.

    Verjovsky Theorem 4.1 concerns the additive Fourier polynomial
    ``N^(-1/2) sum_{n<=N} mu(n)e(nt)`` on arcs of radius ``c/N``.  The
    subpolynomial local-moment assertion is equivalent to RH there, so it is
    diagnostic rather than an unconditional estimate for the multiplicative
    height aspect gate.
    """
    target_length = F(target_length_exponent)
    if target_length < 0:
        raise ValueError("target length exponent must be nonnegative")

    bhsj_ceiling = F(1, 8)
    bhsj_length_ok = target_length < bhsj_ceiling
    bhsj_coefficient_match = False
    bhsj_integrand_match = False
    bhsj_coverage = (
        bhsj_length_ok
        and bhsj_coefficient_match
        and bhsj_integrand_match
    )
    verjovsky_unconditional = False
    return PublishedMobiusFourthMomentCoverageAudit(
        target_length_exponent=target_length,
        target_height_exponent=F(1),
        target_normalized_moment_exponent=F(1),
        bhsj_amplifier_length_ceiling=bhsj_ceiling,
        bhsj_length_power_deficit=max(F(0), target_length - bhsj_ceiling),
        bhsj_length_hypothesis_met=bhsj_length_ok,
        bhsj_mobius_coefficient_class_matches=bhsj_coefficient_match,
        bhsj_pure_fourth_moment_integrand_matches=bhsj_integrand_match,
        bhsj_direct_coverage=bhsj_coverage,
        verjovsky_polynomial_is_additive_fourier=True,
        verjovsky_polynomial_is_multiplicative_dirichlet=False,
        verjovsky_local_arc_exponent=F(-1),
        verjovsky_subpolynomial_moment_bound_equivalent_to_rh=True,
        verjovsky_unconditional_coverage=verjovsky_unconditional,
        direct_published_coverage=(bhsj_coverage or verjovsky_unconditional),
        bhsj_source=(
            "Bui--Hall--Subira Jorge, arXiv:2511.14415v1, "
            "Theorem 1.1 and its amplifier definition."
        ),
        verjovsky_source=(
            "Verjovsky, arXiv:2607.25002v1, Theorem 4.1."
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


def transition_kim_ternary_correlation_audit(
    *,
    ambient_length_exponent: Fraction,
    shift_length_exponent: Fraction,
    target_exponent: Fraction,
) -> TransitionKimTernaryCorrelationAudit:
    """Audit Kim 2026 Theorem 1.6 on the balanced shifted packet.

    In the theorem's ``alpha=0`` case, a shift ``H=X**eta`` must satisfy
    ``eta > 1/2 + 100*epsilon`` and the error saves ``H**(epsilon/2)``.
    The returned epsilon and saving are unattained ceilings because the
    theorem has a strict buffer.  Independently, a Möbius coefficient has
    associated series ``1/L(s,chi)`` and fails the theorem's holomorphy and
    critical-line second-moment hypotheses.  The actual dyadic convolutions
    also are not one fixed multiplicative function.
    """

    x = F(ambient_length_exponent)
    h = F(shift_length_exponent)
    target = F(target_exponent)
    if x <= 0 or h <= 0 or h >= x:
        raise ValueError("require positive shift exponent below ambient length")
    ambient = x + h
    if target > ambient:
        raise ValueError("target cannot exceed the ambient sum exponent")
    eta = h / x
    floor = F(1, 2)
    buffer = 100
    epsilon_ceiling = max(F(0), (eta - floor) / buffer)
    saving_ceiling = h * epsilon_ceiling / 2
    required = ambient - target
    residual = max(F(0), required - saving_ceiling)
    return TransitionKimTernaryCorrelationAudit(
        ambient_length_exponent=x,
        shift_length_exponent=h,
        target_exponent=target,
        relative_shift_exponent=eta,
        theorem_alpha_zero_shift_floor=floor,
        theorem_buffer_multiplier=buffer,
        theorem_epsilon_ceiling=epsilon_ceiling,
        ambient_sum_exponent=ambient,
        required_saving_exponent=required,
        theorem_saving_ceiling=saving_ceiling,
        residual_power_deficit=residual,
        mobius_dirichlet_series_is_reciprocal_l=True,
        mobius_holomorphic_halfplane_hypothesis=False,
        mobius_critical_line_second_moment_hypothesis=False,
        dyadic_convolution_is_one_multiplicative_function=False,
        theorem_applies_to_actual_packet=False,
        whole_line_family_covered=False,
        source=(
            "Jiseong Kim, arXiv:2603.23250v2, Definition 1.1 and "
            "Theorem 1.6."
        ),
    )


def transition_doyle_kfree_moment_audit(
    *,
    product_center_exponent: Fraction,
    short_interval_exponent: Fraction,
) -> TransitionDoyleKFreeMomentAudit:
    """Audit Doyle 2026 on the balanced short-interval variance gate.

    Doyle's ``k=2`` middle-part exponent is ``105/317``.  Theorem 1.7
    therefore gives its Möbius ``L1`` *lower* bound for intervals longer
    than ``N**(315/634+epsilon)``.  This enters the balanced interval
    ``K=N**(1/2)``, but neither its conclusion nor its square-divisor
    coefficient is the upper variance estimate for the two-Möbius
    convolution required by the actual packet.
    """

    x = F(product_center_exponent)
    k = F(short_interval_exponent)
    if x <= 0 or k <= 0 or k > x:
        raise ValueError("require a positive short interval no longer than its center")
    relative = k / x
    delta_two = F(105, 317)
    threshold = F(3, 2) * delta_two
    margin = max(F(0), relative - threshold)
    return TransitionDoyleKFreeMomentAudit(
        product_center_exponent=x,
        short_interval_exponent=k,
        relative_interval_exponent=relative,
        k_two_middle_part_exponent=delta_two,
        mobius_l1_threshold_exponent=threshold,
        length_margin_exponent=margin,
        theorem_is_l1_lower_bound=True,
        theorem_is_variance_upper_bound=False,
        middle_coefficient_uses_square_divisors=True,
        middle_coefficient_matches_balanced_two_mobius_convolution=False,
        theorem_applies_to_actual_packet=False,
        whole_line_family_covered=False,
        source=(
            "Ben Doyle, arXiv:2608.16679v1, Lemma 1.2, Theorem 1.7, "
            "and Corollary 1.8."
        ),
    )


def transition_shi_bessel_kuznetsov_audit(
    *,
    first_fourier_index: int,
    second_fourier_index: int,
) -> TransitionShiBesselKuznetsovAudit:
    """Audit Shi 2026 against the exact determinant Kloosterman orbit.

    The classical nondegenerate Kuznetsov Bessel argument is proportional
    to ``sqrt(abs(m1*m2))/c``.  The exact orbit found in Section 4.16 is
    ``S(0,-h;delta;s)``, hence that argument is zero.  Shi's phase-transition
    theorem instead assumes a smooth weight on a positive dyadic Bessel-
    argument interval and a separately identified linear twist.  It cannot
    be applied to this degenerate Ramanujan/Eisenstein orbit.
    """

    m2 = int(first_fourier_index)
    m1 = int(second_fourier_index)
    if m1 == 0 and m2 == 0:
        raise ValueError("at least one Fourier index must be nonzero")
    argument_is_zero = m1 * m2 == 0
    actual_linear_twist_identified = False
    nondegenerate_adapter = False
    applies = (
        not argument_is_zero
        and actual_linear_twist_identified
        and nondegenerate_adapter
    )
    return TransitionShiBesselKuznetsovAudit(
        exact_orbit_first_fourier_index=m2,
        exact_orbit_second_fourier_index=m1,
        bessel_argument_is_zero=argument_is_zero,
        paper_requires_positive_dyadic_bessel_argument=True,
        paper_linear_twist_identified_in_actual_orbit=(
            actual_linear_twist_identified
        ),
        classical_nondegenerate_kuznetsov_adapter_verified=nondegenerate_adapter,
        subcritical_rapid_decay_applies=applies,
        whole_line_family_covered=False,
        source="Yuhang Shi, arXiv:2608.13232v1, Theorem 1.1.",
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
        "pascadi_uniform=1/700,pascadi_uniform_deficit=349/700,"
        "pascadi_one_bounded=1/276,pascadi_one_bounded_deficit=137/276,"
        "pascadi_factorable=1/12,pascadi_factorable_deficit=5/12,"
        "pascadi_average_q=0,pascadi_average_save=0,four_bp=1/8,"
        "four_bp_deficit=3/8,sqrt_range=True,arbitrary=True,"
        "kernel=False,separable=False,fixed_modulus=False,"
        "pascadi_uniform=True,primitive_q_one=True,"
        "pascadi_average_power=False,covered=False"
    )
    unit_divisor_shifted_prime = (
        farey_type_i_unit_divisor_shifted_prime_reassembly(
            q=11,
            sector_character=3,
            denominators=tuple(range(2, 12)),
            h=2,
            delta=-3,
            packet_label="afe-plus",
        )
    )
    print(
        "large_q_transition: unit_divisor_shifted_prime="
        f"entries={len(unit_divisor_shifted_prime['unit_divisor_entries'])},"
        "exact="
        f"{unit_divisor_shifted_prime['shifted_prime_reassembly_exact']},"
        "shift_identity="
        f"{unit_divisor_shifted_prime['mobius_is_negative_prime_shift_exact']},"
        "shift_one_sectors="
        + ",".join(
            str(label)
            for label in unit_divisor_shifted_prime[
                "shift_one_sector_labels"
            ]
        )
        + ",phase_varies="
        f"{unit_divisor_shifted_prime['sector_phase_varies_after_fixing_shift']},"
        "fixed_weight="
        f"{unit_divisor_shifted_prime['lichtman_fixed_weight_hypothesis_matched']},"
        "proved="
        f"{unit_divisor_shifted_prime['type_i_estimate_proved']}"
    )
    lichtman_type_i = lichtman_shifted_prime_type_i_coverage_audit(
        prime_length_exponent=F(1),
        shift_length_exponent=F(1),
        required_unsquared_saving_exponent=F(1, 2),
    )
    print(
        "large_q_transition: lichtman_type_i="
        "norm=L1_over_shifts,required=vector_cluster_L2,"
        "log_sup="
        f"{_fmt(lichtman_type_i['published_log_saving_exponent_supremum'])},"
        "power="
        f"{_fmt(lichtman_type_i['published_power_saving_exponent'])},"
        "deficit="
        f"{_fmt(lichtman_type_i['remaining_power_deficit'])},"
        "H_lt_X="
        f"{lichtman_type_i['strict_shift_range_h_less_x']},"
        "fixed_weight="
        f"{lichtman_type_i['fixed_weight_across_shifts']},"
        "norm_match="
        f"{lichtman_type_i['norm_hypothesis_matched']},"
        f"covered={lichtman_type_i['covers_type_i_gate']}"
    )
    beatty_grid_alias = technau_zafeiropoulos_grid_coverage_audit(
        value_length_exponent=F(1),
        fourier_truncation_exponent=F(1, 2),
        slope_grid_exponent=F(1),
        coefficient_l2_energy_exponent=F(1),
        target_energy_exponent=F(2),
    )
    print(
        "large_q_transition: beatty_grid_alias="
        "bandwidth="
        f"{_fmt(beatty_grid_alias['trigonometric_bandwidth_exponent'])},"
        f"grid={_fmt(beatty_grid_alias['slope_grid_exponent'])},"
        "alias="
        f"{_fmt(beatty_grid_alias['alias_multiplicity_exponent'])},"
        "continuous="
        f"{_fmt(beatty_grid_alias['continuous_slope_total_energy_exponent'])},"
        "sampled="
        f"{_fmt(beatty_grid_alias['generic_sampled_energy_exponent'])},"
        f"target={_fmt(beatty_grid_alias['target_energy_exponent'])},"
        "deficit="
        f"{_fmt(beatty_grid_alias['remaining_energy_deficit'])},"
        "continuous_metric="
        f"{beatty_grid_alias['continuous_metric_l2_reaches_target']},"
        f"second_mu={beatty_grid_alias['second_index_mobius_supported']},"
        "fixed_f="
        f"{beatty_grid_alias['fixed_arithmetic_function_across_slopes_supported']},"
        "collision="
        f"{beatty_grid_alias['finite_fixed_f_collision_exhibited']},"
        "afe_interlaces="
        f"{beatty_grid_alias['afe_product_frequency_interlaces_sector_grid']},"
        "adapter="
        f"{beatty_grid_alias['type_packet_fourier_adapter_constructed']},"
        "alias_gate="
        f"{beatty_grid_alias['structured_nonzero_alias_cancellation_required']},"
        f"covered={beatty_grid_alias['covers_coupled_type_gate']}"
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
        "zero_proved=False,whole=False"
    )
    transition_resonant_gram = transition_poisson_resonant_gram_audit()
    print(
        "large_q_transition: poisson_resonant_gram="
        f"discrete_diag={_fmt(transition_resonant_gram.discrete_identity_diagonal_exponent)},"
        f"continuous_diag={_fmt(transition_resonant_gram.continuous_self_gram_exponent)},"
        f"sampling={_fmt(transition_resonant_gram.sampling_correction_bound_exponent)},"
        "sampling_deficit=0,continuous_gram=3,target=2,required=1,"
        "jacobian=True,offdiag_sign_indefinite=True,recombination=True,"
        "sampling_power_obstruction=False,endpoint_logs=False,"
        "gram_proved=False,whole=False"
    )
    transition_tube_cluster = transition_poisson_tube_cluster_audit()
    print(
        "large_q_transition: poisson_tube_cluster="
        "length=1/2,width=-1/2,angular_resolution=-1,directions=2,"
        "clusters=1,per_cluster=1,coherent_energy=3,sqrt_energy=2,"
        "target=2,margin=0,coefficient=mu(s)*mu(k*s+w),"
        "same_cluster_implies_collar=True,collar_implies_adjacent=True,"
        "cluster_multiplicity=3,beatty_fiber=True,mobius_product_fold=True,"
        "vector_kernel_blocks_scalar_fold=True,additive_fourier=True,"
        "additive_local_moment_unconditional=False,two_mobius=True,"
        "sector_parseval=True,sector_principal_absorbed=True,"
        "remaining_sector_characters=nonzero,"
        "single_mobius_type_identity=True,automatic_frequency_decay=False,"
        "pre_cauchy_dispersion=True,type_bound_proved=False,"
        f"farey_matches={transition_tube_cluster.unweighted_farey_equidistribution_matches},"
        "nilsequence_matches=False,covered=False"
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
    published_fourth_moment = published_mobius_fourth_moment_coverage_audit(
        target_length_exponent=F(1),
    )
    print(
        "large_q_transition: published_mobius_fourth_moment="
        f"target_length={_fmt(published_fourth_moment.target_length_exponent)},"
        f"target_height={_fmt(published_fourth_moment.target_height_exponent)},"
        "target_moment=1,"
        "bhsj_ceiling=1/8,bhsj_deficit=7/8,bhsj_length=False,"
        "bhsj_mobius=False,bhsj_pure_integrand=False,bhsj_covered=False,"
        "verjovsky_additive=True,verjovsky_multiplicative=False,"
        "verjovsky_arc=-1,verjovsky_rh_equivalent=True,"
        "verjovsky_unconditional=False,covered=False"
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
    kim_ternary = transition_kim_ternary_correlation_audit(
        ambient_length_exponent=F(3),
        shift_length_exponent=F(2),
        target_exponent=F(9, 2),
    )
    print(
        "large_q_transition: kim_2026_ternary="
        f"X={_fmt(kim_ternary.ambient_length_exponent)},"
        f"H={_fmt(kim_ternary.shift_length_exponent)},"
        f"eta={_fmt(kim_ternary.relative_shift_exponent)},"
        f"epsilon_ceiling={_fmt(kim_ternary.theorem_epsilon_ceiling)},"
        f"ambient={_fmt(kim_ternary.ambient_sum_exponent)},"
        f"required={_fmt(kim_ternary.required_saving_exponent)},"
        f"saving_ceiling={_fmt(kim_ternary.theorem_saving_ceiling)},"
        f"deficit={_fmt(kim_ternary.residual_power_deficit)},"
        "reciprocal_l=True,holomorphic=False,critical_l2=False,"
        "dyadic_multiplicative=False,applicable=False,covered=False"
    )
    doyle_kfree = transition_doyle_kfree_moment_audit(
        product_center_exponent=F(2),
        short_interval_exponent=F(1),
    )
    print(
        "large_q_transition: doyle_2026_kfree="
        f"N={_fmt(doyle_kfree.product_center_exponent)},"
        f"K={_fmt(doyle_kfree.short_interval_exponent)},"
        f"relative={_fmt(doyle_kfree.relative_interval_exponent)},"
        f"delta2={_fmt(doyle_kfree.k_two_middle_part_exponent)},"
        f"l1_threshold={_fmt(doyle_kfree.mobius_l1_threshold_exponent)},"
        f"length_margin={_fmt(doyle_kfree.length_margin_exponent)},"
        "l1_lower=True,variance_upper=False,square_divisors=True,"
        "balanced_two_mobius=False,applicable=False,covered=False"
    )
    shi_bessel = transition_shi_bessel_kuznetsov_audit(
        first_fourier_index=0,
        second_fourier_index=-1,
    )
    print(
        "large_q_transition: shi_2026_bessel_kuznetsov="
        f"m2={shi_bessel.exact_orbit_first_fourier_index},"
        f"m1={shi_bessel.exact_orbit_second_fourier_index},"
        "bessel_argument_zero=True,positive_dyadic_required=True,"
        "actual_linear_twist=False,nondegenerate_adapter=False,"
        "subcritical_decay=False,covered=False"
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
