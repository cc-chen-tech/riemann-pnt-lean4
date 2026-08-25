#!/usr/bin/env python3
"""Exact-rational adapters for published MWKF core estimates.

The adapters only certify a route when every encoded hypothesis and the
fixed target saving hold.  A rejected result is a coverage witness, not a
claim that the corresponding theorem is false.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
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


if __name__ == "__main__":
    main()
