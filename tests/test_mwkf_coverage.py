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
        "proved=False k_mu=False"
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
    ):
        assert marker in text
