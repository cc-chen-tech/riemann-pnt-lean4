"""A local/logarithmic ledger must not certify missing physical estimates."""

from fractions import Fraction as F
from pathlib import Path
import sys

import pytest

sys.path.insert(0, str(Path(__file__).parents[1]))
from scripts import audit_mwkf_coverage as audit


def test_local_poisson_identity_does_not_certify_full_weight_embedding():
    result = audit.independent_cubic_closure_verification_audit()
    assert result.c_poisson_jacobian == "A/(r*n)"
    assert result.c_poisson_phase == "e(-j*A*k*l/(r*n))"
    assert result.weighted_partial_summation_verified
    assert not result.c_poisson_full_weight_embedding_verified
    assert not result.all_four_independent_gates_verified


def test_distinct_mechanism_names_do_not_prove_a_disjoint_physical_partition():
    result = audit.independent_cubic_closure_verification_audit()
    assert not result.compact_and_tail_partition_is_disjoint
    assert not result.every_cancellation_source_is_used_once


@pytest.mark.parametrize("log_start", [F(100), F(10**6)])
def test_arbitrarily_large_log_saving_does_not_pay_outer_power_loss(log_start):
    result = audit.mwkf_tail_shell_aggregation_audit(
        tail_log_start=log_start,
        seminorm_decay_order=F(4),
        local_seminorm_log_loss=F(20),
        target_log_saving=F(20),
    )
    assert result.net_tail_log_saving > 20
    assert result.pevp_is_polynomial_in_fixed_kernel_seminorms
    assert not result.transform_tail_aggregated
    assert not result.afe_tail_aggregated
    assert not result.total_tail_is_little_o_T


def test_default_final_report_retains_physical_normalization_and_outer_gaps():
    result = audit.unconditional_long_mollifier_asymptotic_audit()
    assert not result.unconditional_asymptotic_proved
    assert not result.full_remainder_is_little_o_T
    assert not result.physical_weight_ledger_verified
    assert not result.compact_nonzero_poisson_core_is_little_o_T
    assert result.residual_cell_count >= 3
    assert {
        "short_cofactor_HL_normalization",
        "full_outer_PEVP_aggregation",
        "physical_tail_partition_and_bounds",
    } <= set(result.residual_top_level_gates)


@pytest.mark.parametrize("u,a,total", [(F(1, 2), F(0), F(1)),
                                        (F(1), F(1), F(2)),
                                        (F(3), F(5), F(6))])
def test_raw_prefactor_retains_HL_not_HL_over_S(u, a, total):
    result = audit.cubic_reciprocal_endpoint_dispersion_audit(
        longer_modulus_exponent=u, third_length_exponent=a,
        cofactor_cutoff_exponent=F(1, 1000),
        qsmooth_relative_exponent=F(1, 1000),
        taylor_block_relative_exponent=F(17, 50),
        published_epsilon=F(1, 1000), fixed_weight_log_loss=F(20),
        dyadic_and_q_log_loss=F(7), subcritical_cutoff_log_power=F(40),
        poisson_mode_extra_log_loss=F(4), requested_mrstt_log_saving=F(80),
        target_log_saving=F(1),
    )
    assert result.physical_prefactor_exponent == a
    assert result.prefactor_times_dual_volume_exponent == total
    assert result.prefactor_times_dual_volume_exponent > result.local_target_exponent
    assert result.c_poisson_identity_exact
    assert result.partial_summation_gives_X_inverse
    assert not result.local_endpoint_dispersion_lemma_proved


def test_lcpe2_does_not_reintroduce_the_missing_inverse_S():
    result = audit.cubic_reciprocal_lcpe2_audit(
        zeta_log_depth=F(2), shift_log_depth=F(2),
        requested_log_saving=F(80), fixed_log_losses=F(20),
        subcritical_cutoff_log_power=F(40), poisson_mode_extra_log_loss=F(4),
        dyadic_and_q_log_loss=F(7), target_log_saving=F(1),
    )
    assert not result.physical_prefactor_times_dual_volume_is_T
    assert not result.lcpe2_covered_unconditionally


def test_balanced_edge_keeps_the_raw_prefactor_deficit():
    result = audit.balanced_adaptive_reciprocal_phase_audit(
        cofactor_cutoff_exponent=F(1, 1000),
        qsmooth_relative_exponent=F(1, 1000),
        taylor_block_relative_exponent=F(17, 50),
        published_epsilon=F(1, 1000),
    )
    assert result.physical_prefactor_relative_to_target_exponent == F(-267, 550)
    assert not result.prefactor_times_dual_volume_matches_target
    assert result.c_poisson_identity_exact
    assert not result.short_cofactor_range_covered
    assert not result.bcr_and_reciprocal_pieces_cover_full_balanced_edge


def test_slack_vertices_keep_the_raw_prefactor_deficit():
    result = audit.adaptive_reciprocal_slack_vertex_audit(
        cofactor_cutoff_exponent=F(1, 1000),
        qsmooth_relative_exponent=F(1, 1000),
        taylor_block_relative_exponent=F(17, 50),
        published_epsilon=F(1, 1000),
        reciprocal_radical_moment_abscissa=F(1, 100),
    )
    assert not result.short_cofactor_normalization_is_exact
    assert result.covered_vertex_indices == ()
    assert len(result.remaining_vertex_indices) == 14
