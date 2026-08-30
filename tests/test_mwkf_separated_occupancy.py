"""Relative large-sieve coverage needs an actual occupancy denominator."""

from fractions import Fraction as F

from scripts.audit_mwkf_coverage import (
    level_dependent_ratio_fiber_saturation_audit,
    separated_ratio_fiber_large_sieve_polytope_audit,
)


def test_separability_alone_does_not_certify_relative_coverage() -> None:
    result = separated_ratio_fiber_large_sieve_polytope_audit(
        long_prime_exponent=F(2),
        short_prime_exponent=F(3, 2),
        required_linear_gain_exponent=F(1, 4),
        level_independent_long_coefficients_verified=True,
        bounded_projective_q_factor_verified=True,
    )
    assert not result["separated_coefficient_cell_covered"]
    assert not result["occupancy_normalization_supplied"]
    assert result["occupancy_energy_exponent"] is None


def test_single_modulus_normalization_cannot_claim_dense_saving() -> None:
    result = separated_ratio_fiber_large_sieve_polytope_audit(
        long_prime_exponent=F(2),
        short_prime_exponent=F(3, 2),
        required_linear_gain_exponent=F(1, 4),
        level_independent_long_coefficients_verified=True,
        bounded_projective_q_factor_verified=True,
        normalized_occupancy_lower_exponent=F(2),
    )
    assert result["occupancy_energy_exponent"] == F(2)
    assert result["large_sieve_energy_saving_exponent"] == 0
    assert not result["separated_coefficient_cell_covered"]


def test_verified_dense_normalization_recovers_the_half_power() -> None:
    result = separated_ratio_fiber_large_sieve_polytope_audit(
        long_prime_exponent=F(2),
        short_prime_exponent=F(3, 2),
        required_linear_gain_exponent=F(1, 4),
        level_independent_long_coefficients_verified=True,
        bounded_projective_q_factor_verified=True,
        normalized_occupancy_lower_exponent=F(7, 2),
    )
    assert result["large_sieve_energy_saving_exponent"] == F(1, 2)
    assert result["separated_coefficient_cell_covered"]
    assert not result["physical_level_dependent_WRFE_proved"]
    assert not result["coupled_kernel_gate_closed"]


def test_rank_one_single_modulus_coefficients_retain_occupancy_saturation() -> None:
    # C_q(p)=beta_q*alpha_p with q=(5,7), beta=(1,0),
    # p=(23,43), alpha=(1,1): a single separated atom, not level dependence.
    result = level_dependent_ratio_fiber_saturation_audit(
        short_prime=5,
        determinant_shift=1,
        supported_long_primes=(23, 43),
        weights=(F(1), F(1)),
    )
    assert result["signed_ratio_fiber_energy"] == F(12)
    assert result["occupancy_cauchy_bound"] == F(16)
    assert result["energy_to_occupancy_ratio"] == F(3, 4)


def test_missing_normalization_refuses_even_zero_gain_certification() -> None:
    result = separated_ratio_fiber_large_sieve_polytope_audit(
        long_prime_exponent=F(2),
        short_prime_exponent=F(3, 2),
        required_linear_gain_exponent=F(0),
        level_independent_long_coefficients_verified=True,
        bounded_projective_q_factor_verified=True,
    )
    assert not result["normalized_power_ledger_covers"]
    assert not result["separated_coefficient_cell_covered"]
