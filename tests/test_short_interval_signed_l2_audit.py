from fractions import Fraction

import pytest

from experiments.rh.short_interval_signed_l2_audit import (
    exponent_ledger,
    finite_cyclic_weighted_fourier_identity,
    growth_exponent,
    mobius,
    psi_window_decomposition,
    vaughan_two_thirds_budget,
    vaughan_components,
    von_mangoldt,
    weighted_centered_identity,
    zero_density_exponents,
)


def test_two_thirds_model_exponent_and_strict_boundary() -> None:
    a = Fraction(2, 3)

    boundary = exponent_ledger(a=a, beta=Fraction(2, 3))
    assert boundary.zero_response == Fraction(5, 3)
    assert boundary.target == Fraction(5, 3)
    assert boundary.contradiction_margin == 0

    right = exponent_ledger(a=a, beta=Fraction(3, 4))
    assert right.zero_response == Fraction(11, 6)
    assert right.contradiction_margin == Fraction(1, 6)
    assert right.zero_exclusion_threshold == Fraction(2, 3)


def test_coefficientwise_absolute_value_has_exact_two_thirds_deficit() -> None:
    ledger = exponent_ledger(a=Fraction(2, 3), beta=Fraction(3, 4))
    assert ledger.diagonal == Fraction(5, 3)
    assert ledger.floor_remainder == 1
    assert ledger.absolute_off_diagonal == Fraction(7, 3)
    assert ledger.absolute_value_deficit == Fraction(2, 3)


def test_weighted_centered_identity_keeps_signed_off_diagonal() -> None:
    coefficients = {2: 3.0, 3: -2.0, 4: 5.0, 5: -7.0}
    samples = [
        (1.25, 2.0, 0.5),
        (2.10, 2.5, 1.25),
        (3.00, 2.0, 0.75),
    ]

    identity = weighted_centered_identity(coefficients, samples)

    assert identity.window_square == pytest.approx(identity.expanded)
    assert identity.expanded == pytest.approx(
        identity.diagonal + identity.off_diagonal
    )
    assert identity.off_diagonal < 0


def test_psi_window_decomposition_is_exact_up_to_roundoff() -> None:
    # Synthetic Lambda values are enough: the statement is a finite algebraic
    # identity and does not rely on primality or an asymptotic theorem.
    lambda_values = {2: 0.7, 3: 1.1, 4: 0.0, 5: 1.6, 6: 0.2}
    result = psi_window_decomposition(lambda_values, x=1.4, h=3.8)

    assert result.direct_error == pytest.approx(
        result.centered_sum + result.floor_remainder
    )
    assert abs(result.floor_remainder) < 1


def test_two_thirds_crossing_belongs_to_linear_comparison_not_ingham() -> None:
    density = zero_density_exponents(Fraction(2, 3))
    assert density.carlson == density.linear_eight_thirds == Fraction(8, 9)
    assert density.ingham == Fraction(3, 4)
    assert density.carlson_derivative == Fraction(-4, 3)
    assert density.linear_eight_thirds_derivative == Fraction(-8, 3)
    assert density.ingham_derivative == Fraction(-27, 16)
    assert density.guth_maynard == Fraction(15, 19)
    assert density.guth_maynard_uniform == Fraction(10, 13)
    assert density.best_recorded == Fraction(3, 4)


def test_packet_growth_uses_logarithmic_generation_rate() -> None:
    assert growth_exponent(c=2, k=2) == pytest.approx(1.0)
    with pytest.raises(ValueError, match="k must be greater than 1"):
        growth_exponent(c=2, k=1)
    with pytest.raises(ValueError, match="c must be positive"):
        growth_exponent(c=0, k=2)


def test_nonconstant_weight_requires_double_frequency_coupling() -> None:
    coefficients = [3.0, -2.0, 5.0, -7.0, 1.5, 4.0, -1.0, 2.0]
    weights = [0.2, 0.5, 1.0, 1.5, 1.3, 0.8, 0.4, 0.1]

    identity = finite_cyclic_weighted_fourier_identity(
        coefficients, window_length=3, weights=weights
    )

    assert identity.direct_energy == pytest.approx(
        identity.double_frequency_energy, abs=1e-9
    )
    assert abs(identity.imaginary_residual) < 1e-9
    assert abs(identity.frequency_off_diagonal) > 1e-3
    assert identity.direct_energy != pytest.approx(
        identity.diagonal_frequency_energy, abs=1e-3
    )


def test_constant_weight_collapses_to_single_frequency_parseval() -> None:
    coefficients = [1.0, -1.0, 2.0, 0.5, -3.0, 4.0]

    identity = finite_cyclic_weighted_fourier_identity(
        coefficients, window_length=2, weights=[1.0] * len(coefficients)
    )

    assert identity.direct_energy == pytest.approx(
        identity.diagonal_frequency_energy, abs=1e-9
    )
    assert identity.frequency_off_diagonal == pytest.approx(0.0, abs=1e-9)


def test_actual_von_mangoldt_coefficients_satisfy_fourier_identity() -> None:
    coefficients = [von_mangoldt(n) - 1.0 for n in range(2, 18)]
    weights = [float((j + 1) * (16 - j)) for j in range(16)]

    identity = finite_cyclic_weighted_fourier_identity(
        coefficients, window_length=4, weights=weights
    )

    assert von_mangoldt(8) == pytest.approx(__import__("math").log(2))
    assert von_mangoldt(12) == 0.0
    assert identity.direct_energy == pytest.approx(
        identity.double_frequency_energy, rel=1e-11, abs=1e-9
    )


def test_vaughan_identity_holds_pointwise_before_estimating_blocks() -> None:
    for n in range(1, 201):
        components = vaughan_components(n, u_cutoff=5, v_cutoff=5)
        assert components.total == pytest.approx(von_mangoldt(n), abs=1e-12)
        assert components.centered_total == pytest.approx(
            von_mangoldt(n) - 1.0, abs=1e-12
        )


def test_mobius_values_used_by_vaughan_identity() -> None:
    assert [mobius(n) for n in range(1, 11)] == [
        1,
        -1,
        -1,
        0,
        -1,
        1,
        -1,
        0,
        0,
        1,
    ]


def test_two_thirds_budget_triggers_multiple_failure_stop_rule() -> None:
    audit = vaughan_two_thirds_budget()
    failures = [entry for entry in audit.entries if entry.deficit > 0]

    assert audit.target_exponent == Fraction(5, 3)
    assert len(failures) >= 2
    assert all(entry.available_exponent == Fraction(7, 3) for entry in failures)
    assert all(entry.deficit == Fraction(2, 3) for entry in failures)
    assert audit.should_stop_vaughan
    assert not audit.guth_maynard_gate_open
