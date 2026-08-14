from fractions import Fraction

import pytest

from experiments.rh.short_interval_signed_l2_audit import (
    exponent_ledger,
    growth_exponent,
    psi_window_decomposition,
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
