"""Finite witnesses for the physically weighted, not raw, divisor map."""

import importlib
import importlib.util
from fractions import Fraction as F

import pytest


def transfer_module():
    name = "scripts.mwkf_normalized_mellin_transfer"
    assert importlib.util.find_spec(name) is not None, (
        "the normalized Mellin norm-transfer implementation is missing"
    )
    return importlib.import_module(name)


def test_weighted_norm_uses_harmonic_mass_and_exact_lcm_gram() -> None:
    """Dropping 1/x gives mass X instead of H_X and breaks these literals."""
    result = transfer_module().normalized_convolution_certificate(
        coefficients={1: F(1), 2: F(-2), 3: F(3)},
        product_cutoff=6,
        quotient_weights={n: F(1) for n in range(1, 7)},
    )
    assert result.forward_coefficients == (
        (1, F(1)), (2, F(-1)), (3, F(4)),
        (4, F(-1)), (5, F(1)), (6, F(2)),
    )
    assert result.recovered_coefficients == (
        (1, F(1)), (2, F(-2)), (3, F(3)),
        (4, F(0)), (5, F(0)), (6, F(0)),
    )
    assert result.input_weighted_norm_squared == F(6)
    assert result.output_weighted_norm_squared == F(159, 20)
    assert result.maximum_divisor_count == 4
    assert result.harmonic_mass == F(49, 20)
    assert result.squared_operator_envelope == F(49, 5)
    assert result.forward_envelope == F(294, 5)
    gram = {(d, e): value for d, e, value in result.lcm_gram_entries}
    assert gram[1, 1] == F(49, 20)
    assert gram[1, 2] == F(11, 12)
    assert gram[2, 3] == F(1, 6)
    assert gram[3, 3] == F(1, 2)
    assert result.gram_energy == result.output_weighted_norm_squared
    assert result.inverse_identity_exact
    assert result.lcm_gram_identity_exact
    assert result.forward_bound_verified
    assert result.inverse_bound_verified


@pytest.mark.parametrize(
    ("weights", "forward", "gram23"),
    [
        (
            (1, -1, -1, 1, -1, 1),
            (1, -3, 2, 3, -1, 0),
            F(1, 6),
        ),
        (
            (1, F(1, 2), F(1, 3), F(1, 4), F(1, 5), F(1, 6)),
            (1, F(-3, 2), F(10, 3), F(-3, 4), F(1, 5), 1),
            F(1, 36),
        ),
    ],
)
def test_inverse_keeps_the_mellin_quotient_weight(weights, forward, gram23):
    """Omitting w(n) from the inverse or from either Gram leg must fail."""
    result = transfer_module().normalized_convolution_certificate(
        coefficients={1: F(1), 2: F(-2), 3: F(3)},
        product_cutoff=6,
        quotient_weights={n: F(value) for n, value in enumerate(weights, 1)},
    )
    assert tuple(value for _, value in result.forward_coefficients) == forward
    assert dict(result.recovered_coefficients) == {
        1: F(1), 2: F(-2), 3: F(3), 4: F(0), 5: F(0), 6: F(0)
    }
    gram = {(d, e): value for d, e, value in result.lcm_gram_entries}
    assert gram[2, 3] == gram23
    assert result.forward_bound_verified
    assert result.inverse_bound_verified


def test_lcm_cutoff_has_no_missing_endpoint_or_extra_lift() -> None:
    """A common multiple is present at X=6, but absent at X=5."""
    helper = transfer_module().normalized_convolution_certificate
    before = helper(
        coefficients={2: F(1), 3: F(1)},
        product_cutoff=5,
        quotient_weights={n: F(1) for n in range(1, 6)},
    )
    endpoint = helper(
        coefficients={2: F(1), 3: F(1)},
        product_cutoff=6,
        quotient_weights={n: F(1) for n in range(1, 7)},
    )
    before_gram = {(d, e): v for d, e, v in before.lcm_gram_entries}
    endpoint_gram = {(d, e): v for d, e, v in endpoint.lcm_gram_entries}
    assert before_gram[2, 3] == 0
    assert endpoint_gram[2, 3] == F(1, 6)


def test_signed_packet_transfer_keeps_the_negative_cross_gram() -> None:
    """Replacing the signed Gram by its blockwise absolute sum is not transfer."""
    result = transfer_module().signed_packet_transfer_certificate(
        coefficient_packets={
            "I": {1: F(2), 2: F(-3)},
            "II": {1: F(0), 2: F(6)},
        },
        product_cutoff=6,
        quotient_weights={n: F(1) for n in range(1, 7)},
    )
    assert result["packet_gram"] == {
        ("I", "I"): F(141, 20),
        ("I", "II"): F(-11, 2),
        ("II", "I"): F(-11, 2),
        ("II", "II"): F(33),
    }
    assert result["signed_gram_sum"] == F(581, 20)
    assert result["blockwise_absolute_sum"] == F(1021, 20)
    assert result["combined_input_weighted_norm_squared"] == F(17, 2)
    assert result["combined_output_weighted_norm_squared"] == F(581, 20)
    assert result["transfer_applied_after_signed_reassembly"]
    assert not result["coupled_kernel_gate_proved"]


@pytest.mark.parametrize(
    ("weights", "message"),
    [
        ({1: F(1), 2: F(1)}, "every quotient"),
        ({1: F(1), 2: F(2), 3: F(1), 4: F(4)}, "contractive"),
        ({1: F(1), 2: F(1, 2), 3: F(1), 4: F(1)}, "multiplicative"),
    ],
)
def test_invalid_mellin_models_do_not_certify_the_inverse(weights, message):
    with pytest.raises(ValueError, match=message):
        transfer_module().normalized_convolution_certificate(
            coefficients={1: F(1)}, product_cutoff=4, quotient_weights=weights
        )


def test_totient_square_main_kernel_has_the_same_normalized_envelope():
    """The norm uses a(d)^2/d, while the quadratic uses gcd(d,e)/(de)."""
    result = transfer_module().gcd_main_kernel_certificate(
        coefficients={1: F(1), 2: F(-2), 3: F(3)}, cutoff=3
    )
    assert result["gcd_quadratic"] == F(4)
    assert result["totient_squares"] == {
        1: F(1), 2: F(1), 3: F(2)
    }
    assert result["input_weighted_norm_squared"] == F(6)
    assert result["squared_operator_envelope"] == F(11, 3)
    assert result["quadratic_envelope"] == F(22)
    assert result["diagonalization_exact"]
    assert result["bound_verified"]


def test_singleton_and_zero_vector_keep_exact_inverse():
    helper = transfer_module().normalized_convolution_certificate
    for coefficient in (F(0), F(-7, 3)):
        result = helper(
            coefficients={1: coefficient}, product_cutoff=1,
            quotient_weights={1: F(1)},
        )
        assert result.forward_coefficients == ((1, coefficient),)
        assert result.recovered_coefficients == ((1, coefficient),)
        assert result.squared_operator_envelope == 1
        assert result.input_weighted_norm_squared == coefficient**2


@pytest.mark.parametrize("coefficients", [{}, {0: F(1)}, {4: F(1)}])
def test_main_kernel_rejects_outside_or_missing_support(coefficients):
    with pytest.raises(ValueError, match="support"):
        transfer_module().gcd_main_kernel_certificate(
            coefficients=coefficients, cutoff=3
        )
