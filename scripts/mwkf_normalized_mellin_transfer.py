"""Exact finite certificates for normalized Mellin divisor convolution.

The rational model uses raw coefficients with the physical norm
sum_x |a(x)|^2/x.  Equivalently a(x)/sqrt(x) uses ordinary Euclidean norm.
The accompanying proof applies to complex Mellin weights n^(-z),
Re(z)>=0, uniformly in Im(z).  No twisted-moment estimate is asserted.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import gcd, lcm

from scripts.mwkf_mobius_type_identity import divisors, mobius

F = Fraction


@dataclass(frozen=True)
class NormalizedConvolutionCertificate:
    forward_coefficients: tuple[tuple[int, Fraction], ...]
    recovered_coefficients: tuple[tuple[int, Fraction], ...]
    input_weighted_norm_squared: Fraction
    output_weighted_norm_squared: Fraction
    maximum_divisor_count: int
    harmonic_mass: Fraction
    squared_operator_envelope: Fraction
    forward_envelope: Fraction
    inverse_envelope: Fraction
    lcm_gram_entries: tuple[tuple[int, int, Fraction], ...]
    gram_energy: Fraction
    inverse_identity_exact: bool
    lcm_gram_identity_exact: bool
    forward_bound_verified: bool
    inverse_bound_verified: bool


def normalized_convolution_certificate(
    *,
    coefficients: dict[int, Fraction],
    product_cutoff: int,
    quotient_weights: dict[int, Fraction],
) -> NormalizedConvolutionCertificate:
    """Apply w-convolution and its exact mu*w inverse on one finite lattice.

    w is a contractive completely multiplicative rational model.  At
    w=1 this is z=0; w(n)=1/n models z=1.  Signed unit weights test that
    the inverse and the two Gram legs retain the same Mellin model.

    Both squared operator norms in l2(1/x) are bounded by
    max_{n<=X} tau(n) * H_X.  The LCM Gram includes floor(X/lcm(d,e))
    exactly, including the empty sum when lcm(d,e)>X.
    """

    X = product_cutoff
    if not isinstance(X, int) or X < 1:
        raise ValueError("product cutoff must be a positive integer")
    support = tuple(range(1, X + 1))
    if not coefficients or any(
        not isinstance(d, int) or d not in support for d in coefficients
    ):
        raise ValueError("nonempty coefficient support must lie in [1,X]")
    if set(quotient_weights) != set(support):
        raise ValueError("the Mellin model must supply every quotient up to X")
    weights = {n: F(quotient_weights[n]) for n in support}
    if weights[1] != 1 or any(abs(value) > 1 for value in weights.values()):
        raise ValueError("Mellin weights must be contractive with w(1)=1")
    if any(
        weights[u * v] != weights[u] * weights[v]
        for u in support
        for v in range(1, X // u + 1)
    ):
        raise ValueError("Mellin weights must be completely multiplicative")
    source = {n: F(coefficients.get(n, 0)) for n in support}
    divisor_table = {n: tuple(divisors(n)) for n in support}
    forward = {
        x: sum(
            (source[d] * weights[x // d] for d in divisor_table[x]), F(0)
        )
        for x in support
    }
    recovered = {
        x: sum(
            (
                forward[d] * mobius(x // d) * weights[x // d]
                for d in divisor_table[x]
            ),
            F(0),
        )
        for x in support
    }

    def norm_squared(vector):
        return sum((value * value / n for n, value in vector.items()), F(0))

    input_norm = norm_squared(source)
    output_norm = norm_squared(forward)
    divisor_maximum = max(map(len, divisor_table.values()))
    harmonic = sum((F(1, n) for n in support), F(0))
    envelope = divisor_maximum * harmonic
    input_indices = tuple(sorted(coefficients))
    gram = {}
    direct_gram = {}
    for d in input_indices:
        for e in input_indices:
            multiple = lcm(d, e)
            gram[d, e] = (
                weights[multiple // d]
                * weights[multiple // e]
                / multiple
                * sum(
                    (weights[k] ** 2 / k for k in range(1, X // multiple + 1)),
                    F(0),
                )
            )
            direct_gram[d, e] = sum(
                (
                    weights[x // d] * weights[x // e] / x
                    for x in support
                    if x % d == 0 and x % e == 0
                ),
                F(0),
            )
    gram_energy = sum(
        (source[d] * value * source[e] for (d, e), value in gram.items()), F(0)
    )
    inverse_exact = source == recovered
    gram_exact = gram == direct_gram and gram_energy == output_norm
    forward_bound = output_norm <= envelope * input_norm
    inverse_bound = input_norm <= envelope * output_norm
    if not all((inverse_exact, gram_exact, forward_bound, inverse_bound)):
        raise ArithmeticError("the normalized Mellin transfer certificate failed")
    return NormalizedConvolutionCertificate(
        forward_coefficients=tuple(forward.items()),
        recovered_coefficients=tuple(recovered.items()),
        input_weighted_norm_squared=input_norm,
        output_weighted_norm_squared=output_norm,
        maximum_divisor_count=divisor_maximum,
        harmonic_mass=harmonic,
        squared_operator_envelope=envelope,
        forward_envelope=envelope * input_norm,
        inverse_envelope=envelope * output_norm,
        lcm_gram_entries=tuple((d, e, value) for (d, e), value in gram.items()),
        gram_energy=gram_energy,
        inverse_identity_exact=inverse_exact,
        lcm_gram_identity_exact=gram_exact,
        forward_bound_verified=forward_bound,
        inverse_bound_verified=inverse_bound,
    )


def signed_packet_transfer_certificate(
    *,
    coefficient_packets: dict[str, dict[int, Fraction]],
    product_cutoff: int,
    quotient_weights: dict[int, Fraction],
) -> dict[str, object]:
    """Apply one common map to the signed packet sum, retaining cross terms.

    Packet labels can be the already derived Type blocks.  This routine
    does not derive a new Type identity or introduce a direct-sum norm
    over labels that previously had to cancel.
    """

    if not coefficient_packets or any(not name for name in coefficient_packets):
        raise ValueError("at least one named coefficient packet is required")
    certificates = {
        name: normalized_convolution_certificate(
            coefficients=coefficients,
            product_cutoff=product_cutoff,
            quotient_weights=quotient_weights,
        )
        for name, coefficients in coefficient_packets.items()
    }
    indices = sorted({n for packet in coefficient_packets.values() for n in packet})
    combined = {
        n: sum((F(packet.get(n, 0)) for packet in coefficient_packets.values()), F(0))
        for n in indices
    }
    combined_certificate = normalized_convolution_certificate(
        coefficients=combined,
        product_cutoff=product_cutoff,
        quotient_weights=quotient_weights,
    )
    outputs = {
        name: dict(certificate.forward_coefficients)
        for name, certificate in certificates.items()
    }
    gram = {
        (left, right): sum(
            (outputs[left][n] * outputs[right][n] / n
             for n in range(1, product_cutoff + 1)),
            F(0),
        )
        for left in coefficient_packets
        for right in coefficient_packets
    }
    signed_sum = sum(gram.values(), F(0))
    combined_output = dict(combined_certificate.forward_coefficients)
    reassembly_exact = all(
        combined_output[n] == sum((output[n] for output in outputs.values()), F(0))
        for n in combined_output
    )
    if (
        not reassembly_exact
        or signed_sum != combined_certificate.output_weighted_norm_squared
    ):
        raise ArithmeticError("the signed packet transfer did not reassemble")
    return {
        "packet_gram": gram,
        "signed_gram_sum": signed_sum,
        "blockwise_absolute_sum": sum(map(abs, gram.values()), F(0)),
        "combined_input_weighted_norm_squared": (
            combined_certificate.input_weighted_norm_squared
        ),
        "combined_output_weighted_norm_squared": (
            combined_certificate.output_weighted_norm_squared
        ),
        "combined_norm_envelope": combined_certificate.forward_envelope,
        "transfer_applied_after_signed_reassembly": reassembly_exact,
        "coupled_kernel_gate_proved": False,
    }


def gcd_main_kernel_certificate(
    *, coefficients: dict[int, Fraction], cutoff: int
) -> dict[str, object]:
    """Diagonalize the reciprocal-LCM form and bound its normalized norm.

    For c(d)=a(d)/sqrt(d), this certifies the positive matrix
    gcd(d,e)/sqrt(de) against max_{n<=N} tau(n) * H_N.  It does not
    evaluate a zeta moment or assert that the residual has this norm.
    """

    if not isinstance(cutoff, int) or cutoff < 1:
        raise ValueError("cutoff must be a positive integer")
    support = tuple(range(1, cutoff + 1))
    if not coefficients or any(
        not isinstance(d, int) or d not in support for d in coefficients
    ):
        raise ValueError("nonempty coefficient support must lie in [1,N]")
    source = {d: F(coefficients.get(d, 0)) for d in support}
    totients = {r: sum(gcd(k, r) == 1 for k in range(1, r + 1)) for r in support}
    squares = {
        r: totients[r] * sum(
            (source[d] / d for d in range(r, cutoff + 1, r)), F(0)
        ) ** 2
        for r in support
    }
    direct = sum(
        (source[d] * source[e] * F(gcd(d, e), d * e)
         for d in support for e in support),
        F(0),
    )
    input_norm = sum((source[d] ** 2 / d for d in support), F(0))
    harmonic = sum((F(1, d) for d in support), F(0))
    envelope = max(len(divisors(d)) for d in support) * harmonic
    exact = direct == sum(squares.values(), F(0))
    bounded = 0 <= direct <= envelope * input_norm
    if not exact or not bounded:
        raise ArithmeticError("the gcd main-kernel certificate failed")
    return {
        "gcd_quadratic": direct,
        "totient_squares": squares,
        "input_weighted_norm_squared": input_norm,
        "squared_operator_envelope": envelope,
        "quadratic_envelope": envelope * input_norm,
        "diagonalization_exact": exact,
        "bound_verified": bounded,
    }
