"""Independent small-N Arb interval assemblies for Weil matrix entries.

This module does not import or call the released ``arb_ldlt_certify.py`` or
the point-value assemblers in ``weil_extremal_crosscheck``.  It implements two
formula families separately and retains both outward-rounded interval matrices.
The verifier uses only the Python standard library; generation requires
python-flint.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, Iterable, Mapping, Sequence, Tuple


SCHEMA_VERSION = "weil-extremal-kernel-arb-overlap/v1"
CROSS_PRECISION_SCHEMA_VERSION = "weil-extremal-kernel-arb-cross-precision-overlap/v1"
CLAIM_SCOPE = "small-N-gate-a-preparation-only"
GATE_A_STATUS = "not_satisfied"
UPSTREAM_SCRIPT_SHA256 = (
    "02462e7f75a601ed8a5cc4d5c22064ece8088140ff45b9a21fd0295162c72039"
)
ROUTE_NAMES = ("auxiliary_s_cc_xc", "ccm_hypergeometric_lerch")
ROUTES = {
    "auxiliary_s_cc_xc": {
        "assembly": "fresh python-flint Arb S/CC/XC full-matrix assembly",
        "archimedean_formula": "digamma/trigamma plus rigorously bounded geometric tails",
        "pole_formula": "expanded rational expression in the two Fourier indices",
        "prime_formula": "direct cosine/sine Guinand-Weil block",
    },
    "ccm_hypergeometric_lerch": {
        "assembly": "fresh python-flint Arb CCM full-matrix assembly",
        "archimedean_formula": "hypergeometric/Lerch alpha-beta-gamma functions",
        "pole_formula": "factorized pole_c/pole_s outer-product expression",
        "prime_formula": "CCM p0 and p0-derivative representation",
    },
}
SHARED_COMPONENTS = [
    "python-flint Arb runtime",
    "parameter validation",
    "prime-power enumeration",
    "index order",
    "rational interval serialization",
]
LIMITATIONS = [
    "Both formula implementations use the same python-flint Arb runtime.",
    "This small-N artifact does not assemble the registered c=100, N=200 Gate A matrix.",
    "No exact rational LDL certificate or interval-to-LDL transfer margin is emitted.",
    "Only one precision is recorded, so entrywise narrowing at a second precision is not tested.",
]
CROSS_PRECISION_LIMITATIONS = [
    "Both formula implementations use the same python-flint Arb runtime.",
    "This small-N artifact does not assemble the registered c=100, N=200 Gate A matrix.",
    "No exact rational LDL certificate or interval-to-LDL transfer margin is emitted.",
    "Second-precision narrowing is established only for the retained c=13, N=4 interval matrices.",
]

Entry = Tuple[int, int]
BallMatrix = Dict[Entry, Any]
FractionMatrix = Tuple[Tuple[Fraction, ...], ...]


def _require_parameters(
    c: int, N: int, prec_bits: int, decimal_enclosure_digits: int
) -> None:
    if isinstance(c, bool) or not isinstance(c, int) or c < 2:
        raise ValueError("c must be an integer at least 2")
    if isinstance(N, bool) or not isinstance(N, int) or N < 0:
        raise ValueError("N must be a nonnegative integer")
    if (
        isinstance(prec_bits, bool)
        or not isinstance(prec_bits, int)
        or prec_bits < 128
    ):
        raise ValueError("prec_bits must be an integer at least 128")
    if (
        isinstance(decimal_enclosure_digits, bool)
        or not isinstance(decimal_enclosure_digits, int)
        or decimal_enclosure_digits < 30
    ):
        raise ValueError("decimal_enclosure_digits must be an integer at least 30")


def _flint() -> Tuple[Any, Any, Any, str]:
    try:
        import flint
        from flint import acb, arb, ctx
    except ImportError as error:
        raise RuntimeError(
            "interval generation requires python-flint; verification does not"
        ) from error
    return arb, acb, ctx, flint.__version__


def prime_powers_up_to(c: int) -> Tuple[Tuple[int, int], ...]:
    """Return ``(q,p)`` for every prime power ``q=p^a <= c``."""
    if isinstance(c, bool) or not isinstance(c, int) or c < 2:
        raise ValueError("c must be an integer at least 2")
    primes = []
    for candidate in range(2, c + 1):
        if all(candidate % prime for prime in primes):
            primes.append(candidate)
    powers = []
    for prime in primes:
        value = prime
        while value <= c:
            powers.append((value, prime))
            value *= prime
    return tuple(powers)


def _geometric_term_count(c: int, prec_bits: int) -> int:
    terms = 1
    target = 1 << (prec_bits + 64)
    while c ** (2 * terms) <= target:
        terms += 1
    return terms


def _auxiliary_geometric_sums(
    arb: Any, n: int, L: Any, c: int, prec_bits: int
) -> Tuple[Any, Any, Any, Any]:
    """Enclose the four geometric series, including explicit omitted tails."""
    pi = arb.pi()
    w = 2 * pi * n / L
    w_squared = w * w
    sums = [arb(0), arb(0), arb(0), arb(0)]
    terms = _geometric_term_count(c, prec_bits)
    for k in range(terms):
        c_k = arb(2 * k) + arb(1) / 2
        exponential = (-c_k * L).exp()
        denominator = c_k * c_k + w_squared
        sums[0] += exponential / denominator
        if n:
            sums[1] += exponential * w_squared / (c_k * denominator)
        sums[2] += exponential * c_k / denominator
        sums[3] += (
            exponential
            * (c_k * c_k - w_squared)
            / (denominator * denominator)
        )

    first_omitted = arb(2 * terms) + arb(1) / 2
    geometric_tail = (-first_omitted * L).exp() / (
        1 - arb(1) / (c * c)
    )
    inverse_linear_tail = geometric_tail / first_omitted
    inverse_square_tail = inverse_linear_tail / first_omitted
    return (
        arb(sums[0], inverse_square_tail),
        arb(sums[1], inverse_linear_tail),
        arb(sums[2], inverse_linear_tail),
        arb(sums[3], inverse_square_tail),
    )


def assemble_auxiliary_s_cc_xc(
    c: int, N: int, prec_bits: int, decimal_enclosure_digits: int = 120
) -> BallMatrix:
    """Assemble ordered entries using the auxiliary S/CC/XC Arb formulas."""
    _require_parameters(c, N, prec_bits, decimal_enclosure_digits)
    arb, acb, ctx, _version = _flint()
    previous_precision = ctx.prec
    ctx.prec = prec_bits
    try:
        L = arb(c).log()
        pi = arb.pi()
        quarter = arb(1) / 4
        psi_quarter = quarter.digamma()
        s_values = []
        cc_values = []
        xc_values = []
        for n in range(N + 1):
            argument = acb(quarter, pi * n / L)
            psi = argument.digamma()
            trigamma = argument.polygamma(1)
            g_s, g_cc, g_xc1, g_xc2 = _auxiliary_geometric_sums(
                arb, n, L, c, prec_bits
            )
            if n:
                w = 2 * pi * n / L
                s_values.append(psi.imag / 2 - w * g_s)
                cc_values.append(-(psi.real - psi_quarter) / 2 + g_cc)
            else:
                s_values.append(arb(0))
                cc_values.append(arb(0))
            xc_values.append(trigamma.real / 4 - L * g_xc1 - g_xc2)

        def signed_s(index: int) -> Any:
            return s_values[index] if index >= 0 else -s_values[-index]

        u = (L / 2).exp()
        J = -2 * (u + 1).log() + (u * u + 1).log() + 2 * u.atan()
        J += arb.const_log2() - pi / 2
        kappa = (4 * pi * ((L.exp() - 1) / (L.exp() + 1))).log()
        kappa += arb.const_euler()
        prime_powers = prime_powers_up_to(c)
        weights = [arb(p).log() / arb(q).sqrt() for q, p in prime_powers]
        positions = [arb(q).log() for q, _p in prime_powers]

        entries = {}
        L_squared = L * L
        pi_factor = 16 * pi * pi
        pole_prefactor = 32 * L * (L / 4).sinh() ** 2
        for n in range(-N, N + 1):
            for m in range(-N, N + 1):
                pole = pole_prefactor * (L_squared - pi_factor * m * n)
                pole /= (L_squared + pi_factor * m * m) * (
                    L_squared + pi_factor * n * n
                )
                if n == m:
                    archimedean = (
                        kappa
                        + 2 * cc_values[abs(n)]
                        + J
                        - 2 * xc_values[abs(n)] / L
                    )
                else:
                    archimedean = (signed_s(m) - signed_s(n)) / (
                        pi * (n - m)
                    )
                prime = arb(0)
                for weight, position in zip(weights, positions):
                    if n == m:
                        basis_value = (
                            2
                            * (1 - position / L)
                            * (2 * pi * n * position / L).cos()
                        )
                    else:
                        basis_value = (
                            (2 * pi * m * position / L).sin()
                            - (2 * pi * n * position / L).sin()
                        ) / (pi * (n - m))
                    prime += weight * basis_value
                entries[(n, m)] = pole - archimedean - prime
        return entries
    finally:
        ctx.prec = previous_precision


def assemble_ccm_hypergeometric_lerch(
    c: int, N: int, prec_bits: int, decimal_enclosure_digits: int = 120
) -> BallMatrix:
    """Assemble ordered entries using the independent CCM Arb formulas."""
    _require_parameters(c, N, prec_bits, decimal_enclosure_digits)
    arb, acb, ctx, _version = _flint()
    previous_precision = ctx.prec
    ctx.prec = prec_bits
    try:
        L = arb(c).log()
        pi = arb.pi()
        z = arb(1) / (c * c)
        z_complex = acb(z)
        quarter = arb(1) / 4
        inverse_sqrt_c = 1 / arb(c).sqrt()
        prime_powers = prime_powers_up_to(c)

        def argument(n: int) -> Any:
            return acb(quarter, pi * n / L)

        def hypergeometric(n: int) -> Any:
            a_n = argument(n)
            return z_complex.hypgeom_2f1(1, a_n, a_n + 1, abc=True)

        def alpha(n: int) -> Any:
            quotient = 2 * L * hypergeometric(n) / acb(L, 4 * pi * n)
            return (
                inverse_sqrt_c * quotient.imag + argument(n).digamma().imag / 2
            ) / pi

        def beta(n: int) -> Any:
            a_n = argument(n)
            denominator = acb(4 * pi * n, -L)
            first = -L * inverse_sqrt_c * (
                2 * L * hypergeometric(n) / denominator
            ).imag
            second = (
                -inverse_sqrt_c * z_complex.lerch_phi(2, a_n).real / 4
            )
            third = a_n.polygamma(1).real / 4
            return (first + second + third) / L

        c_w = ((arb(c).sqrt() - 1) / (arb(c).sqrt() + 1)).log() / 2
        c_w += arb(c).sqrt().atan() - pi / 4
        c_w += arb.const_euler() / 2 + (8 * pi).log() / 2

        hypergeometric_zero = z_complex.hypgeom_2f1(
            quarter, 1, quarter + 1, abc=True
        )

        def gamma(n: int) -> Any:
            first = -inverse_sqrt_c * (
                2 * L * hypergeometric(n) / acb(L, 4 * pi * n)
            ).real
            second = 2 * inverse_sqrt_c * hypergeometric_zero.real
            third = -(argument(n).digamma().real - quarter.digamma()) / 2
            return first + second + third + c_w

        def prime_value(n: int) -> Any:
            value = arb(0)
            for q, p in prime_powers:
                value -= (
                    arb(p).log()
                    * (2 * pi * n * (1 - arb(q).log() / L)).sin()
                    / (pi * arb(q).sqrt())
                )
            return value

        def prime_derivative(n: int) -> Any:
            value = arb(0)
            for q, p in prime_powers:
                value -= (
                    2
                    * arb(p).log()
                    * (1 - arb(q).log() / L)
                    * (2 * pi * n * (1 - arb(q).log() / L)).cos()
                    / arb(q).sqrt()
                )
            return value

        p0 = {n: alpha(n) + prime_value(n) for n in range(-N, N + 1)}
        p0_derivative = {
            n: -2 * (gamma(n) - beta(n)) + prime_derivative(n)
            for n in range(-N, N + 1)
        }

        def pole_c(n: int) -> Any:
            return (L / 4).sinh() / L.sqrt() / (
                quarter + (2 * pi * n / L) ** 2
            )

        def pole_s(n: int) -> Any:
            return (
                4
                * pi
                * (L / 4).sinh()
                * n
                / (L * L.sqrt() * (quarter + (2 * pi * n / L) ** 2))
            )

        entries = {}
        for m in range(-N, N + 1):
            for n in range(-N, N + 1):
                pole = 2 * (pole_c(m) * pole_c(n) - pole_s(m) * pole_s(n))
                if m == n:
                    entries[(m, n)] = p0_derivative[n] + pole
                else:
                    entries[(m, n)] = (p0[m] - p0[n]) / (m - n) + pole
        return entries
    finally:
        ctx.prec = previous_precision


def _fraction_from_scaled_integer(value: int, exponent: int) -> Fraction:
    if exponent >= 0:
        return Fraction(value * (10**exponent))
    return Fraction(value, 10 ** (-exponent))


def arb_fraction_bounds(value: Any, decimal_enclosure_digits: int) -> Tuple[Fraction, Fraction]:
    """Convert an Arb ball to an exact rational interval containing it."""
    if not value.is_finite():
        raise ValueError("matrix assembly produced a non-finite Arb ball")
    midpoint, radius, exponent = value.mid_rad_10exp(decimal_enclosure_digits)
    midpoint_integer = int(midpoint)
    radius_integer = int(radius)
    decimal_exponent = int(exponent)
    if radius_integer < 0:
        raise ValueError("Arb returned a negative serialization radius")
    return (
        _fraction_from_scaled_integer(
            midpoint_integer - radius_integer, decimal_exponent
        ),
        _fraction_from_scaled_integer(
            midpoint_integer + radius_integer, decimal_exponent
        ),
    )


def _format_fraction(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def _format_matrix(matrix: FractionMatrix) -> list[list[str]]:
    return [[_format_fraction(value) for value in row] for row in matrix]


def _rational_enclosure(
    entries: BallMatrix, indices: Sequence[int], decimal_enclosure_digits: int
) -> Tuple[FractionMatrix, FractionMatrix]:
    expected_entries = {(i, j) for i in indices for j in indices}
    if set(entries) != expected_entries:
        raise ValueError("assembled matrix does not contain every ordered entry")
    lower_rows = []
    upper_rows = []
    for i in indices:
        lower_row = []
        upper_row = []
        for j in indices:
            lower, upper = arb_fraction_bounds(
                entries[(i, j)], decimal_enclosure_digits
            )
            lower_row.append(lower)
            upper_row.append(upper)
        lower_rows.append(tuple(lower_row))
        upper_rows.append(tuple(upper_row))
    return tuple(lower_rows), tuple(upper_rows)


def _intersection_evidence(
    left_lower: FractionMatrix,
    left_upper: FractionMatrix,
    right_lower: FractionMatrix,
    right_upper: FractionMatrix,
) -> Dict[str, Any]:
    dimension = len(left_lower)
    overlap_rows = []
    intersection_lower_rows = []
    intersection_upper_rows = []
    for i in range(dimension):
        overlap_row = []
        lower_row = []
        upper_row = []
        for j in range(dimension):
            lower = max(left_lower[i][j], right_lower[i][j])
            upper = min(left_upper[i][j], right_upper[i][j])
            overlap_row.append(lower <= upper)
            lower_row.append(lower)
            upper_row.append(upper)
        overlap_rows.append(overlap_row)
        intersection_lower_rows.append(tuple(lower_row))
        intersection_upper_rows.append(tuple(upper_row))

    intersection_lower = tuple(intersection_lower_rows)
    intersection_upper = tuple(intersection_upper_rows)
    symmetric_lower_rows = []
    symmetric_upper_rows = []
    for i in range(dimension):
        lower_row = []
        upper_row = []
        for j in range(dimension):
            lower_row.append(
                max(intersection_lower[i][j], intersection_lower[j][i])
            )
            upper_row.append(
                min(intersection_upper[i][j], intersection_upper[j][i])
            )
        symmetric_lower_rows.append(tuple(lower_row))
        symmetric_upper_rows.append(tuple(upper_row))
    symmetric_lower = tuple(symmetric_lower_rows)
    symmetric_upper = tuple(symmetric_upper_rows)

    all_entries_overlap = all(value for row in overlap_rows for value in row)
    symmetric_intersection_nonempty = all(
        symmetric_lower[i][j] <= symmetric_upper[i][j]
        for i in range(dimension)
        for j in range(dimension)
    )
    return {
        "entrywise": overlap_rows,
        "intersection": {
            "lower": _format_matrix(intersection_lower),
            "upper": _format_matrix(intersection_upper),
        },
        "symmetric_intersection": {
            "lower": _format_matrix(symmetric_lower),
            "upper": _format_matrix(symmetric_upper),
        },
        "result": {
            "all_entries_overlap": all_entries_overlap,
            "entry_count": dimension * dimension,
            "symmetric_intersection_nonempty": symmetric_intersection_nonempty,
        },
    }


def _matrix_comparison_evidence(
    coarse_lower: FractionMatrix,
    coarse_upper: FractionMatrix,
    fine_lower: FractionMatrix,
    fine_upper: FractionMatrix,
) -> Dict[str, Any]:
    """Record exact rational containment and strict width reduction entrywise."""
    dimension = len(coarse_lower)
    contained_rows = []
    strict_rows = []
    for i in range(dimension):
        contained_row = []
        strict_row = []
        for j in range(dimension):
            coarse_width = coarse_upper[i][j] - coarse_lower[i][j]
            fine_width = fine_upper[i][j] - fine_lower[i][j]
            contained_row.append(
                coarse_lower[i][j] <= fine_lower[i][j]
                and fine_upper[i][j] <= coarse_upper[i][j]
            )
            strict_row.append(fine_width < coarse_width)
        contained_rows.append(contained_row)
        strict_rows.append(strict_row)
    return {
        "contained_entrywise": contained_rows,
        "strictly_narrower_entrywise": strict_rows,
        "result": {
            "all_entries_contained": all(
                value for row in contained_rows for value in row
            ),
            "all_entries_strictly_narrower": all(
                value for row in strict_rows for value in row
            ),
            "entry_count": dimension * dimension,
        },
    }


def _precision_artifact_evidence(
    c: int,
    N: int,
    prec_bits: int,
    decimal_enclosure_digits: int,
    flint_version: str,
) -> Dict[str, Any]:
    """Assemble both routes and retain their exact rational enclosures."""
    indices = tuple(range(-N, N + 1))
    auxiliary_lower, auxiliary_upper = _rational_enclosure(
        assemble_auxiliary_s_cc_xc(c, N, prec_bits, decimal_enclosure_digits),
        indices,
        decimal_enclosure_digits,
    )
    ccm_lower, ccm_upper = _rational_enclosure(
        assemble_ccm_hypergeometric_lerch(c, N, prec_bits, decimal_enclosure_digits),
        indices,
        decimal_enclosure_digits,
    )
    overlap = _intersection_evidence(
        auxiliary_lower, auxiliary_upper, ccm_lower, ccm_upper
    )
    if (
        not overlap["result"]["all_entries_overlap"]
        or not overlap["result"]["symmetric_intersection_nonempty"]
    ):
        raise ValueError("independent Arb interval matrices do not overlap")
    return {
        "matrices": {
            "auxiliary_s_cc_xc": {
                "enclosure": {
                    "lower": _format_matrix(auxiliary_lower),
                    "upper": _format_matrix(auxiliary_upper),
                }
            },
            "ccm_hypergeometric_lerch": {
                "enclosure": {
                    "lower": _format_matrix(ccm_lower),
                    "upper": _format_matrix(ccm_upper),
                }
            },
        },
        "overlap": {key: value for key, value in overlap.items() if key != "result"},
        "parameters": {
            "N": N,
            "c": c,
            "decimal_enclosure_digits": decimal_enclosure_digits,
            "dimension": 2 * N + 1,
            "index_order": list(indices),
            "prec_bits": prec_bits,
            "python_flint_version": flint_version,
        },
        "result": overlap["result"],
    }


def _canonical_json(value: Mapping[str, Any]) -> str:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
        allow_nan=False,
    )


def _payload_digest(payload: Mapping[str, Any]) -> str:
    return hashlib.sha256(_canonical_json(payload).encode("utf-8")).hexdigest()


def _source_sha256() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def build_overlap_artifact(
    c: int,
    N: int,
    prec_bits: int,
    decimal_enclosure_digits: int,
) -> Dict[str, Any]:
    """Run both Arb routes and build a self-checking overlap artifact."""
    _require_parameters(c, N, prec_bits, decimal_enclosure_digits)
    _arb, _acb, _ctx, flint_version = _flint()
    indices = tuple(range(-N, N + 1))
    auxiliary = assemble_auxiliary_s_cc_xc(
        c, N, prec_bits, decimal_enclosure_digits
    )
    ccm = assemble_ccm_hypergeometric_lerch(
        c, N, prec_bits, decimal_enclosure_digits
    )
    auxiliary_lower, auxiliary_upper = _rational_enclosure(
        auxiliary, indices, decimal_enclosure_digits
    )
    ccm_lower, ccm_upper = _rational_enclosure(
        ccm, indices, decimal_enclosure_digits
    )
    evidence = _intersection_evidence(
        auxiliary_lower, auxiliary_upper, ccm_lower, ccm_upper
    )
    if (
        not evidence["result"]["all_entries_overlap"]
        or not evidence["result"]["symmetric_intersection_nonempty"]
    ):
        raise ValueError("independent Arb interval matrices do not overlap")

    payload = {
        "claim_scope": CLAIM_SCOPE,
        "gate_a_status": GATE_A_STATUS,
        "generator_sha256": _source_sha256(),
        "limitations": LIMITATIONS,
        "matrices": {
            "auxiliary_s_cc_xc": {
                "enclosure": {
                    "lower": _format_matrix(auxiliary_lower),
                    "upper": _format_matrix(auxiliary_upper),
                }
            },
            "ccm_hypergeometric_lerch": {
                "enclosure": {
                    "lower": _format_matrix(ccm_lower),
                    "upper": _format_matrix(ccm_upper),
                }
            },
        },
        "overlap": {
            key: value for key, value in evidence.items() if key != "result"
        },
        "parameters": {
            "N": N,
            "c": c,
            "decimal_enclosure_digits": decimal_enclosure_digits,
            "dimension": 2 * N + 1,
            "index_order": list(indices),
            "prec_bits": prec_bits,
            "python_flint_version": flint_version,
        },
        "result": evidence["result"],
        "routes": ROUTES,
        "schema_version": SCHEMA_VERSION,
        "shared_components": SHARED_COMPONENTS,
        "upstream_script_sha256": UPSTREAM_SCRIPT_SHA256,
    }
    return {**payload, "payload_sha256": _payload_digest(payload)}


def build_cross_precision_overlap_artifact(
    c: int,
    N: int,
    low_prec_bits: int,
    high_prec_bits: int,
    low_decimal_enclosure_digits: int,
    high_decimal_enclosure_digits: int,
) -> Dict[str, Any]:
    """Retain two precision levels and certify exact rational narrowing."""
    _require_parameters(c, N, low_prec_bits, low_decimal_enclosure_digits)
    _require_parameters(c, N, high_prec_bits, high_decimal_enclosure_digits)
    if high_prec_bits < low_prec_bits + 512:
        raise ValueError("high_prec_bits must exceed low_prec_bits by at least 512")
    if high_decimal_enclosure_digits <= low_decimal_enclosure_digits:
        raise ValueError("high_decimal_enclosure_digits must exceed the low precision")
    _arb, _acb, _ctx, flint_version = _flint()
    low = _precision_artifact_evidence(
        c, N, low_prec_bits, low_decimal_enclosure_digits, flint_version
    )
    high = _precision_artifact_evidence(
        c, N, high_prec_bits, high_decimal_enclosure_digits, flint_version
    )

    low_matrices = {
        name: _parse_enclosure(low["matrices"][name]["enclosure"], 2 * N + 1)
        for name in ROUTE_NAMES
    }
    high_matrices = {
        name: _parse_enclosure(high["matrices"][name]["enclosure"], 2 * N + 1)
        for name in ROUTE_NAMES
    }
    if any(value is None for value in (*low_matrices.values(), *high_matrices.values())):
        raise AssertionError("internally produced enclosure did not parse")

    route_comparisons = {
        name: _matrix_comparison_evidence(*low_matrices[name], *high_matrices[name])
        for name in ROUTE_NAMES
    }
    low_intersection = _parse_enclosure(low["overlap"]["intersection"], 2 * N + 1)
    high_intersection = _parse_enclosure(high["overlap"]["intersection"], 2 * N + 1)
    if low_intersection is None or high_intersection is None:
        raise AssertionError("internally produced intersection did not parse")
    intersection_comparison = _matrix_comparison_evidence(
        *low_intersection, *high_intersection
    )
    comparison_result = {
        "all_route_entries_contained": all(
            route_comparisons[name]["result"]["all_entries_contained"]
            for name in ROUTE_NAMES
        ),
        "all_route_entries_strictly_narrower": all(
            route_comparisons[name]["result"]["all_entries_strictly_narrower"]
            for name in ROUTE_NAMES
        ),
        "intersection_entries_contained": intersection_comparison["result"][
            "all_entries_contained"
        ],
        "intersection_entries_strictly_narrower": intersection_comparison["result"][
            "all_entries_strictly_narrower"
        ],
    }
    if not all(comparison_result.values()):
        raise ValueError("second-precision interval narrowing did not hold entrywise")
    payload = {
        "claim_scope": CLAIM_SCOPE,
        "gate_a_status": GATE_A_STATUS,
        "generator_sha256": _source_sha256(),
        "limitations": CROSS_PRECISION_LIMITATIONS,
        "precision_levels": {"low": low, "high": high},
        "precision_narrowing": {
            "intersection": intersection_comparison,
            "routes": route_comparisons,
            "result": comparison_result,
        },
        "routes": ROUTES,
        "schema_version": CROSS_PRECISION_SCHEMA_VERSION,
        "shared_components": SHARED_COMPONENTS,
        "upstream_script_sha256": UPSTREAM_SCRIPT_SHA256,
    }
    return {**payload, "payload_sha256": _payload_digest(payload)}


def write_overlap_artifact(
    path: str | Path,
    c: int,
    N: int,
    prec_bits: int,
    decimal_enclosure_digits: int,
) -> Dict[str, Any]:
    record = build_overlap_artifact(c, N, prec_bits, decimal_enclosure_digits)
    output_path = Path(path)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_bytes((_canonical_json(record) + "\n").encode("ascii"))
    return record


def write_cross_precision_overlap_artifact(
    path: str | Path,
    c: int,
    N: int,
    low_prec_bits: int,
    high_prec_bits: int,
    low_decimal_enclosure_digits: int,
    high_decimal_enclosure_digits: int,
) -> Dict[str, Any]:
    record = build_cross_precision_overlap_artifact(
        c,
        N,
        low_prec_bits,
        high_prec_bits,
        low_decimal_enclosure_digits,
        high_decimal_enclosure_digits,
    )
    output_path = Path(path)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_bytes((_canonical_json(record) + "\n").encode("ascii"))
    return record


def _canonical_fraction(value: Any) -> Fraction | None:
    if not isinstance(value, str):
        return None
    try:
        fraction = Fraction(value)
    except (ValueError, ZeroDivisionError):
        return None
    return fraction if _format_fraction(fraction) == value else None


def _parse_enclosure(
    record: Any, dimension: int
) -> Tuple[FractionMatrix, FractionMatrix] | None:
    if not isinstance(record, dict) or set(record) != {"lower", "upper"}:
        return None
    parsed = []
    for name in ("lower", "upper"):
        rows = record[name]
        if (
            not isinstance(rows, list)
            or len(rows) != dimension
            or any(not isinstance(row, list) or len(row) != dimension for row in rows)
        ):
            return None
        parsed_rows = []
        for row in rows:
            parsed_row = tuple(_canonical_fraction(value) for value in row)
            if any(value is None for value in parsed_row):
                return None
            parsed_rows.append(parsed_row)
        parsed.append(tuple(parsed_rows))
    lower, upper = parsed
    if any(
        lower[i][j] > upper[i][j]
        for i in range(dimension)
        for j in range(dimension)
    ):
        return None
    return lower, upper


def _parse_precision_level(
    record: Any,
) -> Tuple[Dict[str, Any], Dict[str, Tuple[FractionMatrix, FractionMatrix]], Tuple[FractionMatrix, FractionMatrix]] | None:
    """Validate one retained precision level and reconstruct its intervals."""
    if not isinstance(record, dict) or set(record) != {
        "matrices",
        "overlap",
        "parameters",
        "result",
    }:
        return None
    parameters = record["parameters"]
    parameter_keys = {
        "N",
        "c",
        "decimal_enclosure_digits",
        "dimension",
        "index_order",
        "prec_bits",
        "python_flint_version",
    }
    if not isinstance(parameters, dict) or set(parameters) != parameter_keys:
        return None
    integer_parameters = (
        parameters["N"],
        parameters["c"],
        parameters["decimal_enclosure_digits"],
        parameters["dimension"],
        parameters["prec_bits"],
    )
    if any(isinstance(value, bool) or not isinstance(value, int) for value in integer_parameters):
        return None
    try:
        _require_parameters(
            parameters["c"],
            parameters["N"],
            parameters["prec_bits"],
            parameters["decimal_enclosure_digits"],
        )
    except ValueError:
        return None
    dimension = 2 * parameters["N"] + 1
    if (
        parameters["dimension"] != dimension
        or parameters["index_order"] != list(range(-parameters["N"], parameters["N"] + 1))
        or not isinstance(parameters["python_flint_version"], str)
    ):
        return None
    matrices = record["matrices"]
    if not isinstance(matrices, dict) or set(matrices) != set(ROUTE_NAMES):
        return None
    parsed_matrices = {}
    for route_name in ROUTE_NAMES:
        route_record = matrices[route_name]
        if not isinstance(route_record, dict) or set(route_record) != {"enclosure"}:
            return None
        parsed = _parse_enclosure(route_record["enclosure"], dimension)
        if parsed is None:
            return None
        parsed_matrices[route_name] = parsed
    expected = _intersection_evidence(
        *parsed_matrices["auxiliary_s_cc_xc"],
        *parsed_matrices["ccm_hypergeometric_lerch"],
    )
    if (
        record["overlap"] != {key: value for key, value in expected.items() if key != "result"}
        or record["result"] != expected["result"]
        or not expected["result"]["all_entries_overlap"]
        or not expected["result"]["symmetric_intersection_nonempty"]
    ):
        return None
    intersection = _parse_enclosure(record["overlap"]["intersection"], dimension)
    if intersection is None:
        return None
    return parameters, parsed_matrices, intersection


def verify_overlap_artifact(record: Any) -> bool:
    required_keys = {
        "claim_scope",
        "gate_a_status",
        "generator_sha256",
        "limitations",
        "matrices",
        "overlap",
        "parameters",
        "payload_sha256",
        "result",
        "routes",
        "schema_version",
        "shared_components",
        "upstream_script_sha256",
    }
    if not isinstance(record, dict) or set(record) != required_keys:
        return False
    if (
        record["schema_version"] != SCHEMA_VERSION
        or record["claim_scope"] != CLAIM_SCOPE
        or record["gate_a_status"] != GATE_A_STATUS
        or record["routes"] != ROUTES
        or record["shared_components"] != SHARED_COMPONENTS
        or record["limitations"] != LIMITATIONS
        or record["upstream_script_sha256"] != UPSTREAM_SCRIPT_SHA256
        or record["generator_sha256"] != _source_sha256()
        or not isinstance(record["payload_sha256"], str)
    ):
        return False
    payload = {key: value for key, value in record.items() if key != "payload_sha256"}
    try:
        if _payload_digest(payload) != record["payload_sha256"]:
            return False
    except (TypeError, ValueError):
        return False

    parameters = record["parameters"]
    parameter_keys = {
        "N",
        "c",
        "decimal_enclosure_digits",
        "dimension",
        "index_order",
        "prec_bits",
        "python_flint_version",
    }
    if not isinstance(parameters, dict) or set(parameters) != parameter_keys:
        return False
    integer_parameters = (
        parameters["N"],
        parameters["c"],
        parameters["decimal_enclosure_digits"],
        parameters["dimension"],
        parameters["prec_bits"],
    )
    if any(isinstance(value, bool) or not isinstance(value, int) for value in integer_parameters):
        return False
    try:
        _require_parameters(
            parameters["c"],
            parameters["N"],
            parameters["prec_bits"],
            parameters["decimal_enclosure_digits"],
        )
    except ValueError:
        return False
    dimension = 2 * parameters["N"] + 1
    if (
        parameters["dimension"] != dimension
        or parameters["index_order"] != list(range(-parameters["N"], parameters["N"] + 1))
        or not isinstance(parameters["python_flint_version"], str)
    ):
        return False

    matrices = record["matrices"]
    if not isinstance(matrices, dict) or set(matrices) != set(ROUTE_NAMES):
        return False
    parsed_matrices = {}
    for route_name in ROUTE_NAMES:
        route_record = matrices[route_name]
        if not isinstance(route_record, dict) or set(route_record) != {"enclosure"}:
            return False
        parsed = _parse_enclosure(route_record["enclosure"], dimension)
        if parsed is None:
            return False
        parsed_matrices[route_name] = parsed

    expected = _intersection_evidence(
        *parsed_matrices["auxiliary_s_cc_xc"],
        *parsed_matrices["ccm_hypergeometric_lerch"],
    )
    expected_overlap = {
        key: value for key, value in expected.items() if key != "result"
    }
    return (
        record["overlap"] == expected_overlap
        and record["result"] == expected["result"]
        and expected["result"]["all_entries_overlap"] is True
        and expected["result"]["symmetric_intersection_nonempty"] is True
    )


def verify_cross_precision_overlap_artifact(record: Any) -> bool:
    required_keys = {
        "claim_scope",
        "gate_a_status",
        "generator_sha256",
        "limitations",
        "payload_sha256",
        "precision_levels",
        "precision_narrowing",
        "routes",
        "schema_version",
        "shared_components",
        "upstream_script_sha256",
    }
    if not isinstance(record, dict) or set(record) != required_keys:
        return False
    if (
        record["schema_version"] != CROSS_PRECISION_SCHEMA_VERSION
        or record["claim_scope"] != CLAIM_SCOPE
        or record["gate_a_status"] != GATE_A_STATUS
        or record["routes"] != ROUTES
        or record["shared_components"] != SHARED_COMPONENTS
        or record["limitations"] != CROSS_PRECISION_LIMITATIONS
        or record["upstream_script_sha256"] != UPSTREAM_SCRIPT_SHA256
        or record["generator_sha256"] != _source_sha256()
        or not isinstance(record["payload_sha256"], str)
    ):
        return False
    payload = {key: value for key, value in record.items() if key != "payload_sha256"}
    try:
        if _payload_digest(payload) != record["payload_sha256"]:
            return False
    except (TypeError, ValueError):
        return False
    levels = record["precision_levels"]
    if not isinstance(levels, dict) or set(levels) != {"low", "high"}:
        return False
    low = _parse_precision_level(levels["low"])
    high = _parse_precision_level(levels["high"])
    if low is None or high is None:
        return False
    low_parameters, low_matrices, low_intersection = low
    high_parameters, high_matrices, high_intersection = high
    if (
        low_parameters["c"] != high_parameters["c"]
        or low_parameters["N"] != high_parameters["N"]
        or low_parameters["python_flint_version"] != high_parameters["python_flint_version"]
        or high_parameters["prec_bits"] < low_parameters["prec_bits"] + 512
        or high_parameters["decimal_enclosure_digits"] <= low_parameters["decimal_enclosure_digits"]
    ):
        return False
    expected_routes = {
        name: _matrix_comparison_evidence(*low_matrices[name], *high_matrices[name])
        for name in ROUTE_NAMES
    }
    expected_intersection = _matrix_comparison_evidence(
        *low_intersection, *high_intersection
    )
    expected_result = {
        "all_route_entries_contained": all(
            expected_routes[name]["result"]["all_entries_contained"]
            for name in ROUTE_NAMES
        ),
        "all_route_entries_strictly_narrower": all(
            expected_routes[name]["result"]["all_entries_strictly_narrower"]
            for name in ROUTE_NAMES
        ),
        "intersection_entries_contained": expected_intersection["result"][
            "all_entries_contained"
        ],
        "intersection_entries_strictly_narrower": expected_intersection["result"][
            "all_entries_strictly_narrower"
        ],
    }
    expected_narrowing = {
        "intersection": expected_intersection,
        "routes": expected_routes,
        "result": expected_result,
    }
    return record["precision_narrowing"] == expected_narrowing and all(
        expected_result.values()
    )


def verify_overlap_artifact_file(path: str | Path) -> bool:
    try:
        source = Path(path).read_bytes()
        record = json.loads(source, parse_constant=lambda value: (_ for _ in ()).throw(
            ValueError(f"non-finite JSON constant: {value}")
        ))
        canonical = (_canonical_json(record) + "\n").encode("ascii")
    except (OSError, TypeError, UnicodeError, ValueError):
        return False
    return source == canonical and verify_overlap_artifact(record)


def verify_cross_precision_overlap_artifact_file(path: str | Path) -> bool:
    try:
        source = Path(path).read_bytes()
        record = json.loads(source, parse_constant=lambda value: (_ for _ in ()).throw(
            ValueError(f"non-finite JSON constant: {value}")
        ))
        canonical = (_canonical_json(record) + "\n").encode("ascii")
    except (OSError, TypeError, UnicodeError, ValueError):
        return False
    return source == canonical and verify_cross_precision_overlap_artifact(record)


def _generate(args: argparse.Namespace) -> int:
    artifact = write_overlap_artifact(
        args.output,
        args.c,
        args.N,
        args.prec_bits,
        args.decimal_enclosure_digits,
    )
    print(
        "independent small-N Arb intervals overlap entrywise: "
        f"{str(artifact['result']['all_entries_overlap']).lower()}"
    )
    return 0


def _verify(path: Path) -> int:
    valid = verify_overlap_artifact_file(path)
    print(f"valid small-N Arb interval overlap artifact: {str(valid).lower()}")
    return 0 if valid else 1


def _generate_cross_precision(args: argparse.Namespace) -> int:
    artifact = write_cross_precision_overlap_artifact(
        args.output,
        args.c,
        args.N,
        args.low_prec_bits,
        args.high_prec_bits,
        args.low_decimal_enclosure_digits,
        args.high_decimal_enclosure_digits,
    )
    result = artifact["precision_narrowing"]["result"]
    print(
        "independent small-N Arb intervals narrow at second precision: "
        f"{str(all(result.values())).lower()}"
    )
    return 0


def _verify_cross_precision(path: Path) -> int:
    valid = verify_cross_precision_overlap_artifact_file(path)
    print(f"valid small-N Arb cross-precision artifact: {str(valid).lower()}")
    return 0 if valid else 1


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Generate or verify independent small-N Arb Weil intervals."
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    generate_parser = subparsers.add_parser("generate")
    generate_parser.add_argument("output", type=Path)
    generate_parser.add_argument("--c", type=int, default=13)
    generate_parser.add_argument("--N", type=int, default=4)
    generate_parser.add_argument("--prec-bits", type=int, default=384)
    generate_parser.add_argument(
        "--decimal-enclosure-digits", type=int, default=120
    )

    cross_generate_parser = subparsers.add_parser("generate-cross-precision")
    cross_generate_parser.add_argument("output", type=Path)
    cross_generate_parser.add_argument("--c", type=int, default=13)
    cross_generate_parser.add_argument("--N", type=int, default=4)
    cross_generate_parser.add_argument("--low-prec-bits", type=int, default=384)
    cross_generate_parser.add_argument("--high-prec-bits", type=int, default=896)
    cross_generate_parser.add_argument(
        "--low-decimal-enclosure-digits", type=int, default=120
    )
    cross_generate_parser.add_argument(
        "--high-decimal-enclosure-digits", type=int, default=240
    )

    verify_parser = subparsers.add_parser("verify")
    verify_parser.add_argument("artifact", type=Path)

    cross_verify_parser = subparsers.add_parser("verify-cross-precision")
    cross_verify_parser.add_argument("artifact", type=Path)

    args = parser.parse_args(argv)
    if args.command == "generate":
        return _generate(args)
    if args.command == "verify":
        return _verify(args.artifact)
    if args.command == "generate-cross-precision":
        return _generate_cross_precision(args)
    return _verify_cross_precision(args.artifact)


if __name__ == "__main__":
    raise SystemExit(main())
