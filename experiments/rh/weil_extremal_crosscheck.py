"""Independent high-precision pointwise cross-check for small Weil blocks.

This module deliberately does not import the released ``arb_ldlt_certify.py``.
It implements two published closed-form descriptions of the same cutoff-free
full matrix: the auxiliary S/CC/XC formula and the CCM
hypergeometric/Lerch formula.  It is a numerical cross-check only; neither
route emits interval enclosures or an LDL certificate.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from decimal import Decimal, InvalidOperation, localcontext
from pathlib import Path
from typing import Any, Dict, Iterable, Mapping, Sequence, Tuple


SCHEMA_VERSION = "weil-extremal-kernel-high-precision-crosscheck/v1"
CLAIM_SCOPE = "high-precision-pointwise-crosscheck-only"
UPSTREAM_SCRIPT_SHA256 = "02462e7f75a601ed8a5cc4d5c22064ece8088140ff45b9a21fd0295162c72039"
COMPARISON_GUARD_DIGITS = 20
SERIALIZED_REAL_DIGITS = 70
PRECISION_AUDIT_GUARD_DIGITS = 10
EXPECTED_LIMITATIONS = (
    "Both routes emit high-precision point values, not outward-rounded interval enclosures.",
    "The comparison does not establish entrywise interval overlap between two rigorous assemblies.",
    "No exact rational LDL artifact or analytic interval-to-rational transfer margin is produced.",
    "The small-N cases do not reproduce the registered c=100, N=200 Gate A target.",
)
EXPECTED_ROUTES = {
    "auxiliary_closed_form": "fresh mpmath S/CC/XC implementation",
    "ccm_hypergeometric_lerch": "fresh mpmath CCM hypergeometric/Lerch implementation",
}

Entry = Tuple[int, int]
NumericMatrix = Dict[Entry, Any]


def _mpmath() -> Any:
    try:
        import mpmath as mp
    except ImportError as error:
        raise RuntimeError(
            "high-precision cross-check requires mpmath; install it in the "
            "interpreter used to execute this module"
        ) from error
    return mp


def _require_parameters(c: int, N: int, dps: int) -> None:
    if isinstance(c, bool) or not isinstance(c, int) or c < 2:
        raise ValueError("c must be an integer at least 2")
    if isinstance(N, bool) or not isinstance(N, int) or N < 0:
        raise ValueError("N must be a nonnegative integer")
    if isinstance(dps, bool) or not isinstance(dps, int) or dps < 30:
        raise ValueError("dps must be an integer at least 30")


def prime_powers_up_to(c: int) -> Tuple[Tuple[int, int], ...]:
    """Return ``(q, p)`` for every prime power ``q = p^a <= c``."""
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


def _geometric_sums(mp: Any, n: int, L: Any, dps: int) -> Tuple[Any, Any, Any, Any]:
    """Numerically sum the four exponentially convergent geometric tails."""
    pi = mp.pi
    w = 2 * pi * n / L
    w_squared = w * w
    sums = [mp.mpf("0") for _ in range(4)]
    target = mp.power(10, -(dps + 20))
    for k in range(10000):
        c_k = 2 * k + mp.mpf("0.5")
        exponential = mp.exp(-c_k * L)
        denominator = c_k * c_k + w_squared
        sums[0] += exponential / denominator
        if n:
            sums[1] += exponential * w_squared / (c_k * denominator)
        sums[2] += exponential * c_k / denominator
        sums[3] += exponential * (c_k * c_k - w_squared) / (denominator * denominator)
        if k > 2 and exponential < target:
            return tuple(sums)
    raise RuntimeError("geometric sums did not reach the requested numerical target")


def assemble_auxiliary_closed_form(c: int, N: int, dps: int) -> NumericMatrix:
    """Assemble all full-matrix entries through S/CC/XC closed forms.

    This is a fresh mpmath implementation of the formula used by the published
    Arb route; it is intentionally not an interval computation and does not
    import or call the released script.
    """
    _require_parameters(c, N, dps)
    mp = _mpmath()
    with mp.workdps(dps):
        L = mp.log(c)
        pi = mp.pi
        quarter = mp.mpf("0.25")
        psi_quarter = mp.digamma(quarter)
        s_values = []
        cc_values = []
        xc_values = []
        for n in range(N + 1):
            w = 2 * pi * n / L
            argument = quarter + 1j * pi * n / L
            psi = mp.digamma(argument)
            trigamma = mp.polygamma(1, argument)
            g_s, g_cc, g_xc1, g_xc2 = _geometric_sums(mp, n, L, dps)
            if n:
                s_values.append(mp.im(psi) / 2 - w * g_s)
                cc_values.append(-(mp.re(psi) - psi_quarter) / 2 + g_cc)
            else:
                s_values.append(mp.mpf("0"))
                cc_values.append(mp.mpf("0"))
            xc_values.append(mp.re(trigamma) / 4 - L * g_xc1 - g_xc2)

        def signed_s(index: int) -> Any:
            return s_values[index] if index >= 0 else -s_values[-index]

        u = mp.exp(L / 2)
        J = -2 * mp.log(u + 1) + mp.log(u * u + 1) + 2 * mp.atan(u)
        J += mp.log(2) - pi / 2
        kappa = mp.log(4 * pi * (mp.exp(L) - 1) / (mp.exp(L) + 1)) + mp.euler
        prime_powers = prime_powers_up_to(c)
        weights = [mp.log(p) / mp.sqrt(q) for q, p in prime_powers]
        positions = [mp.log(q) for q, _ in prime_powers]

        entries = {}
        L_squared = L * L
        pi_factor = 16 * pi * pi
        pole_prefactor = 32 * L * mp.sinh(L / 4) ** 2
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
                    archimedean = (signed_s(m) - signed_s(n)) / (pi * (n - m))
                prime = mp.fsum(
                    weight
                    * (
                        2 * (1 - position / L) * mp.cos(2 * pi * n * position / L)
                        if n == m
                        else (
                            mp.sin(2 * pi * m * position / L)
                            - mp.sin(2 * pi * n * position / L)
                        )
                        / (pi * (n - m))
                    )
                    for weight, position in zip(weights, positions)
                )
                entries[(n, m)] = pole - archimedean - prime
        return entries


def assemble_ccm_closed_form(c: int, N: int, dps: int) -> NumericMatrix:
    """Assemble all full entries from the CCM hypergeometric/Lerch formula."""
    _require_parameters(c, N, dps)
    mp = _mpmath()
    with mp.workdps(dps):
        L = mp.log(c)
        pi = mp.pi
        z = mp.exp(-2 * L)
        quarter = mp.mpf("0.25")
        prime_powers = prime_powers_up_to(c)

        def argument(n: int) -> Any:
            return quarter + pi * 1j * n / L

        def hypergeometric(n: int) -> Any:
            a_n = argument(n)
            return mp.hyp2f1(1, a_n, a_n + 1, z)

        def alpha(n: int) -> Any:
            return (
                mp.exp(-L / 2)
                * mp.im(2 * L * hypergeometric(n) / (L + 4 * pi * 1j * n))
                + mp.im(mp.digamma(argument(n))) / 2
            ) / pi

        def beta(n: int) -> Any:
            a_n = argument(n)
            first = -L * mp.exp(-L / 2) * mp.im(
                2 * L * hypergeometric(n) / (4 * pi * n - 1j * L)
            )
            second = -mp.exp(-L / 2) * mp.re(mp.lerchphi(z, 2, a_n)) / 4
            third = mp.re(mp.polygamma(1, a_n)) / 4
            return (first + second + third) / L

        c_w = mp.log((mp.exp(L / 2) - 1) / (mp.exp(L / 2) + 1)) / 2
        c_w += mp.atan(mp.exp(L / 2)) - pi / 4 + mp.euler / 2 + mp.log(8 * pi) / 2

        def gamma(n: int) -> Any:
            first = -mp.exp(-L / 2) * mp.re(
                2 * L * hypergeometric(n) / (L + 4 * pi * 1j * n)
            )
            second = 2 * mp.exp(-L / 2) * mp.hyp2f1(quarter, 1, quarter + 1, z)
            third = -(mp.re(mp.digamma(argument(n))) - mp.digamma(quarter)) / 2
            return first + second + third + c_w

        def prime_value(n: int) -> Any:
            return -mp.fsum(
                mp.log(p)
                * mp.sin(2 * pi * n * (1 - mp.log(q) / L))
                / (pi * mp.sqrt(q))
                for q, p in prime_powers
            )

        def prime_derivative(n: int) -> Any:
            return -2 * mp.fsum(
                mp.log(p)
                * (1 - mp.log(q) / L)
                * mp.cos(2 * pi * n * (1 - mp.log(q) / L))
                / mp.sqrt(q)
                for q, p in prime_powers
            )

        p0 = {n: alpha(n) + prime_value(n) for n in range(-N, N + 1)}
        p0_derivative = {
            n: -2 * (gamma(n) - beta(n)) + prime_derivative(n)
            for n in range(-N, N + 1)
        }

        def pole_c(n: int) -> Any:
            return mp.sinh(L / 4) / mp.sqrt(L) / (quarter + (2 * pi * n / L) ** 2)

        def pole_s(n: int) -> Any:
            return (
                4
                * pi
                * mp.sinh(L / 4)
                * n
                / (L * mp.sqrt(L) * (quarter + (2 * pi * n / L) ** 2))
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


def _format_real(
    mp: Any, value: Any, digits: int = SERIALIZED_REAL_DIGITS
) -> str:
    if not mp.isfinite(value):
        raise ValueError("cross-check produced a non-finite value")
    return mp.nstr(value, digits, strip_zeros=False)


def _max_difference(left: NumericMatrix, right: NumericMatrix) -> Tuple[Entry, Any]:
    if set(left) != set(right):
        raise ValueError("matrix entries do not have the same index set")
    return max(((entry, abs(left[entry] - right[entry])) for entry in left), key=lambda row: row[1])


def compare_all_entries(c: int, N: int, low_dps: int, high_dps: int) -> Dict[str, Any]:
    """Return an all-entry, two-precision numerical comparison record."""
    _require_parameters(c, N, low_dps)
    _require_parameters(c, N, high_dps)
    if high_dps <= low_dps:
        raise ValueError("high_dps must exceed low_dps")
    mp = _mpmath()
    comparison_dps = high_dps + COMPARISON_GUARD_DIGITS
    precision_audit_digits = high_dps + PRECISION_AUDIT_GUARD_DIGITS
    with mp.workdps(comparison_dps):
        auxiliary_low = assemble_auxiliary_closed_form(c, N, low_dps)
        ccm_low = assemble_ccm_closed_form(c, N, low_dps)
        auxiliary_high = assemble_auxiliary_closed_form(c, N, high_dps)
        ccm_high = assemble_ccm_closed_form(c, N, high_dps)
        max_route_entry, max_route_difference = _max_difference(
            auxiliary_high, ccm_high
        )
        max_auxiliary_entry, max_auxiliary_precision_difference = _max_difference(
            auxiliary_low, auxiliary_high
        )
        max_ccm_entry, max_ccm_precision_difference = _max_difference(
            ccm_low, ccm_high
        )
        tolerance_exponent = low_dps - 20
        tolerance = mp.power(10, -tolerance_exponent)
        entries = []
        for i in range(-N, N + 1):
            for j in range(-N, N + 1):
                auxiliary_precision_difference = abs(
                    auxiliary_low[(i, j)] - auxiliary_high[(i, j)]
                )
                ccm_precision_difference = abs(
                    ccm_low[(i, j)] - ccm_high[(i, j)]
                )
                entries.append(
                    {
                        "auxiliary_closed_form": _format_real(
                            mp, auxiliary_high[(i, j)]
                        ),
                        "auxiliary_closed_form_high_precision_audit": _format_real(
                            mp,
                            auxiliary_high[(i, j)],
                            precision_audit_digits,
                        ),
                        "auxiliary_closed_form_low_precision_audit": _format_real(
                            mp,
                            auxiliary_low[(i, j)],
                            precision_audit_digits,
                        ),
                        "auxiliary_low_to_high_difference": _format_real(
                            mp, auxiliary_precision_difference
                        ),
                        "ccm_hypergeometric_lerch": _format_real(
                            mp, ccm_high[(i, j)]
                        ),
                        "ccm_hypergeometric_lerch_high_precision_audit": _format_real(
                            mp,
                            ccm_high[(i, j)],
                            precision_audit_digits,
                        ),
                        "ccm_hypergeometric_lerch_low_precision_audit": _format_real(
                            mp,
                            ccm_low[(i, j)],
                            precision_audit_digits,
                        ),
                        "ccm_low_to_high_difference": _format_real(
                            mp, ccm_precision_difference
                        ),
                        "i": i,
                        "j": j,
                        "absolute_difference": _format_real(
                            mp, abs(auxiliary_high[(i, j)] - ccm_high[(i, j)])
                        ),
                    }
                )
        return {
            "N": N,
            "all_entries_compared": True,
            "c": c,
            "comparison_dps": comparison_dps,
            "dimension": 2 * N + 1,
            "entries": entries,
            "entry_count": len(entries),
            "high_dps": high_dps,
            "low_dps": low_dps,
            "max_abs_auxiliary_low_to_high": {
                "entry": list(max_auxiliary_entry),
                "value": _format_real(mp, max_auxiliary_precision_difference),
            },
            "max_abs_ccm_low_to_high": {
                "entry": list(max_ccm_entry),
                "value": _format_real(mp, max_ccm_precision_difference),
            },
            "max_abs_route_difference_high": {
                "entry": list(max_route_entry),
                "value": _format_real(mp, max_route_difference),
            },
            "numerical_tolerance": _format_real(mp, tolerance),
            "passes_numerical_tolerance": bool(
                max_route_difference < tolerance
                and max_auxiliary_precision_difference < tolerance
                and max_ccm_precision_difference < tolerance
            ),
            "precision_audit_digits": precision_audit_digits,
        }


def _canonical_json(value: Mapping[str, Any]) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def _payload_digest(payload: Mapping[str, Any]) -> str:
    return hashlib.sha256(_canonical_json(payload).encode("utf-8")).hexdigest()


def _artifact_from_case_records(case_records: Sequence[Dict[str, Any]]) -> Dict[str, Any]:
    payload = {
        "cases": case_records,
        "claim_scope": CLAIM_SCOPE,
        "gate_a_status": "not_satisfied",
        "limitations": list(EXPECTED_LIMITATIONS),
        "routes": dict(EXPECTED_ROUTES),
        "schema_version": SCHEMA_VERSION,
        "upstream_script_sha256": UPSTREAM_SCRIPT_SHA256,
    }
    return {**payload, "payload_sha256": _payload_digest(payload)}


def build_crosscheck_artifact(cases: Iterable[Tuple[int, int]], low_dps: int, high_dps: int) -> Dict[str, Any]:
    case_records = [compare_all_entries(c, N, low_dps, high_dps) for c, N in cases]
    return _artifact_from_case_records(case_records)


def write_crosscheck_artifact(
    path: str | Path, cases: Iterable[Tuple[int, int]], low_dps: int, high_dps: int
) -> Dict[str, Any]:
    record = build_crosscheck_artifact(cases, low_dps, high_dps)
    output_path = Path(path)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_bytes((_canonical_json(record) + "\n").encode("utf-8"))
    return record


def append_crosscheck_cases(
    path: str | Path, cases: Iterable[Tuple[int, int]], low_dps: int, high_dps: int
) -> Dict[str, Any]:
    """Append bounded runs to an existing, valid artifact and rehash it."""
    output_path = Path(path)
    existing = json.loads(output_path.read_bytes())
    if not verify_crosscheck_artifact(existing):
        raise ValueError("cannot append to an invalid cross-check artifact")
    existing_cases = existing["cases"]
    existing_pairs = {(case["c"], case["N"]) for case in existing_cases}
    appended = [compare_all_entries(c, N, low_dps, high_dps) for c, N in cases]
    appended_pairs = {(case["c"], case["N"]) for case in appended}
    if len(appended_pairs) != len(appended) or existing_pairs & appended_pairs:
        raise ValueError("each artifact case must have a unique (c, N) pair")
    record = _artifact_from_case_records([*existing_cases, *appended])
    output_path.write_bytes((_canonical_json(record) + "\n").encode("utf-8"))
    return record


def _is_decimal_string(value: Any) -> bool:
    if not isinstance(value, str):
        return False
    try:
        return Decimal(value).is_finite()
    except (InvalidOperation, ValueError):
        return False


def _decimal(value: Any) -> Decimal | None:
    if not isinstance(value, str):
        return None
    try:
        parsed = Decimal(value)
    except (InvalidOperation, ValueError):
        return None
    return parsed if parsed.is_finite() else None


def _serialization_rounding_radius(value: Decimal, digits: int) -> Decimal:
    """Return half an ulp at the requested significant-digit scale."""
    if value.is_zero():
        return Decimal(0)
    return Decimal(5).scaleb(value.adjusted() - digits)


def _serialized_difference_is_consistent(
    left: Decimal,
    right: Decimal,
    recorded_difference: Decimal,
    *,
    value_digits: int = SERIALIZED_REAL_DIGITS,
    difference_digits: int = SERIALIZED_REAL_DIGITS,
) -> bool:
    with localcontext() as context:
        context.prec = 3 * max(value_digits, difference_digits) + 20
        residual = abs(abs(left - right) - recorded_difference)
        rounding_budget = (
            _serialization_rounding_radius(left, value_digits)
            + _serialization_rounding_radius(right, value_digits)
            + _serialization_rounding_radius(
                recorded_difference, difference_digits
            )
        )
        return residual <= rounding_budget


def verify_crosscheck_artifact(record: Any) -> bool:
    required_keys = {
        "cases",
        "claim_scope",
        "gate_a_status",
        "limitations",
        "payload_sha256",
        "routes",
        "schema_version",
        "upstream_script_sha256",
    }
    if not isinstance(record, dict) or set(record) != required_keys:
        return False
    if (
        record["schema_version"] != SCHEMA_VERSION
        or record["claim_scope"] != CLAIM_SCOPE
        or record["gate_a_status"] != "not_satisfied"
        or record["upstream_script_sha256"] != UPSTREAM_SCRIPT_SHA256
        or not isinstance(record["payload_sha256"], str)
        or not isinstance(record["cases"], list)
        or not record["cases"]
        or record["limitations"] != list(EXPECTED_LIMITATIONS)
        or record["routes"] != EXPECTED_ROUTES
    ):
        return False
    payload = {key: value for key, value in record.items() if key != "payload_sha256"}
    if _payload_digest(payload) != record["payload_sha256"]:
        return False
    seen_cases = set()
    for case in record["cases"]:
        required_case_keys = {
            "N",
            "all_entries_compared",
            "c",
            "comparison_dps",
            "dimension",
            "entries",
            "entry_count",
            "high_dps",
            "low_dps",
            "max_abs_auxiliary_low_to_high",
            "max_abs_ccm_low_to_high",
            "max_abs_route_difference_high",
            "numerical_tolerance",
            "passes_numerical_tolerance",
            "precision_audit_digits",
        }
        if not isinstance(case, dict) or set(case) != required_case_keys:
            return False
        if (
            type(case["c"]) is not int
            or type(case["N"]) is not int
            or type(case["low_dps"]) is not int
            or type(case["high_dps"]) is not int
            or type(case["comparison_dps"]) is not int
            or type(case["dimension"]) is not int
            or type(case["entry_count"]) is not int
            or type(case["precision_audit_digits"]) is not int
            or not isinstance(case["entries"], list)
            or case["c"] < 2
            or case["N"] < 0
            or case["low_dps"] < 30
            or case["dimension"] != 2 * case["N"] + 1
            or case["entry_count"] != case["dimension"] ** 2
            or len(case["entries"]) != case["entry_count"]
            or case["high_dps"] <= case["low_dps"]
            or case["comparison_dps"]
            != case["high_dps"] + COMPARISON_GUARD_DIGITS
            or case["precision_audit_digits"]
            != case["high_dps"] + PRECISION_AUDIT_GUARD_DIGITS
            or case["all_entries_compared"] is not True
            or type(case["passes_numerical_tolerance"]) is not bool
        ):
            return False
        case_key = (case["c"], case["N"])
        if case_key in seen_cases:
            return False
        seen_cases.add(case_key)
        tolerance = _decimal(case["numerical_tolerance"])
        expected_tolerance = Decimal(1).scaleb(20 - case["low_dps"])
        if tolerance is None or tolerance <= 0 or tolerance != expected_tolerance:
            return False
        expected_entries = {
            (i, j)
            for i in range(-case["N"], case["N"] + 1)
            for j in range(-case["N"], case["N"] + 1)
        }
        seen_entries = set()
        entry_diagnostics = {}
        for entry in case["entries"]:
            if not isinstance(entry, dict) or set(entry) != {
                "absolute_difference",
                "auxiliary_closed_form",
                "auxiliary_closed_form_high_precision_audit",
                "auxiliary_closed_form_low_precision_audit",
                "auxiliary_low_to_high_difference",
                "ccm_hypergeometric_lerch",
                "ccm_hypergeometric_lerch_high_precision_audit",
                "ccm_hypergeometric_lerch_low_precision_audit",
                "ccm_low_to_high_difference",
                "i",
                "j",
            }:
                return False
            if type(entry["i"]) is not int or type(entry["j"]) is not int:
                return False
            decimal_fields = (
                "absolute_difference",
                "auxiliary_closed_form",
                "auxiliary_closed_form_high_precision_audit",
                "auxiliary_closed_form_low_precision_audit",
                "auxiliary_low_to_high_difference",
                "ccm_hypergeometric_lerch",
                "ccm_hypergeometric_lerch_high_precision_audit",
                "ccm_hypergeometric_lerch_low_precision_audit",
                "ccm_low_to_high_difference",
            )
            if not all(_is_decimal_string(entry[key]) for key in decimal_fields):
                return False
            index = (entry["i"], entry["j"])
            seen_entries.add(index)
            diagnostics = {
                key: _decimal(entry[key])
                for key in (
                    "absolute_difference",
                    "auxiliary_low_to_high_difference",
                    "ccm_low_to_high_difference",
                )
            }
            if any(value is None or value < 0 for value in diagnostics.values()):
                return False
            auxiliary_value = _decimal(entry["auxiliary_closed_form"])
            ccm_value = _decimal(entry["ccm_hypergeometric_lerch"])
            if (
                auxiliary_value is None
                or ccm_value is None
                or not _serialized_difference_is_consistent(
                    auxiliary_value,
                    ccm_value,
                    diagnostics["absolute_difference"],
                )
            ):
                return False
            auxiliary_low = _decimal(
                entry["auxiliary_closed_form_low_precision_audit"]
            )
            auxiliary_high = _decimal(
                entry["auxiliary_closed_form_high_precision_audit"]
            )
            ccm_low = _decimal(
                entry["ccm_hypergeometric_lerch_low_precision_audit"]
            )
            ccm_high = _decimal(
                entry["ccm_hypergeometric_lerch_high_precision_audit"]
            )
            audit_digits = case["precision_audit_digits"]
            if (
                auxiliary_low is None
                or auxiliary_high is None
                or ccm_low is None
                or ccm_high is None
                or not _serialized_difference_is_consistent(
                    auxiliary_low,
                    auxiliary_high,
                    diagnostics["auxiliary_low_to_high_difference"],
                    value_digits=audit_digits,
                )
                or not _serialized_difference_is_consistent(
                    ccm_low,
                    ccm_high,
                    diagnostics["ccm_low_to_high_difference"],
                    value_digits=audit_digits,
                )
            ):
                return False
            entry_diagnostics[index] = diagnostics
        if seen_entries != expected_entries:
            return False
        maximum_fields = {
            "max_abs_auxiliary_low_to_high": "auxiliary_low_to_high_difference",
            "max_abs_ccm_low_to_high": "ccm_low_to_high_difference",
            "max_abs_route_difference_high": "absolute_difference",
        }
        actual_maxima = []
        for maximum_key, diagnostic_key in maximum_fields.items():
            maximum = case[maximum_key]
            if (
                not isinstance(maximum, dict)
                or set(maximum) != {"entry", "value"}
                or not isinstance(maximum["entry"], list)
                or len(maximum["entry"]) != 2
                or not all(type(value) is int for value in maximum["entry"])
                or tuple(maximum["entry"]) not in expected_entries
                or not _is_decimal_string(maximum["value"])
            ):
                return False
            maximum_value = _decimal(maximum["value"])
            actual_maximum = max(
                diagnostics[diagnostic_key]
                for diagnostics in entry_diagnostics.values()
            )
            maximum_entry = tuple(maximum["entry"])
            if (
                maximum_value is None
                or maximum_value < 0
                or maximum_value != actual_maximum
                or entry_diagnostics[maximum_entry][diagnostic_key]
                != actual_maximum
            ):
                return False
            actual_maxima.append(actual_maximum)
        expected_pass = all(maximum < tolerance for maximum in actual_maxima)
        if case["passes_numerical_tolerance"] is not expected_pass:
            return False
    return True


def verify_crosscheck_artifact_file(path: str | Path) -> bool:
    try:
        source = Path(path).read_bytes()
        record = json.loads(source)
        canonical = (_canonical_json(record) + "\n").encode("utf-8")
    except (OSError, TypeError, UnicodeError, ValueError):
        return False
    return source == canonical and verify_crosscheck_artifact(record)


def _parse_case(value: str) -> Tuple[int, int]:
    try:
        c_text, n_text = value.split(":", 1)
        c, N = int(c_text), int(n_text)
    except ValueError as error:
        raise argparse.ArgumentTypeError("cases must use c:N, for example 13:4") from error
    try:
        _require_parameters(c, N, 30)
    except ValueError as error:
        raise argparse.ArgumentTypeError(str(error)) from error
    return c, N


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Cross-check small cutoff-free Weil matrices without importing upstream assembly code."
    )
    parser.add_argument("--case", action="append", type=_parse_case, required=True)
    parser.add_argument("--low-dps", type=int, default=100)
    parser.add_argument("--high-dps", type=int, default=160)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument(
        "--append",
        action="store_true",
        help="append bounded cases to an existing verified artifact and rehash it",
    )
    args = parser.parse_args(argv)
    if args.append:
        record = append_crosscheck_cases(
            args.output, args.case, args.low_dps, args.high_dps
        )
    else:
        record = write_crosscheck_artifact(
            args.output, args.case, args.low_dps, args.high_dps
        )
    if not all(case["passes_numerical_tolerance"] for case in record["cases"]):
        print("high-precision pointwise cross-check: failed numerical tolerance")
        return 1
    print("high-precision pointwise cross-check: passed (not a Gate A interval certificate)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
