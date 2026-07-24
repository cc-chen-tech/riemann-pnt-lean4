"""Exact sign certificate for the retained small-N Weil interval matrix.

The artifact embeds the two-route, two-precision Arb evidence produced by
``weil_extremal_interval_overlap``.  Generation and verification in this
module use only Python's standard library and exact ``Fraction`` arithmetic.
Arb is needed only to regenerate the embedded source evidence.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path
from typing import Any, Mapping, Sequence

from experiments.rh import weil_extremal_interval_overlap as overlap
from experiments.rh import weil_extremal_kernels as kernels


SCHEMA_VERSION = "weil-extremal-kernel-small-n-interval-sign/v1"
CLAIM_SCOPE = "small-N-finite-interval-matrix-sign-only"
GATE_A_STATUS = "not_satisfied"
CLASSIFICATION = "positive_definite"
FROZEN_CROSS_PRECISION_SHA256 = (
    "5e63562ed160a5d9a4940319ec69b1463a8806c215b9b1623e595ef537d70ec5"
)
LIMITATIONS = [
    "This certificate concerns only the retained c=13, N=4 full 9 x 9 matrix.",
    "It does not assemble or certify the registered c=100, N=200 Gate A matrix.",
    "It transfers the retained finite entry intervals only; no analytic tail or basis-change budget is included.",
    "It is not an analytic transfer theorem and makes no statement about the Riemann Hypothesis.",
    "Payload hashes check internal consistency, not authenticity; independent Arb regeneration is separate evidence.",
]

Matrix = tuple[tuple[Fraction, ...], ...]


def _canonical_json(value: Mapping[str, Any]) -> str:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
        allow_nan=False,
    )


def _payload_digest(payload: Mapping[str, Any]) -> str:
    return hashlib.sha256(_canonical_json(payload).encode("ascii")).hexdigest()


def _record_digest(record: Mapping[str, Any]) -> str:
    return hashlib.sha256((_canonical_json(record) + "\n").encode("ascii")).hexdigest()


def _source_sha256() -> str:
    return hashlib.sha256(Path(__file__).read_bytes()).hexdigest()


def _format_fraction(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def _format_matrix(matrix: Matrix) -> list[list[str]]:
    return [[_format_fraction(value) for value in row] for row in matrix]


def _parse_fraction(value: Any) -> Fraction | None:
    if not isinstance(value, str):
        return None
    try:
        parsed = Fraction(value)
    except (ValueError, ZeroDivisionError):
        return None
    return parsed if _format_fraction(parsed) == value else None


def _parse_matrix(
    value: Any, size: int, *, require_symmetric: bool
) -> Matrix | None:
    if (
        not isinstance(value, list)
        or len(value) != size
        or any(not isinstance(row, list) or len(row) != size for row in value)
    ):
        return None
    parsed_rows = []
    for row in value:
        parsed_row = tuple(_parse_fraction(entry) for entry in row)
        if any(entry is None for entry in parsed_row):
            return None
        parsed_rows.append(parsed_row)
    matrix = tuple(parsed_rows)
    if require_symmetric and any(
        matrix[i][j] != matrix[j][i] for i in range(size) for j in range(i)
    ):
        return None
    return matrix  # type: ignore[return-value]


def _parse_vector(value: Any, size: int) -> tuple[Fraction, ...] | None:
    if not isinstance(value, list) or len(value) != size:
        return None
    parsed = tuple(_parse_fraction(entry) for entry in value)
    if any(entry is None for entry in parsed):
        return None
    return parsed  # type: ignore[return-value]


def _center(enclosure: kernels.RationalIntervalMatrix) -> Matrix:
    size = len(enclosure.lower)
    return tuple(
        tuple(
            (enclosure.lower[i][j] + enclosure.upper[i][j]) / 2
            for j in range(size)
        )
        for i in range(size)
    )


def _matrix_product(left: Matrix, right: Matrix) -> Matrix:
    size = len(left)
    return tuple(
        tuple(
            sum(
                (left[i][k] * right[k][j] for k in range(size)),
                Fraction(0),
            )
            for j in range(size)
        )
        for i in range(size)
    )


def _transpose(matrix: Matrix) -> Matrix:
    size = len(matrix)
    return tuple(tuple(matrix[j][i] for j in range(size)) for i in range(size))


def _is_identity(matrix: Matrix) -> bool:
    size = len(matrix)
    return all(
        matrix[i][j] == (1 if i == j else 0)
        for i in range(size)
        for j in range(size)
    )


def _source_components(
    cross_precision_evidence: Any,
) -> tuple[dict[str, Any], dict[str, Any], kernels.RationalIntervalMatrix] | None:
    if (
        not isinstance(cross_precision_evidence, dict)
        or not overlap.verify_cross_precision_overlap_artifact(
            cross_precision_evidence
        )
        or _record_digest(cross_precision_evidence)
        != FROZEN_CROSS_PRECISION_SHA256
    ):
        return None
    levels = cross_precision_evidence["precision_levels"]
    low = levels["low"]
    high = levels["high"]
    low_parameters = low["parameters"]
    high_parameters = high["parameters"]
    if (
        low_parameters["c"] != 13
        or low_parameters["N"] != 4
        or high_parameters["c"] != 13
        or high_parameters["N"] != 4
        or low_parameters["dimension"] != 9
        or high_parameters["dimension"] != 9
        or low_parameters["decimal_enclosure_digits"] != 120
        or high_parameters["decimal_enclosure_digits"] != 120
        or high_parameters["prec_bits"] - low_parameters["prec_bits"] != 512
    ):
        return None
    intersection = high["overlap"]["intersection"]
    try:
        enclosure = kernels.interval_matrix_from_bounds(
            intersection["lower"], intersection["upper"]
        )
    except (KeyError, TypeError, ValueError):
        return None
    return low_parameters, high_parameters, enclosure


def _artifact_parameters(high_parameters: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "N": high_parameters["N"],
        "c": high_parameters["c"],
        "decimal_enclosure_digits": high_parameters[
            "decimal_enclosure_digits"
        ],
        "dimension": high_parameters["dimension"],
        "index_order": high_parameters["index_order"],
        "prec_bits": high_parameters["prec_bits"],
        "precision_level": "high",
        "python_flint_version": high_parameters["python_flint_version"],
    }


def build_sign_certificate_artifact(
    cross_precision_evidence: Mapping[str, Any],
) -> dict[str, Any]:
    """Build an exact positive-definiteness certificate from verified evidence."""
    source = _source_components(cross_precision_evidence)
    if source is None:
        raise ValueError("invalid c=13, N=4 cross-precision source evidence")
    _low_parameters, high_parameters, enclosure = source
    certificate = kernels.certify_interval_matrix(enclosure)
    if not kernels.verify_interval_matrix_certificate(
        enclosure, certificate, require_positive=True
    ):
        raise ValueError(
            "the retained interval matrix has no strict positive-definiteness certificate"
        )

    center = _center(enclosure)
    exact_reconstruction = kernels.verify_ldlt_certificate(
        center, certificate.ldlt, require_nonnegative=False
    )
    positive_diagonal = all(value > 0 for value in certificate.ldlt.diagonal)
    inverse_identity = _is_identity(
        _matrix_product(
            certificate.inverse_transpose, _transpose(certificate.ldlt.lower)
        )
    )
    strict_margin = (
        certificate.center_lower_bound - certificate.perturbation_row_bound
    )
    finite_interval_transfer_strict = strict_margin > 0
    certified_positive_definite = all(
        (
            exact_reconstruction,
            positive_diagonal,
            inverse_identity,
            finite_interval_transfer_strict,
        )
    )
    if not certified_positive_definite:
        raise AssertionError("internally generated exact certificate did not verify")

    payload = {
        "bounds": {
            "center_lower_bound": _format_fraction(
                certificate.center_lower_bound
            ),
            "perturbation_row_bound": _format_fraction(
                certificate.perturbation_row_bound
            ),
            "strict_margin": _format_fraction(strict_margin),
        },
        "certificate": {
            "diagonal": [
                _format_fraction(value) for value in certificate.ldlt.diagonal
            ],
            "inverse_transpose": _format_matrix(
                certificate.inverse_transpose
            ),
            "lower": _format_matrix(certificate.ldlt.lower),
        },
        "center": _format_matrix(center),
        "claim_scope": CLAIM_SCOPE,
        "classification": CLASSIFICATION,
        "cross_precision_artifact_sha256": _record_digest(
            cross_precision_evidence
        ),
        "cross_precision_evidence": dict(cross_precision_evidence),
        "enclosure": {
            "lower": _format_matrix(enclosure.lower),
            "upper": _format_matrix(enclosure.upper),
        },
        "gate_a_status": GATE_A_STATUS,
        "generator_sha256": _source_sha256(),
        "limitations": LIMITATIONS,
        "parameters": _artifact_parameters(high_parameters),
        "result": {
            "certified_positive_definite": certified_positive_definite,
            "cross_precision_evidence_verified": True,
            "exact_center_reconstruction": exact_reconstruction,
            "finite_interval_transfer_strict": finite_interval_transfer_strict,
            "inverse_transpose_identity": inverse_identity,
            "positive_diagonal": positive_diagonal,
        },
        "schema_version": SCHEMA_VERSION,
    }
    return {**payload, "payload_sha256": _payload_digest(payload)}


def write_sign_certificate_artifact(
    output_path: str | Path, cross_precision_path: str | Path
) -> dict[str, Any]:
    source_path = Path(cross_precision_path)
    if not overlap.verify_cross_precision_overlap_artifact_file(source_path):
        raise ValueError("cross-precision source file is not canonical and valid")
    source_record = json.loads(source_path.read_bytes())
    record = build_sign_certificate_artifact(source_record)
    Path(output_path).write_bytes((_canonical_json(record) + "\n").encode("ascii"))
    return record


def verify_sign_certificate_artifact(record: Any) -> bool:
    required_keys = {
        "bounds",
        "certificate",
        "center",
        "claim_scope",
        "classification",
        "cross_precision_artifact_sha256",
        "cross_precision_evidence",
        "enclosure",
        "gate_a_status",
        "generator_sha256",
        "limitations",
        "parameters",
        "payload_sha256",
        "result",
        "schema_version",
    }
    if not isinstance(record, dict) or set(record) != required_keys:
        return False
    if (
        record["schema_version"] != SCHEMA_VERSION
        or record["claim_scope"] != CLAIM_SCOPE
        or record["classification"] != CLASSIFICATION
        or record["gate_a_status"] != GATE_A_STATUS
        or record["limitations"] != LIMITATIONS
        or record["generator_sha256"] != _source_sha256()
        or not isinstance(record["payload_sha256"], str)
        or not isinstance(record["cross_precision_artifact_sha256"], str)
    ):
        return False
    payload = {key: value for key, value in record.items() if key != "payload_sha256"}
    try:
        if _payload_digest(payload) != record["payload_sha256"]:
            return False
    except (TypeError, ValueError):
        return False

    evidence = record["cross_precision_evidence"]
    source = _source_components(evidence)
    if source is None:
        return False
    _low_parameters, high_parameters, source_enclosure = source
    if (
        _record_digest(evidence) != record["cross_precision_artifact_sha256"]
        or record["parameters"] != _artifact_parameters(high_parameters)
    ):
        return False

    enclosure_record = record["enclosure"]
    if not isinstance(enclosure_record, dict) or set(enclosure_record) != {
        "lower",
        "upper",
    }:
        return False
    size = high_parameters["dimension"]
    lower = _parse_matrix(
        enclosure_record["lower"], size, require_symmetric=True
    )
    upper = _parse_matrix(
        enclosure_record["upper"], size, require_symmetric=True
    )
    if lower is None or upper is None:
        return False
    try:
        enclosure = kernels.interval_matrix_from_bounds(lower, upper)
    except (TypeError, ValueError):
        return False
    if enclosure != source_enclosure:
        return False

    center = _parse_matrix(record["center"], size, require_symmetric=True)
    expected_center = _center(enclosure)
    if center is None or center != expected_center:
        return False

    certificate_record = record["certificate"]
    if not isinstance(certificate_record, dict) or set(certificate_record) != {
        "diagonal",
        "inverse_transpose",
        "lower",
    }:
        return False
    diagonal = _parse_vector(certificate_record["diagonal"], size)
    lower_factor = _parse_matrix(
        certificate_record["lower"], size, require_symmetric=False
    )
    inverse_transpose = _parse_matrix(
        certificate_record["inverse_transpose"],
        size,
        require_symmetric=False,
    )
    if diagonal is None or lower_factor is None or inverse_transpose is None:
        return False
    ldlt = kernels.LDLCertificate(
        lower=lower_factor,
        diagonal=diagonal,
    )

    bounds = record["bounds"]
    if not isinstance(bounds, dict) or set(bounds) != {
        "center_lower_bound",
        "perturbation_row_bound",
        "strict_margin",
    }:
        return False
    center_lower_bound = _parse_fraction(bounds["center_lower_bound"])
    perturbation_row_bound = _parse_fraction(bounds["perturbation_row_bound"])
    strict_margin = _parse_fraction(bounds["strict_margin"])
    if (
        center_lower_bound is None
        or perturbation_row_bound is None
        or strict_margin is None
    ):
        return False
    certificate = kernels.IntervalMatrixCertificate(
        ldlt=ldlt,
        inverse_transpose=inverse_transpose,
        center_lower_bound=center_lower_bound,
        perturbation_row_bound=perturbation_row_bound,
    )

    exact_reconstruction = kernels.verify_ldlt_certificate(
        center, ldlt, require_nonnegative=False
    )
    positive_diagonal = all(value > 0 for value in diagonal)
    inverse_identity = _is_identity(
        _matrix_product(inverse_transpose, _transpose(lower_factor))
    )
    finite_interval_transfer_strict = (
        strict_margin == center_lower_bound - perturbation_row_bound
        and strict_margin > 0
    )
    certified_positive_definite = (
        exact_reconstruction
        and positive_diagonal
        and inverse_identity
        and finite_interval_transfer_strict
        and kernels.verify_interval_matrix_certificate(
            enclosure, certificate, require_positive=True
        )
    )
    result = record["result"]
    result_keys = {
        "certified_positive_definite",
        "cross_precision_evidence_verified",
        "exact_center_reconstruction",
        "finite_interval_transfer_strict",
        "inverse_transpose_identity",
        "positive_diagonal",
    }
    if (
        not isinstance(result, dict)
        or set(result) != result_keys
        or any(type(result[key]) is not bool for key in result_keys)
    ):
        return False
    expected_result = {
        "certified_positive_definite": certified_positive_definite,
        "cross_precision_evidence_verified": True,
        "exact_center_reconstruction": exact_reconstruction,
        "finite_interval_transfer_strict": finite_interval_transfer_strict,
        "inverse_transpose_identity": inverse_identity,
        "positive_diagonal": positive_diagonal,
    }
    return result == expected_result and all(expected_result.values())


def verify_sign_certificate_artifact_file(path: str | Path) -> bool:
    try:
        source = Path(path).read_bytes()
        record = json.loads(
            source,
            parse_constant=lambda value: (_ for _ in ()).throw(
                ValueError(f"non-finite JSON constant: {value}")
            ),
        )
        canonical = (_canonical_json(record) + "\n").encode("ascii")
    except (OSError, TypeError, UnicodeError, ValueError):
        return False
    return source == canonical and verify_sign_certificate_artifact(record)


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Generate or verify the exact small-N Weil interval sign certificate."
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    generate_parser = subparsers.add_parser("generate")
    generate_parser.add_argument("cross_precision_artifact", type=Path)
    generate_parser.add_argument("output", type=Path)

    verify_parser = subparsers.add_parser("verify")
    verify_parser.add_argument("artifact", type=Path)

    args = parser.parse_args(argv)
    if args.command == "generate":
        record = write_sign_certificate_artifact(
            args.output, args.cross_precision_artifact
        )
        valid = record["result"]["certified_positive_definite"]
        print(
            "certified small-N interval matrix positive definite: "
            f"{str(valid).lower()}"
        )
        return 0 if valid else 1

    valid = verify_sign_certificate_artifact_file(args.artifact)
    print(
        "valid small-N exact interval sign certificate: "
        f"{str(valid).lower()}"
    )
    return 0 if valid else 1


if __name__ == "__main__":
    raise SystemExit(main())
