from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence, Union


SCHEMA_VERSION = "weil-extremal-kernel-ldlt/v1"
CLAIM_SCOPE = "finite-rational-matrix-only"

RationalInput = Union[Fraction, int, str]
Matrix = tuple[tuple[Fraction, ...], ...]


class LDLDecompositionError(ValueError):
    """Raised when exact unpivoted LDL^T encounters a zero-pivot breakdown."""


@dataclass(frozen=True)
class LDLCertificate:
    lower: Matrix
    diagonal: tuple[Fraction, ...]


def _as_fraction(value: RationalInput) -> Fraction:
    if isinstance(value, bool) or isinstance(value, float):
        raise TypeError("rational entries must be Fraction, int, or rational string")
    if isinstance(value, Fraction):
        return value
    if isinstance(value, int):
        return Fraction(value)
    if isinstance(value, str):
        try:
            return Fraction(value)
        except (ValueError, ZeroDivisionError) as error:
            raise ValueError(f"invalid rational string: {value!r}") from error
    raise TypeError("rational entries must be Fraction, int, or rational string")


def fraction_matrix(
    rows: Iterable[Iterable[RationalInput]], *, require_symmetric: bool = True
) -> Matrix:
    matrix = tuple(tuple(_as_fraction(value) for value in row) for row in rows)
    size = len(matrix)
    if any(len(row) != size for row in matrix):
        raise ValueError("matrix must be square")
    if require_symmetric and any(
        matrix[i][j] != matrix[j][i] for i in range(size) for j in range(i)
    ):
        raise ValueError("matrix must be symmetric")
    return matrix


def _fraction_vector(values: Iterable[RationalInput]) -> tuple[Fraction, ...]:
    return tuple(_as_fraction(value) for value in values)


def quadratic_form(matrix: Matrix, vector: Sequence[RationalInput]) -> Fraction:
    checked_matrix = fraction_matrix(matrix)
    checked_vector = _fraction_vector(vector)
    size = len(checked_matrix)
    if len(checked_vector) != size:
        raise ValueError("vector dimension must match matrix dimension")
    return sum(
        (
            checked_vector[i] * checked_matrix[i][j] * checked_vector[j]
            for i in range(size)
            for j in range(size)
        ),
        Fraction(0),
    )


def ldlt_decompose(matrix: Matrix) -> LDLCertificate:
    checked_matrix = fraction_matrix(matrix)
    size = len(checked_matrix)
    lower = [[Fraction(i == j) for j in range(size)] for i in range(size)]
    diagonal: list[Fraction] = []

    for column in range(size):
        pivot = checked_matrix[column][column] - sum(
            (
                lower[column][k] * lower[column][k] * diagonal[k]
                for k in range(column)
            ),
            Fraction(0),
        )
        diagonal.append(pivot)

        for row in range(column + 1, size):
            residual = checked_matrix[row][column] - sum(
                (
                    lower[row][k] * lower[column][k] * diagonal[k]
                    for k in range(column)
                ),
                Fraction(0),
            )
            if pivot == 0:
                if residual != 0:
                    raise LDLDecompositionError(
                        f"zero pivot at index {column} has nonzero residual"
                    )
                lower[row][column] = Fraction(0)
            else:
                lower[row][column] = residual / pivot

    return LDLCertificate(
        lower=tuple(tuple(row) for row in lower),
        diagonal=tuple(diagonal),
    )


def _is_unit_lower_triangular(lower: Matrix) -> bool:
    size = len(lower)
    return all(
        lower[i][j] == (1 if i == j else 0)
        for i in range(size)
        for j in range(i, size)
    )


def verify_ldlt_certificate(
    matrix: Matrix,
    certificate: LDLCertificate,
    *,
    require_nonnegative: bool = True,
) -> bool:
    try:
        checked_matrix = fraction_matrix(matrix)
        lower = fraction_matrix(certificate.lower, require_symmetric=False)
        diagonal = _fraction_vector(certificate.diagonal)
    except (TypeError, ValueError):
        return False

    size = len(checked_matrix)
    if len(lower) != size or len(diagonal) != size:
        return False
    if not _is_unit_lower_triangular(lower):
        return False
    if require_nonnegative and any(value < 0 for value in diagonal):
        return False

    return all(
        checked_matrix[i][j]
        == sum(
            (lower[i][k] * diagonal[k] * lower[j][k] for k in range(size)),
            Fraction(0),
        )
        for i in range(size)
        for j in range(size)
    )


def _format_fraction(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def _format_matrix(matrix: Matrix) -> list[list[str]]:
    return [[_format_fraction(value) for value in row] for row in matrix]


def _canonical_json(value: Mapping[str, Any]) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def _payload_digest(payload: Mapping[str, Any]) -> str:
    return hashlib.sha256(_canonical_json(payload).encode("utf-8")).hexdigest()


def _artifact_payload(
    matrix: Matrix,
    certificate: LDLCertificate,
    parameters: Mapping[str, Any],
) -> dict[str, Any]:
    exact_reconstruction = verify_ldlt_certificate(
        matrix, certificate, require_nonnegative=False
    )
    nonnegative_diagonal = all(value >= 0 for value in certificate.diagonal)
    return {
        "certificate": {
            "diagonal": [_format_fraction(value) for value in certificate.diagonal],
            "lower": _format_matrix(certificate.lower),
        },
        "claim_scope": CLAIM_SCOPE,
        "matrix": _format_matrix(matrix),
        "parameters": dict(parameters),
        "result": {
            "certified_psd": exact_reconstruction and nonnegative_diagonal,
            "exact_reconstruction": exact_reconstruction,
            "nonnegative_diagonal": nonnegative_diagonal,
        },
        "schema_version": SCHEMA_VERSION,
    }


def write_experiment_artifact(
    path: str | Path,
    matrix: Matrix,
    certificate: LDLCertificate,
    *,
    parameters: Mapping[str, Any],
) -> dict[str, Any]:
    checked_matrix = fraction_matrix(matrix)
    payload = _artifact_payload(checked_matrix, certificate, parameters)
    record = {**payload, "payload_sha256": _payload_digest(payload)}
    output_path = Path(path)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(_canonical_json(record) + "\n", encoding="utf-8")
    return record


def load_experiment_artifact(path: str | Path) -> dict[str, Any]:
    record = json.loads(Path(path).read_text(encoding="utf-8"))
    if not isinstance(record, dict):
        raise ValueError("experiment artifact must be a JSON object")
    return record


def _is_canonical_fraction_string(value: Any) -> bool:
    if not isinstance(value, str):
        return False
    try:
        fraction = _as_fraction(value)
    except (TypeError, ValueError):
        return False
    return _format_fraction(fraction) == value


def _all_canonical_fraction_strings(rows: Any) -> bool:
    return isinstance(rows, list) and all(
        isinstance(row, list) and all(_is_canonical_fraction_string(value) for value in row)
        for row in rows
    )


def verify_experiment_artifact(record: Any) -> bool:
    required_keys = {
        "certificate",
        "claim_scope",
        "matrix",
        "parameters",
        "payload_sha256",
        "result",
        "schema_version",
    }
    if not isinstance(record, dict) or set(record) != required_keys:
        return False
    if record["schema_version"] != SCHEMA_VERSION or record["claim_scope"] != CLAIM_SCOPE:
        return False
    if not isinstance(record["parameters"], dict):
        return False
    if not isinstance(record["payload_sha256"], str):
        return False

    payload = {key: value for key, value in record.items() if key != "payload_sha256"}
    if _payload_digest(payload) != record["payload_sha256"]:
        return False

    certificate_record = record["certificate"]
    if not isinstance(certificate_record, dict) or set(certificate_record) != {
        "diagonal",
        "lower",
    }:
        return False
    if not _all_canonical_fraction_strings(record["matrix"]):
        return False
    if not _all_canonical_fraction_strings(certificate_record["lower"]):
        return False
    raw_diagonal = certificate_record["diagonal"]
    if not isinstance(raw_diagonal, list) or not all(
        _is_canonical_fraction_string(value) for value in raw_diagonal
    ):
        return False

    try:
        matrix = fraction_matrix(record["matrix"])
        certificate = LDLCertificate(
            lower=fraction_matrix(certificate_record["lower"], require_symmetric=False),
            diagonal=_fraction_vector(raw_diagonal),
        )
    except (TypeError, ValueError):
        return False

    exact_reconstruction = verify_ldlt_certificate(
        matrix, certificate, require_nonnegative=False
    )
    nonnegative_diagonal = all(value >= 0 for value in certificate.diagonal)
    expected_result = {
        "certified_psd": exact_reconstruction and nonnegative_diagonal,
        "exact_reconstruction": exact_reconstruction,
        "nonnegative_diagonal": nonnegative_diagonal,
    }
    return record["result"] == expected_result


def _certify(input_path: Path, output_path: Path) -> int:
    input_record = json.loads(input_path.read_text(encoding="utf-8"))
    if not isinstance(input_record, dict) or "matrix" not in input_record:
        raise ValueError("input must be a JSON object containing matrix")
    parameters = input_record.get("parameters", {})
    if not isinstance(parameters, dict):
        raise ValueError("parameters must be a JSON object")
    matrix = fraction_matrix(input_record["matrix"])
    certificate = ldlt_decompose(matrix)
    artifact = write_experiment_artifact(
        output_path, matrix, certificate, parameters=parameters
    )
    certified = artifact["result"]["certified_psd"]
    print(f"certified finite rational matrix: {str(certified).lower()}")
    return 0


def _verify(path: Path) -> int:
    valid = verify_experiment_artifact(load_experiment_artifact(path))
    print(f"valid exact LDL^T artifact: {str(valid).lower()}")
    return 0 if valid else 1


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Create and verify exact rational LDL^T artifacts."
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    certify_parser = subparsers.add_parser("certify")
    certify_parser.add_argument("input", type=Path)
    certify_parser.add_argument("output", type=Path)

    verify_parser = subparsers.add_parser("verify")
    verify_parser.add_argument("artifact", type=Path)

    args = parser.parse_args(argv)
    if args.command == "certify":
        return _certify(args.input, args.output)
    return _verify(args.artifact)


if __name__ == "__main__":
    raise SystemExit(main())
