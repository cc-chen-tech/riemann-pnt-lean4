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
INTERVAL_SCHEMA_VERSION = "weil-extremal-kernel-interval-ldlt/v1"
INTERVAL_CLAIM_SCOPE = "finite-rational-interval-matrix-only"

RationalInput = Union[Fraction, int, str]
Matrix = tuple[tuple[Fraction, ...], ...]


class LDLDecompositionError(ValueError):
    """Raised when exact unpivoted LDL^T encounters a zero-pivot breakdown."""


@dataclass(frozen=True)
class LDLCertificate:
    lower: Matrix
    diagonal: tuple[Fraction, ...]


@dataclass(frozen=True)
class RationalIntervalMatrix:
    lower: Matrix
    upper: Matrix


@dataclass(frozen=True)
class IntervalMatrixCertificate:
    ldlt: LDLCertificate
    inverse_transpose: Matrix
    center_lower_bound: Fraction
    perturbation_row_bound: Fraction


@dataclass(frozen=True)
class FiniteDictionaryDimensions:
    fourier_cutoff: int
    full_dimension: int
    even_sector_dimension: int


def finite_dictionary_dimensions(N: int) -> FiniteDictionaryDimensions:
    """Return the full and even-sector sizes for Fourier indices -N,...,N."""
    if isinstance(N, bool) or not isinstance(N, int) or N < 0:
        raise ValueError("N must be a nonnegative integer")
    return FiniteDictionaryDimensions(
        fourier_cutoff=N,
        full_dimension=2 * N + 1,
        even_sector_dimension=N + 1,
    )


def _is_plain_int(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool)


def verify_groskin_provenance_metadata(
    record: Any, *, expected_c: int, expected_N: int
) -> bool:
    """Check only the dimensional and inertia metadata of the released audit.

    This does not replay matrix assembly, interval arithmetic, or LDL^T.
    """
    try:
        dimensions = finite_dictionary_dimensions(expected_N)
    except ValueError:
        return False
    if not isinstance(record, dict):
        return False
    integer_fields = ("c", "N", "dimension", "prec_bits", "n_pos", "n_neg")
    if any(not _is_plain_int(record.get(field)) for field in integer_fields):
        return False
    return (
        record.get("script") == "arb_ldlt_certify.py"
        and record["c"] == expected_c
        and record["N"] == expected_N
        and record["dimension"] == dimensions.full_dimension
        and record["prec_bits"] > 0
        and record["n_pos"] == dimensions.full_dimension
        and record["n_neg"] == 0
        and record.get("undetermined_pivot") is None
        and record.get("certified_positive_definite") is True
    )


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


def _named_rows(rows: Iterable[Iterable[RationalInput]], name: str) -> Matrix:
    try:
        return tuple(tuple(_as_fraction(value) for value in row) for row in rows)
    except (TypeError, ValueError) as error:
        raise type(error)(f"invalid {name}: {error}") from error


def _require_square(matrix: Matrix, name: str) -> None:
    if not matrix or any(len(row) != len(matrix) for row in matrix):
        raise ValueError(f"{name} must be a nonempty square matrix")


def _require_symmetric(matrix: Matrix, name: str) -> None:
    size = len(matrix)
    if any(matrix[i][j] != matrix[j][i] for i in range(size) for j in range(i)):
        raise ValueError(f"{name} must be symmetric")


def interval_matrix_from_bounds(
    lower: Iterable[Iterable[RationalInput]],
    upper: Iterable[Iterable[RationalInput]],
) -> RationalIntervalMatrix:
    checked_lower = _named_rows(lower, "lower bound")
    checked_upper = _named_rows(upper, "upper bound")
    if len(checked_lower) != len(checked_upper) or any(
        len(lower_row) != len(upper_row)
        for lower_row, upper_row in zip(checked_lower, checked_upper)
    ):
        raise ValueError("lower and upper bounds must have the same shape and be nonempty")
    _require_square(checked_lower, "lower bound")
    _require_square(checked_upper, "upper bound")
    _require_symmetric(checked_lower, "lower bound")
    _require_symmetric(checked_upper, "upper bound")
    size = len(checked_lower)
    if any(
        checked_lower[i][j] > checked_upper[i][j]
        for i in range(size)
        for j in range(size)
    ):
        raise ValueError("every lower bound must be at most its upper bound")
    return RationalIntervalMatrix(lower=checked_lower, upper=checked_upper)


def interval_matrix_from_center_radius(
    center: Iterable[Iterable[RationalInput]],
    radius: Iterable[Iterable[RationalInput]],
) -> RationalIntervalMatrix:
    checked_center = _named_rows(center, "center")
    checked_radius = _named_rows(radius, "radius")
    if len(checked_center) != len(checked_radius) or any(
        len(center_row) != len(radius_row)
        for center_row, radius_row in zip(checked_center, checked_radius)
    ):
        raise ValueError("center and radius must have the same shape and be nonempty")
    _require_square(checked_center, "center")
    _require_square(checked_radius, "radius")
    _require_symmetric(checked_center, "center")
    _require_symmetric(checked_radius, "radius")
    size = len(checked_center)
    if any(checked_radius[i][j] < 0 for i in range(size) for j in range(size)):
        raise ValueError("radius entries must be nonnegative")
    lower = tuple(
        tuple(checked_center[i][j] - checked_radius[i][j] for j in range(size))
        for i in range(size)
    )
    upper = tuple(
        tuple(checked_center[i][j] + checked_radius[i][j] for j in range(size))
        for i in range(size)
    )
    return RationalIntervalMatrix(lower=lower, upper=upper)


def _interval_center(enclosure: RationalIntervalMatrix) -> Matrix:
    size = len(enclosure.lower)
    return tuple(
        tuple((enclosure.lower[i][j] + enclosure.upper[i][j]) / 2 for j in range(size))
        for i in range(size)
    )


def _interval_radius(enclosure: RationalIntervalMatrix) -> Matrix:
    size = len(enclosure.lower)
    return tuple(
        tuple((enclosure.upper[i][j] - enclosure.lower[i][j]) / 2 for j in range(size))
        for i in range(size)
    )


def _transpose(matrix: Matrix) -> Matrix:
    size = len(matrix)
    return tuple(tuple(matrix[j][i] for j in range(size)) for i in range(size))


def _invert_matrix(matrix: Matrix) -> Matrix:
    checked = fraction_matrix(matrix, require_symmetric=False)
    size = len(checked)
    augmented = [
        list(checked[i]) + [Fraction(i == j) for j in range(size)]
        for i in range(size)
    ]
    for column in range(size):
        pivot_row = next(
            (row for row in range(column, size) if augmented[row][column] != 0),
            None,
        )
        if pivot_row is None:
            raise ValueError("matrix is singular")
        augmented[column], augmented[pivot_row] = (
            augmented[pivot_row],
            augmented[column],
        )
        pivot = augmented[column][column]
        augmented[column] = [value / pivot for value in augmented[column]]
        for row in range(size):
            if row == column:
                continue
            multiplier = augmented[row][column]
            augmented[row] = [
                augmented[row][entry] - multiplier * augmented[column][entry]
                for entry in range(2 * size)
            ]
    return tuple(tuple(row[size:]) for row in augmented)


def _matrix_product(left: Matrix, right: Matrix) -> Matrix:
    size = len(left)
    return tuple(
        tuple(
            sum((left[i][k] * right[k][j] for k in range(size)), Fraction(0))
            for j in range(size)
        )
        for i in range(size)
    )


def _is_identity(matrix: Matrix) -> bool:
    size = len(matrix)
    return all(matrix[i][j] == (1 if i == j else 0) for i in range(size) for j in range(size))


def _inverse_norm_product(inverse: Matrix) -> Fraction:
    size = len(inverse)
    row_norm = max(sum((abs(value) for value in row), Fraction(0)) for row in inverse)
    column_norm = max(
        sum((abs(inverse[i][j]) for i in range(size)), Fraction(0))
        for j in range(size)
    )
    return row_norm * column_norm


def _interval_certificate_values(
    enclosure: RationalIntervalMatrix,
    ldlt: LDLCertificate,
    inverse_transpose: Matrix,
) -> tuple[Fraction, Fraction]:
    diagonal_minimum = min(ldlt.diagonal)
    center_lower_bound = diagonal_minimum / _inverse_norm_product(inverse_transpose)
    radius = _interval_radius(enclosure)
    perturbation_row_bound = max(
        sum(row, Fraction(0)) for row in radius
    )
    return center_lower_bound, perturbation_row_bound


def certify_interval_matrix(
    enclosure: RationalIntervalMatrix,
) -> IntervalMatrixCertificate:
    checked_enclosure = interval_matrix_from_bounds(enclosure.lower, enclosure.upper)
    center = _interval_center(checked_enclosure)
    ldlt = ldlt_decompose(center)
    if any(value <= 0 for value in ldlt.diagonal):
        raise ValueError("center LDL diagonal must be strictly positive")
    inverse_transpose = _invert_matrix(_transpose(ldlt.lower))
    center_lower_bound, perturbation_row_bound = _interval_certificate_values(
        checked_enclosure, ldlt, inverse_transpose
    )
    return IntervalMatrixCertificate(
        ldlt=ldlt,
        inverse_transpose=inverse_transpose,
        center_lower_bound=center_lower_bound,
        perturbation_row_bound=perturbation_row_bound,
    )


def verify_interval_matrix_certificate(
    enclosure: RationalIntervalMatrix,
    certificate: IntervalMatrixCertificate,
    *,
    require_positive: bool = False,
) -> bool:
    try:
        checked_enclosure = interval_matrix_from_bounds(enclosure.lower, enclosure.upper)
        center = _interval_center(checked_enclosure)
        inverse_transpose = fraction_matrix(
            certificate.inverse_transpose, require_symmetric=False
        )
        diagonal = _fraction_vector(certificate.ldlt.diagonal)
        stored_center_lower_bound = _as_fraction(certificate.center_lower_bound)
        stored_perturbation_row_bound = _as_fraction(
            certificate.perturbation_row_bound
        )
    except (AttributeError, TypeError, ValueError, ZeroDivisionError):
        return False
    size = len(center)
    if len(inverse_transpose) != size or len(diagonal) != size:
        return False
    if any(value <= 0 for value in diagonal):
        return False
    if not verify_ldlt_certificate(center, certificate.ldlt, require_nonnegative=False):
        return False
    if not _is_identity(
        _matrix_product(inverse_transpose, _transpose(certificate.ldlt.lower))
    ):
        return False
    center_lower_bound, perturbation_row_bound = _interval_certificate_values(
        checked_enclosure, certificate.ldlt, inverse_transpose
    )
    if (
        stored_center_lower_bound != center_lower_bound
        or stored_perturbation_row_bound != perturbation_row_bound
    ):
        return False
    if require_positive:
        return perturbation_row_bound < center_lower_bound
    return perturbation_row_bound <= center_lower_bound


def _format_fraction(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def _format_matrix(matrix: Matrix) -> list[list[str]]:
    return [[_format_fraction(value) for value in row] for row in matrix]


def _canonical_json(value: Mapping[str, Any]) -> str:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
        allow_nan=False,
    )


def _reject_nonfinite_json_constant(value: str) -> None:
    raise ValueError(f"non-finite JSON constant is not permitted: {value}")


def _load_strict_json(data: bytes) -> Any:
    return json.loads(data, parse_constant=_reject_nonfinite_json_constant)


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
    output_path.write_bytes((_canonical_json(record) + "\n").encode("utf-8"))
    return record


def load_experiment_artifact(path: str | Path) -> dict[str, Any]:
    record = _load_strict_json(Path(path).read_bytes())
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
    try:
        payload_digest = _payload_digest(payload)
    except (TypeError, ValueError):
        return False
    if payload_digest != record["payload_sha256"]:
        return False

    result = record["result"]
    result_keys = {
        "certified_psd",
        "exact_reconstruction",
        "nonnegative_diagonal",
    }
    if not isinstance(result, dict) or set(result) != result_keys:
        return False
    if any(type(result[key]) is not bool for key in result_keys):
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
    return result == expected_result


def verify_experiment_artifact_file(path: str | Path) -> bool:
    try:
        artifact_bytes = Path(path).read_bytes()
        record = _load_strict_json(artifact_bytes)
        canonical_bytes = (_canonical_json(record) + "\n").encode("utf-8")
    except (OSError, TypeError, UnicodeError, ValueError):
        return False
    return artifact_bytes == canonical_bytes and verify_experiment_artifact(record)


def _interval_inverse_identity(certificate: IntervalMatrixCertificate) -> bool:
    try:
        lower = fraction_matrix(certificate.ldlt.lower, require_symmetric=False)
        inverse_transpose = fraction_matrix(
            certificate.inverse_transpose, require_symmetric=False
        )
    except (TypeError, ValueError):
        return False
    if len(lower) != len(inverse_transpose):
        return False
    return _is_identity(_matrix_product(inverse_transpose, _transpose(lower)))


def _interval_artifact_payload(
    enclosure: RationalIntervalMatrix,
    certificate: IntervalMatrixCertificate,
    parameters: Mapping[str, Any],
) -> dict[str, Any]:
    center = _interval_center(enclosure)
    exact_center_reconstruction = verify_ldlt_certificate(
        center, certificate.ldlt, require_nonnegative=False
    )
    positive_diagonal = all(value > 0 for value in certificate.ldlt.diagonal)
    inverse_transpose_identity = _interval_inverse_identity(certificate)
    certified_psd = verify_interval_matrix_certificate(enclosure, certificate)
    certified_pd = verify_interval_matrix_certificate(
        enclosure, certificate, require_positive=True
    )
    return {
        "certificate": {
            "diagonal": [_format_fraction(value) for value in certificate.ldlt.diagonal],
            "inverse_transpose": _format_matrix(certificate.inverse_transpose),
            "lower": _format_matrix(certificate.ldlt.lower),
        },
        "claim_scope": INTERVAL_CLAIM_SCOPE,
        "enclosure": {
            "lower": _format_matrix(enclosure.lower),
            "upper": _format_matrix(enclosure.upper),
        },
        "parameters": dict(parameters),
        "result": {
            "center_lower_bound": _format_fraction(certificate.center_lower_bound),
            "certified_pd": certified_pd,
            "certified_psd": certified_psd,
            "exact_center_reconstruction": exact_center_reconstruction,
            "inverse_transpose_identity": inverse_transpose_identity,
            "perturbation_row_bound": _format_fraction(
                certificate.perturbation_row_bound
            ),
            "positive_diagonal": positive_diagonal,
        },
        "schema_version": INTERVAL_SCHEMA_VERSION,
    }


def write_interval_experiment_artifact(
    path: str | Path,
    enclosure: RationalIntervalMatrix,
    certificate: IntervalMatrixCertificate,
    *,
    parameters: Mapping[str, Any],
) -> dict[str, Any]:
    checked_enclosure = interval_matrix_from_bounds(enclosure.lower, enclosure.upper)
    payload = _interval_artifact_payload(checked_enclosure, certificate, parameters)
    record = {**payload, "payload_sha256": _payload_digest(payload)}
    output_path = Path(path)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_bytes((_canonical_json(record) + "\n").encode("utf-8"))
    return record


def verify_interval_experiment_artifact(record: Any) -> bool:
    required_keys = {
        "certificate",
        "claim_scope",
        "enclosure",
        "parameters",
        "payload_sha256",
        "result",
        "schema_version",
    }
    if not isinstance(record, dict) or set(record) != required_keys:
        return False
    if (
        record["schema_version"] != INTERVAL_SCHEMA_VERSION
        or record["claim_scope"] != INTERVAL_CLAIM_SCOPE
        or not isinstance(record["parameters"], dict)
        or not isinstance(record["payload_sha256"], str)
    ):
        return False
    payload = {key: value for key, value in record.items() if key != "payload_sha256"}
    try:
        if _payload_digest(payload) != record["payload_sha256"]:
            return False
    except (TypeError, ValueError):
        return False

    enclosure_record = record["enclosure"]
    if not isinstance(enclosure_record, dict) or set(enclosure_record) != {
        "lower",
        "upper",
    }:
        return False
    if not _all_canonical_fraction_strings(
        enclosure_record["lower"]
    ) or not _all_canonical_fraction_strings(enclosure_record["upper"]):
        return False

    certificate_record = record["certificate"]
    if not isinstance(certificate_record, dict) or set(certificate_record) != {
        "diagonal",
        "inverse_transpose",
        "lower",
    }:
        return False
    if not _all_canonical_fraction_strings(
        certificate_record["lower"]
    ) or not _all_canonical_fraction_strings(certificate_record["inverse_transpose"]):
        return False
    raw_diagonal = certificate_record["diagonal"]
    if not isinstance(raw_diagonal, list) or not all(
        _is_canonical_fraction_string(value) for value in raw_diagonal
    ):
        return False

    result = record["result"]
    boolean_result_keys = {
        "certified_pd",
        "certified_psd",
        "exact_center_reconstruction",
        "inverse_transpose_identity",
        "positive_diagonal",
    }
    result_keys = boolean_result_keys | {
        "center_lower_bound",
        "perturbation_row_bound",
    }
    if not isinstance(result, dict) or set(result) != result_keys:
        return False
    if any(type(result[key]) is not bool for key in boolean_result_keys):
        return False
    if not _is_canonical_fraction_string(
        result["center_lower_bound"]
    ) or not _is_canonical_fraction_string(result["perturbation_row_bound"]):
        return False

    try:
        enclosure = interval_matrix_from_bounds(
            enclosure_record["lower"], enclosure_record["upper"]
        )
        certificate = IntervalMatrixCertificate(
            ldlt=LDLCertificate(
                lower=fraction_matrix(
                    certificate_record["lower"], require_symmetric=False
                ),
                diagonal=_fraction_vector(raw_diagonal),
            ),
            inverse_transpose=fraction_matrix(
                certificate_record["inverse_transpose"], require_symmetric=False
            ),
            center_lower_bound=_as_fraction(result["center_lower_bound"]),
            perturbation_row_bound=_as_fraction(result["perturbation_row_bound"]),
        )
        expected_payload = _interval_artifact_payload(
            enclosure, certificate, record["parameters"]
        )
    except (TypeError, ValueError, ZeroDivisionError):
        return False
    return payload == expected_payload


def verify_interval_experiment_artifact_file(path: str | Path) -> bool:
    try:
        artifact_bytes = Path(path).read_bytes()
        record = _load_strict_json(artifact_bytes)
        canonical_bytes = (_canonical_json(record) + "\n").encode("utf-8")
    except (OSError, TypeError, UnicodeError, ValueError):
        return False
    return artifact_bytes == canonical_bytes and verify_interval_experiment_artifact(record)


def _certify(input_path: Path, output_path: Path) -> int:
    input_record = _load_strict_json(input_path.read_bytes())
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
    valid = verify_experiment_artifact_file(path)
    print(f"valid exact LDL^T artifact: {str(valid).lower()}")
    return 0 if valid else 1


def _certify_interval(input_path: Path, output_path: Path) -> int:
    input_record = _load_strict_json(input_path.read_bytes())
    if not isinstance(input_record, dict):
        raise ValueError("interval input must be a JSON object")
    parameters = input_record.get("parameters", {})
    if not isinstance(parameters, dict):
        raise ValueError("parameters must be a JSON object")
    interval_keys = set(input_record) - {"parameters"}
    if interval_keys == {"center", "radius"}:
        enclosure = interval_matrix_from_center_radius(
            input_record["center"], input_record["radius"]
        )
    elif interval_keys == {"lower", "upper"}:
        enclosure = interval_matrix_from_bounds(
            input_record["lower"], input_record["upper"]
        )
    else:
        raise ValueError("input must contain exactly center/radius or lower/upper")
    certificate = certify_interval_matrix(enclosure)
    artifact = write_interval_experiment_artifact(
        output_path, enclosure, certificate, parameters=parameters
    )
    print(
        "certified interval matrix positive definite: "
        f"{str(artifact['result']['certified_pd']).lower()}"
    )
    return 0


def _verify_interval(path: Path) -> int:
    valid = verify_interval_experiment_artifact_file(path)
    print(f"valid interval LDL^T artifact: {str(valid).lower()}")
    return 0 if valid else 1


def _verify_groskin_provenance(path: Path, expected_c: int, expected_N: int) -> int:
    try:
        record = _load_strict_json(path.read_bytes())
    except (OSError, TypeError, UnicodeError, ValueError):
        valid = False
    else:
        valid = verify_groskin_provenance_metadata(
            record, expected_c=expected_c, expected_N=expected_N
        )
    print(f"dimensionally consistent Groskin provenance metadata: {str(valid).lower()}")
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

    certify_interval_parser = subparsers.add_parser("certify-interval")
    certify_interval_parser.add_argument("input", type=Path)
    certify_interval_parser.add_argument("output", type=Path)

    verify_interval_parser = subparsers.add_parser("verify-interval")
    verify_interval_parser.add_argument("artifact", type=Path)

    verify_groskin_parser = subparsers.add_parser("verify-groskin-provenance")
    verify_groskin_parser.add_argument("provenance", type=Path)
    verify_groskin_parser.add_argument("--c", type=int, required=True)
    verify_groskin_parser.add_argument("--N", type=int, required=True)

    args = parser.parse_args(argv)
    if args.command == "certify":
        return _certify(args.input, args.output)
    if args.command == "verify":
        return _verify(args.artifact)
    if args.command == "certify-interval":
        return _certify_interval(args.input, args.output)
    if args.command == "verify-interval":
        return _verify_interval(args.artifact)
    return _verify_groskin_provenance(args.provenance, args.c, args.N)


if __name__ == "__main__":
    raise SystemExit(main())
