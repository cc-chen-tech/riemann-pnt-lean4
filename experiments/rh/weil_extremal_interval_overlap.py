"""Overlap and symmetrization merge for Weil extremal kernel interval artifacts.

This module implements rings 1/2 of the Gate A six-ring certificate chain: it
consumes two independent interval-assembly artifacts (schema
``weil-extremal-kernel-interval-assembly/v1``) produced by two mutually
independent routes, and

1. validates both artifacts (schema, index convention, well-formed enclosing
   intervals, and the ``payload_sha256`` self-hash);
2. checks that the two artifacts agree on ``c``/``N``/``dimension``/
   ``index_convention`` and were produced by *different* routes;
3. intersects the two enclosures entry by entry — an empty intersection for
   any entry rejects the merge with a non-zero exit code, reporting both
   intervals and the relative gap of that entry;
4. exploits the real symmetry of the matrix by intersecting, for every
   unordered pair ``(i, j)``, the merged enclosure at ``(i, j)`` with the
   merged enclosure at ``(j, i)`` (symmetrize-by-intersection; the triangle is
   never copied), and assigns the intersection to both positions;
5. outward-rounds the strict intersection to a fixed dyadic rational
   enclosure and certifies the shifted center ``C - 2ρ I`` by an exact
   rational ``LDL^T`` decomposition;
6. emits ``weil-extremal-kernel-dual-route-certificate/v1`` with source
   hashes, a machine-checkable strict-overlap predicate, the exact shifted
   certificate, overlap diagnostics, and a canonical ``payload_sha256``.

All interval arithmetic on the serialized decimal endpoints is exact
``Decimal`` arithmetic: intersection endpoints are selected (max of lowers,
min of uppers), never rounded.  Touching endpoints are rejected.  The
dyadic conversion rounds outward and therefore only enlarges the certified
enclosure.  The claim scope is finite rational interval matrices; this module
does not assert an infinite-dimensional Weil criterion or RH.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from decimal import Decimal, InvalidOperation, localcontext
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, List, Mapping, Optional, Sequence, Tuple

from experiments.rh import weil_extremal_kernels as exact

ROUTE_SCHEMA_VERSION = "weil-extremal-kernel-interval-assembly/v1"
OVERLAP_SCHEMA_VERSION = "weil-extremal-kernel-dual-route-certificate/v1"
LDLT_SCHEMA_VERSION = "weil-extremal-kernel-shifted-interval-ldlt/v1"
CLAIM_SCOPE = "finite-rational-interval-matrix-only"
DEFAULT_CERTIFICATE_BITS = 256
# Backward-compatible name used by the two route producers.
SCHEMA_VERSION = ROUTE_SCHEMA_VERSION
INDEX_CONVENTION = "fourier -N..N row-major"
GENERATOR = "experiments/rh/weil_extremal_interval_overlap.py"

ROUTE_REQUIRED_FIELDS = {
    "schema_version",
    "c",
    "N",
    "dimension",
    "route",
    "prec_bits",
    "index_convention",
    "entries",
    "provenance",
    "payload_sha256",
}
OVERLAP_REQUIRED_FIELDS = ROUTE_REQUIRED_FIELDS | {
    "certificate",
    "source_artifacts",
    "strict_overlap",
    "overlap",
}
PROVENANCE_FIELDS = {"generator", "note", "created_utc"}

EXIT_OK = 0
EXIT_INVALID_ARTIFACT = 1
EXIT_EMPTY_OVERLAP = 2

Interval = Tuple[Decimal, Decimal]


class ArtifactError(ValueError):
    """Raised when an interval artifact fails validation."""


class OverlapError(ValueError):
    """Raised when two certified enclosures have an empty intersection.

    The ``report`` attribute carries a JSON-serializable description of the
    failure: the entry, both intervals, the absolute gap, and the relative
    gap (``None`` when both adjacent endpoints are zero).
    """

    def __init__(self, report: Mapping[str, Any]) -> None:
        self.report = dict(report)
        super().__init__(json.dumps(self.report, sort_keys=True))


def _canonical_json(value: Mapping[str, Any]) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def _payload_digest(payload: Mapping[str, Any]) -> str:
    return hashlib.sha256(_canonical_json(payload).encode("utf-8")).hexdigest()


def _parse_decimal(value: Any) -> Decimal:
    if not isinstance(value, str):
        raise ArtifactError(f"interval endpoint must be a decimal string, got {value!r}")
    try:
        parsed = Decimal(value)
    except (InvalidOperation, ValueError):
        raise ArtifactError(f"interval endpoint is not a valid decimal: {value!r}")
    if not parsed.is_finite():
        raise ArtifactError(f"interval endpoint must be finite, got {value!r}")
    return parsed


def _parse_fraction(value: Any) -> Fraction:
    if not isinstance(value, str):
        raise ArtifactError(f"rational value must be a string, got {value!r}")
    try:
        parsed = Fraction(value)
    except (ValueError, ZeroDivisionError) as error:
        raise ArtifactError(f"invalid rational value {value!r}") from error
    if _fraction_str(parsed) != value:
        raise ArtifactError(f"rational value is not canonical: {value!r}")
    return parsed


def _fraction_str(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def _fraction_matrix_str(matrix: exact.Matrix) -> List[List[str]]:
    return [[_fraction_str(value) for value in row] for row in matrix]


def _decimal_str(value: Decimal) -> str:
    """Serialize a Decimal exactly in plain notation, stripping redundant zeros.

    The transformation is purely syntactic (no rounding, no context
    dependence), so serialized endpoints remain exact enclosure bounds.
    """
    text = format(value, "f")
    if "." in text:
        text = text.rstrip("0").rstrip(".")
    if text in ("", "-0"):
        return "0"
    return text


def _is_int(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool)


def entry_index(i: int, j: int, N: int) -> int:
    """Flat row-major index of matrix entry ``(i, j)`` with indices in ``-N..N``."""
    if not -N <= i <= N or not -N <= j <= N:
        raise ValueError(f"entry ({i}, {j}) outside -{N}..{N}")
    return (i + N) * (2 * N + 1) + (j + N)


def index_entry(flat: int, N: int) -> Tuple[int, int]:
    """Inverse of :func:`entry_index`."""
    dimension = 2 * N + 1
    if not 0 <= flat < dimension * dimension:
        raise ValueError(f"flat index {flat} outside 0..{dimension * dimension - 1}")
    row, col = divmod(flat, dimension)
    return row - N, col - N


def _working_precision(intervals: Sequence[Interval]) -> int:
    """Precision (in significant digits) making endpoint arithmetic exact."""
    max_digits = 1
    for lo, hi in intervals:
        for endpoint in (lo, hi):
            max_digits = max(max_digits, len(endpoint.as_tuple().digits))
    return max(200, 4 * max_digits + 50)


def validate_artifact(record: Any, *, label: str = "artifact") -> None:
    """Validate a route artifact or a dual-route proof-carrying artifact.

    Raises :class:`ArtifactError` on any violation.  Extra top-level fields
    beyond the required schema fields are covered by the self-hash.
    """
    if not isinstance(record, dict):
        raise ArtifactError(f"{label}: top-level value must be a JSON object")
    schema_version = record.get("schema_version")
    if schema_version == ROUTE_SCHEMA_VERSION:
        required_fields = ROUTE_REQUIRED_FIELDS
    elif schema_version == OVERLAP_SCHEMA_VERSION:
        required_fields = OVERLAP_REQUIRED_FIELDS
    else:
        raise ArtifactError(
            f"{label}: unsupported schema_version {schema_version!r}"
        )
    missing = required_fields - set(record)
    if missing:
        raise ArtifactError(f"{label}: missing required fields {sorted(missing)}")
    if not _is_int(record["c"]) or record["c"] < 2:
        raise ArtifactError(f"{label}: c must be an integer at least 2")
    if not _is_int(record["N"]) or record["N"] < 0:
        raise ArtifactError(f"{label}: N must be a nonnegative integer")
    dimension = 2 * record["N"] + 1
    if record["dimension"] != dimension:
        raise ArtifactError(
            f"{label}: dimension must be 2N+1 = {dimension}, got {record['dimension']!r}"
        )
    if not isinstance(record["route"], str) or not record["route"]:
        raise ArtifactError(f"{label}: route must be a nonempty string")
    if not _is_int(record["prec_bits"]) or record["prec_bits"] < 1:
        raise ArtifactError(f"{label}: prec_bits must be a positive integer")
    if record["index_convention"] != INDEX_CONVENTION:
        raise ArtifactError(
            f"{label}: index_convention must be {INDEX_CONVENTION!r}, "
            f"got {record['index_convention']!r}"
        )
    entries = record["entries"]
    if not isinstance(entries, list) or len(entries) != dimension * dimension:
        raise ArtifactError(
            f"{label}: entries must be a list of (2N+1)^2 = {dimension * dimension} "
            "intervals"
        )
    for flat, item in enumerate(entries):
        if (
            not isinstance(item, list)
            or len(item) != 2
            or not all(isinstance(endpoint, str) for endpoint in item)
        ):
            i, j = index_entry(flat, record["N"])
            raise ArtifactError(
                f"{label}: entry ({i}, {j}) must be a [lo, hi] pair of decimal strings"
            )
        lo = _parse_decimal(item[0])
        hi = _parse_decimal(item[1])
        if lo > hi:
            i, j = index_entry(flat, record["N"])
            raise ArtifactError(
                f"{label}: entry ({i}, {j}) has lo > hi: [{item[0]}, {item[1]}]"
            )
    provenance = record["provenance"]
    if not isinstance(provenance, dict) or set(provenance) != PROVENANCE_FIELDS:
        raise ArtifactError(
            f"{label}: provenance must be an object with fields {sorted(PROVENANCE_FIELDS)}"
        )
    if not all(isinstance(provenance[field], str) for field in PROVENANCE_FIELDS):
        raise ArtifactError(f"{label}: provenance fields must be strings")
    if not isinstance(record["payload_sha256"], str):
        raise ArtifactError(f"{label}: payload_sha256 must be a string")
    payload = {key: value for key, value in record.items() if key != "payload_sha256"}
    if _payload_digest(payload) != record["payload_sha256"]:
        raise ArtifactError(
            f"{label}: payload_sha256 does not match the canonical payload "
            "(artifact corrupted or tampered)"
        )
    if schema_version == OVERLAP_SCHEMA_VERSION:
        _validate_overlap_certificate(record, label=label)


def verify_artifact(record: Any) -> bool:
    """Boolean counterpart of :func:`validate_artifact`."""
    try:
        validate_artifact(record)
    except ArtifactError:
        return False
    return True


def load_artifact(path: str | Path, *, label: Optional[str] = None) -> Dict[str, Any]:
    """Load and validate an interval artifact from disk."""
    source = Path(path)
    try:
        record = json.loads(source.read_bytes())
    except (OSError, json.JSONDecodeError) as error:
        raise ArtifactError(f"{label or source}: cannot read artifact: {error}") from error
    validate_artifact(record, label=label or str(source))
    return record


def _intervals(record: Mapping[str, Any]) -> List[Interval]:
    return [(_parse_decimal(lo), _parse_decimal(hi)) for lo, hi in record["entries"]]


def _gap_report(
    i: int,
    j: int,
    first: Interval,
    second: Interval,
    *,
    kind: str,
) -> Dict[str, Any]:
    """Describe an empty intersection between two enclosures."""
    if first[1] <= second[0]:
        lower_interval, upper_interval = first, second
        first_label, second_label = "first", "second"
    else:
        lower_interval, upper_interval = second, first
        first_label, second_label = "second", "first"
    gap = upper_interval[0] - lower_interval[1]
    scale = max(abs(lower_interval[1]), abs(upper_interval[0]))
    relative_gap: Optional[str]
    relative_gap = _decimal_str(gap / scale) if scale > 0 else None
    return {
        "kind": kind,
        "entry": [i, j],
        "first_interval": [_decimal_str(first[0]), _decimal_str(first[1])],
        "second_interval": [_decimal_str(second[0]), _decimal_str(second[1])],
        "absolute_gap": _decimal_str(gap),
        "relative_gap": relative_gap,
        "lower_interval_from": first_label,
        "upper_interval_from": second_label,
    }


def _intersect(first: Interval, second: Interval) -> Optional[Interval]:
    lo = max(first[0], second[0])
    hi = min(first[1], second[1])
    if lo >= hi:
        return None
    return lo, hi


def _dyadic_bound(value: str, bits: int, *, lower: bool) -> Fraction:
    scale = 1 << bits
    scaled = Fraction(value) * scale
    if lower:
        integer = scaled.numerator // scaled.denominator
    else:
        integer = -((-scaled.numerator) // scaled.denominator)
    return Fraction(integer, scale)


def _dyadic_enclosure(
    entries: Sequence[Sequence[str]], dimension: int, bits: int
) -> exact.RationalIntervalMatrix:
    lower = tuple(
        tuple(
            _dyadic_bound(entries[i * dimension + j][0], bits, lower=True)
            for j in range(dimension)
        )
        for i in range(dimension)
    )
    upper = tuple(
        tuple(
            _dyadic_bound(entries[i * dimension + j][1], bits, lower=False)
            for j in range(dimension)
        )
        for i in range(dimension)
    )
    return exact.interval_matrix_from_bounds(lower, upper)


def _center_radius(
    enclosure: exact.RationalIntervalMatrix,
) -> Tuple[exact.Matrix, exact.Matrix]:
    dimension = len(enclosure.lower)
    center = tuple(
        tuple(
            (enclosure.lower[i][j] + enclosure.upper[i][j]) / 2
            for j in range(dimension)
        )
        for i in range(dimension)
    )
    radius = tuple(
        tuple(
            (enclosure.upper[i][j] - enclosure.lower[i][j]) / 2
            for j in range(dimension)
        )
        for i in range(dimension)
    )
    return center, radius


def _build_shifted_ldlt_certificate(
    entries: Sequence[Sequence[str]],
    dimension: int,
    source_hashes: Sequence[str],
    *,
    bits: int,
) -> Dict[str, Any]:
    enclosure = _dyadic_enclosure(entries, dimension, bits)
    center, radius = _center_radius(enclosure)
    rho = max(sum(row, Fraction(0)) for row in radius)
    mu = 2 * rho
    shifted = tuple(
        tuple(
            center[i][j] - (mu if i == j else 0)
            for j in range(dimension)
        )
        for i in range(dimension)
    )
    ldlt = exact.ldlt_decompose(shifted)
    nonnegative_diagonal = all(value >= 0 for value in ldlt.diagonal)
    exact_reconstruction = exact.verify_ldlt_certificate(shifted, ldlt)
    strict_budget = rho < mu
    if not nonnegative_diagonal or not exact_reconstruction or not strict_budget:
        raise ArtifactError(
            "outward-dyadic enclosure failed shifted exact LDL certification"
        )
    result = {
        "center_lower_bound": _fraction_str(mu),
        "certified_pd": True,
        "certified_psd": True,
        "exact_shifted_reconstruction": True,
        "nonnegative_diagonal": True,
        "perturbation_row_bound": _fraction_str(rho),
        "strict_budget": True,
    }
    payload: Dict[str, Any] = {
        "schema_version": LDLT_SCHEMA_VERSION,
        "claim_scope": CLAIM_SCOPE,
        "dyadic_bits": bits,
        "source_payload_sha256": list(source_hashes),
        "center_lower_bound": _fraction_str(mu),
        "perturbation_row_bound": _fraction_str(rho),
        "lower": _fraction_matrix_str(ldlt.lower),
        "diagonal": [_fraction_str(value) for value in ldlt.diagonal],
        "result": result,
    }
    return {**payload, "payload_sha256": _payload_digest(payload)}


def _validate_shifted_ldlt_certificate(
    record: Mapping[str, Any],
    certificate: Any,
    *,
    label: str,
) -> None:
    required = {
        "schema_version",
        "claim_scope",
        "dyadic_bits",
        "source_payload_sha256",
        "center_lower_bound",
        "perturbation_row_bound",
        "lower",
        "diagonal",
        "result",
        "payload_sha256",
    }
    if not isinstance(certificate, dict) or set(certificate) != required:
        raise ArtifactError(f"{label}: certificate has incorrect fields")
    if certificate["schema_version"] != LDLT_SCHEMA_VERSION:
        raise ArtifactError(f"{label}: unsupported shifted LDL schema")
    if certificate["claim_scope"] != CLAIM_SCOPE:
        raise ArtifactError(f"{label}: invalid finite claim_scope")
    bits = certificate["dyadic_bits"]
    if not _is_int(bits) or bits < 1:
        raise ArtifactError(f"{label}: dyadic_bits must be positive")
    certificate_payload = {
        key: value for key, value in certificate.items() if key != "payload_sha256"
    }
    if _payload_digest(certificate_payload) != certificate["payload_sha256"]:
        raise ArtifactError(f"{label}: certificate payload hash mismatch")
    source_hashes = [source["payload_sha256"] for source in record["source_artifacts"]]
    if certificate["source_payload_sha256"] != source_hashes:
        raise ArtifactError(f"{label}: certificate/source hash mismatch")

    dimension = record["dimension"]
    try:
        lower = exact.fraction_matrix(
            certificate["lower"], require_symmetric=False
        )
        diagonal = tuple(_parse_fraction(value) for value in certificate["diagonal"])
        mu = _parse_fraction(certificate["center_lower_bound"])
        rho = _parse_fraction(certificate["perturbation_row_bound"])
        enclosure = _dyadic_enclosure(record["entries"], dimension, bits)
    except (TypeError, ValueError) as error:
        raise ArtifactError(f"{label}: invalid shifted LDL data: {error}") from error
    if len(lower) != dimension or len(diagonal) != dimension:
        raise ArtifactError(f"{label}: shifted LDL dimension mismatch")
    center, radius = _center_radius(enclosure)
    expected_rho = max(sum(row, Fraction(0)) for row in radius)
    expected_mu = 2 * expected_rho
    if rho != expected_rho or mu != expected_mu:
        raise ArtifactError(f"{label}: stored interval budget was not recomputed")
    shifted = tuple(
        tuple(
            center[i][j] - (mu if i == j else 0)
            for j in range(dimension)
        )
        for i in range(dimension)
    )
    ldlt = exact.LDLCertificate(lower=lower, diagonal=diagonal)
    exact_reconstruction = exact.verify_ldlt_certificate(shifted, ldlt)
    nonnegative_diagonal = all(value >= 0 for value in diagonal)
    strict_budget = rho < mu
    expected_result = {
        "center_lower_bound": _fraction_str(mu),
        "certified_pd": exact_reconstruction
        and nonnegative_diagonal
        and strict_budget,
        "certified_psd": exact_reconstruction
        and nonnegative_diagonal
        and rho <= mu,
        "exact_shifted_reconstruction": exact_reconstruction,
        "nonnegative_diagonal": nonnegative_diagonal,
        "perturbation_row_bound": _fraction_str(rho),
        "strict_budget": strict_budget,
    }
    if certificate["result"] != expected_result:
        raise ArtifactError(f"{label}: shifted LDL result fields do not replay")
    if not expected_result["certified_pd"]:
        raise ArtifactError(f"{label}: shifted LDL certificate does not certify PD")


def _validate_overlap_certificate(
    record: Mapping[str, Any], *, label: str
) -> None:
    sources = record["source_artifacts"]
    if not isinstance(sources, list) or len(sources) != 2:
        raise ArtifactError(f"{label}: source_artifacts must contain two routes")
    source_required = {
        "schema_version",
        "route",
        "prec_bits",
        "payload_sha256",
    }
    for source in sources:
        if not isinstance(source, dict) or set(source) != source_required:
            raise ArtifactError(f"{label}: malformed source_artifacts entry")
        if source["schema_version"] != ROUTE_SCHEMA_VERSION:
            raise ArtifactError(f"{label}: source artifact schema mismatch")
        if (
            not isinstance(source["payload_sha256"], str)
            or len(source["payload_sha256"]) != 64
            or any(character not in "0123456789abcdef" for character in source["payload_sha256"])
        ):
            raise ArtifactError(f"{label}: malformed source payload hash")
    if sources[0]["route"] == sources[1]["route"]:
        raise ArtifactError(f"{label}: source routes must be independent")
    if [source["route"] for source in sources] != record["overlap"]["routes"]:
        raise ArtifactError(f"{label}: source routes disagree with overlap report")

    strict = record["strict_overlap"]
    expected_strict = {
        "all_strict": True,
        "predicate": "max(lower_a,lower_b) < min(upper_a,upper_b)",
        "route_intersection_count": record["dimension"] ** 2,
        "symmetry_intersection_count": (
            record["dimension"] * (record["dimension"] - 1) // 2
        ),
    }
    if strict != expected_strict:
        raise ArtifactError(f"{label}: strict-overlap proof fields do not replay")
    if any(_parse_decimal(lo) >= _parse_decimal(hi) for lo, hi in record["entries"]):
        raise ArtifactError(f"{label}: merged artifact contains a non-strict interval")
    _validate_shifted_ldlt_certificate(
        record, record["certificate"], label=label
    )


def _lean_rational(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"({value.numerator} : ℚ) / {value.denominator}"


def _render_lean_matrix(name: str, matrix: exact.Matrix) -> str:
    rows = []
    for row in matrix:
        entries = ",\n".join(f"      {_lean_rational(value)}" for value in row)
        rows.append(f"  #[\n{entries}\n  ]")
    return (
        f"private def {name} : Array (Array ℚ) := #[\n"
        + ",\n".join(rows)
        + "\n]\n"
    )


def _render_lean_vector(name: str, values: Sequence[Fraction]) -> str:
    entries = ",\n".join(f"  {_lean_rational(value)}" for value in values)
    return f"private def {name} : Array ℚ := #[\n{entries}\n]\n"


def render_lean_certificate(
    record: Mapping[str, Any],
    *,
    namespace: str,
    metadata_constant: str,
) -> str:
    """Render one validated overlap artifact as a Lean-native-replayable module."""
    validate_artifact(record, label="Lean certificate source")
    if not namespace or any(not part for part in namespace.split(".")):
        raise ArtifactError("Lean namespace must be dot-separated and nonempty")
    if not metadata_constant or not metadata_constant.isidentifier():
        raise ArtifactError("Lean metadata constant must be an identifier")

    dimension = record["dimension"]
    certificate = record["certificate"]
    enclosure = _dyadic_enclosure(
        record["entries"], dimension, certificate["dyadic_bits"]
    )
    shifted_lower = exact.fraction_matrix(
        certificate["lower"], require_symmetric=False
    )
    shifted_diagonal = tuple(
        _parse_fraction(value) for value in certificate["diagonal"]
    )
    mu = _parse_fraction(certificate["center_lower_bound"])
    rho = _parse_fraction(certificate["perturbation_row_bound"])
    payload_hash = record["payload_sha256"]

    sections = [
        "import WeilExtremalKernels.FiniteQuadraticForm\n",
        "/-!\n",
        "Generated from a validated dual-route overlap artifact.\n",
        f"Payload SHA-256: {payload_hash}\n",
        "Claim scope: finite rational interval matrix only.\n",
        "Do not edit by hand; regenerate with weil_extremal_interval_overlap.py.\n",
        "-/\n\n",
        f"namespace {namespace}\n\n",
        "open WeilExtremalKernels\n\n",
        "set_option maxRecDepth 1000000\n\n",
        _render_lean_matrix("lowerRows", enclosure.lower),
        "\n",
        _render_lean_matrix("upperRows", enclosure.upper),
        "\n",
        _render_lean_matrix("shiftedLowerRows", shifted_lower),
        "\n",
        _render_lean_vector("shiftedDiagonalValues", shifted_diagonal),
        "\n",
        f"def certificate : RationalIntervalLDLCertificate {dimension} where\n",
        f"  metadata := {metadata_constant}\n",
        "  lower := rationalMatrixOfRows lowerRows\n",
        "  upper := rationalMatrixOfRows upperRows\n",
        "  shiftedLower := rationalMatrixOfRows shiftedLowerRows\n",
        "  shiftedDiagonal := rationalVectorOfArray shiftedDiagonalValues\n",
        f"  centerLowerBound := {_lean_rational(mu)}\n",
        f"  perturbationRowBound := {_lean_rational(rho)}\n\n",
        "set_option maxHeartbeats 0 in\n",
        "set_option maxRecDepth 1000000 in\n",
        "theorem certificate_valid : certificate.Valid := by\n",
        "  native_decide\n\n",
        "set_option maxHeartbeats 0 in\n",
        "set_option maxRecDepth 1000000 in\n",
        "theorem certificate_strictValid : certificate.StrictValid := by\n",
        "  native_decide\n\n",
        "theorem artifact_quadraticForm_nonneg\n",
        f"    (A : FiniteMatrix {dimension})\n",
        "    (hbounds : ∀ i j,\n",
        "      (certificate.lower i j : ℝ) ≤ A i j ∧\n",
        "        A i j ≤ (certificate.upper i j : ℝ)) :\n",
        "    ∀ x, 0 ≤ quadraticForm A x :=\n",
        "  certificate.quadraticForm_nonneg_of_bounds certificate_valid A hbounds\n\n",
        "theorem artifact_quadraticForm_pos\n",
        f"    (A : FiniteMatrix {dimension})\n",
        "    (hbounds : ∀ i j,\n",
        "      (certificate.lower i j : ℝ) ≤ A i j ∧\n",
        "        A i j ≤ (certificate.upper i j : ℝ)) :\n",
        "    ∀ x, x ≠ 0 → 0 < quadraticForm A x :=\n",
        "  certificate.quadraticForm_pos_of_bounds\n",
        "    certificate_strictValid A hbounds\n\n",
        f"end {namespace}\n",
    ]
    return "".join(sections)


def write_lean_certificate(
    record: Mapping[str, Any],
    path: str | Path,
    *,
    namespace: str,
    metadata_constant: str,
) -> None:
    source = render_lean_certificate(
        record,
        namespace=namespace,
        metadata_constant=metadata_constant,
    )
    output_path = Path(path)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(source, encoding="utf-8")


def merge_artifacts(
    artifact_a: Mapping[str, Any],
    artifact_b: Mapping[str, Any],
    *,
    created_utc: Optional[str] = None,
) -> Dict[str, Any]:
    """Merge two validated interval artifacts into one symmetrized artifact.

    Raises :class:`ArtifactError` on any validation or consistency failure and
    :class:`OverlapError` when any entrywise (or symmetrization) intersection
    is empty.
    """
    validate_artifact(artifact_a, label="artifact A")
    validate_artifact(artifact_b, label="artifact B")
    for field in ("c", "N", "dimension", "index_convention"):
        if artifact_a[field] != artifact_b[field]:
            raise ArtifactError(
                f"{field} mismatch between artifacts: "
                f"{artifact_a[field]!r} vs {artifact_b[field]!r}"
            )
    if artifact_a["route"] == artifact_b["route"]:
        raise ArtifactError(
            "both artifacts claim the same route "
            f"{artifact_a['route']!r}; the certificate chain requires two "
            "independent routes"
        )

    N = artifact_a["N"]
    dimension = artifact_a["dimension"]
    route_a = artifact_a["route"]
    route_b = artifact_b["route"]
    intervals_a = _intervals(artifact_a)
    intervals_b = _intervals(artifact_b)

    with localcontext() as context:
        context.prec = _working_precision([*intervals_a, *intervals_b])

        merged: List[Interval] = []
        for flat in range(dimension * dimension):
            i, j = index_entry(flat, N)
            enclosure = _intersect(intervals_a[flat], intervals_b[flat])
            if enclosure is None:
                report = _gap_report(
                    i,
                    j,
                    intervals_a[flat],
                    intervals_b[flat],
                    kind="route_intersection",
                )
                report["strict_overlap"] = False
                raise OverlapError(report)
            merged.append(enclosure)

        symmetrization_narrowed = 0
        for i in range(-N, N + 1):
            for j in range(i + 1, N + 1):
                upper = entry_index(i, j, N)
                lower = entry_index(j, i, N)
                enclosure = _intersect(merged[upper], merged[lower])
                if enclosure is None:
                    report = _gap_report(
                        i,
                        j,
                        merged[upper],
                        merged[lower],
                        kind="symmetrization",
                    )
                    report["strict_overlap"] = False
                    raise OverlapError(report)
                if enclosure != merged[upper] or enclosure != merged[lower]:
                    symmetrization_narrowed += 1
                merged[upper] = enclosure
                merged[lower] = enclosure

        per_entry: List[Dict[str, Any]] = []
        widths: List[Decimal] = []
        for flat in range(dimension * dimension):
            i, j = index_entry(flat, N)
            width = merged[flat][1] - merged[flat][0]
            widths.append(width)
            per_entry.append(
                {
                    "entry": [i, j],
                    "index": flat,
                    "intersection_width": _decimal_str(width),
                    "width_route_a": _decimal_str(
                        intervals_a[flat][1] - intervals_a[flat][0]
                    ),
                    "width_route_b": _decimal_str(
                        intervals_b[flat][1] - intervals_b[flat][0]
                    ),
                }
            )
        max_flat = max(range(len(widths)), key=lambda k: widths[k])
        min_flat = min(range(len(widths)), key=lambda k: widths[k])
        mean_width = sum(widths, Decimal(0)) / len(widths)

        overlap_report = {
            "routes": [route_a, route_b],
            "entry_count": dimension * dimension,
            "max_intersection_width": {
                "entry": list(index_entry(max_flat, N)),
                "width": _decimal_str(widths[max_flat]),
            },
            "tightest_entry": {
                "entry": list(index_entry(min_flat, N)),
                "width": _decimal_str(widths[min_flat]),
            },
            "mean_intersection_width": _decimal_str(mean_width),
            "symmetrization_narrowed_pairs": symmetrization_narrowed,
            "per_entry": per_entry,
        }

    if created_utc is None:
        created_utc = max(
            artifact_a["provenance"]["created_utc"],
            artifact_b["provenance"]["created_utc"],
        )
    serialized_entries = [
        [_decimal_str(lo), _decimal_str(hi)] for lo, hi in merged
    ]
    source_artifacts = [
        {
            "schema_version": artifact["schema_version"],
            "route": artifact["route"],
            "prec_bits": artifact["prec_bits"],
            "payload_sha256": artifact["payload_sha256"],
        }
        for artifact in (artifact_a, artifact_b)
    ]
    certificate = _build_shifted_ldlt_certificate(
        serialized_entries,
        dimension,
        [source["payload_sha256"] for source in source_artifacts],
        bits=DEFAULT_CERTIFICATE_BITS,
    )
    payload: Dict[str, Any] = {
        "schema_version": OVERLAP_SCHEMA_VERSION,
        "c": artifact_a["c"],
        "N": N,
        "dimension": dimension,
        "route": f"overlap({route_a}|{route_b})",
        "prec_bits": min(artifact_a["prec_bits"], artifact_b["prec_bits"]),
        "index_convention": INDEX_CONVENTION,
        "entries": serialized_entries,
        "source_artifacts": source_artifacts,
        "strict_overlap": {
            "all_strict": True,
            "predicate": "max(lower_a,lower_b) < min(upper_a,upper_b)",
            "route_intersection_count": dimension * dimension,
            "symmetry_intersection_count": dimension * (dimension - 1) // 2,
        },
        "certificate": certificate,
        "provenance": {
            "generator": GENERATOR,
            "note": (
                "entrywise intersection of two independent interval assemblies, "
                "strictly symmetrized across the transpose, then certified by "
                "an exact shifted rational LDL decomposition of an outward-"
                "dyadic enclosure; finite matrix claim only"
            ),
            "created_utc": created_utc,
        },
        "overlap": overlap_report,
    }
    return {**payload, "payload_sha256": _payload_digest(payload)}


def write_merged_artifact(
    path_a: str | Path,
    path_b: str | Path,
    path_out: str | Path,
) -> Dict[str, Any]:
    """Load two artifacts, merge them, and write the canonical merged record."""
    artifact_a = load_artifact(path_a, label="artifact A")
    artifact_b = load_artifact(path_b, label="artifact B")
    record = merge_artifacts(artifact_a, artifact_b)
    output_path = Path(path_out)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_bytes((_canonical_json(record) + "\n").encode("utf-8"))
    return record


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Merge two independent weil-extremal-kernel-interval-assembly/v1 "
            "artifacts by entrywise interval intersection plus "
            "symmetrize-by-intersection; rejects with a non-zero exit code if "
            "any intersection is empty."
        )
    )
    parser.add_argument("--a", required=True, help="path to interval artifact from route A")
    parser.add_argument("--b", required=True, help="path to interval artifact from route B")
    parser.add_argument("--out", required=True, help="output path for the merged artifact")
    parser.add_argument(
        "--lean-out",
        help="optional generated Lean certificate module path",
    )
    parser.add_argument(
        "--lean-namespace",
        help="namespace for --lean-out (defaults from c and N)",
    )
    parser.add_argument(
        "--lean-metadata-constant",
        help="ArtifactMetadata constant for --lean-out (defaults from c and N)",
    )
    args = parser.parse_args(argv)

    try:
        record = write_merged_artifact(args.a, args.b, args.out)
        if args.lean_out:
            namespace = args.lean_namespace or (
                "WeilExtremalKernels.Certificates."
                f"C{record['c']}N{record['N']}"
            )
            metadata_constant = args.lean_metadata_constant or (
                f"c{record['c']}N{record['N']}ArtifactMetadata"
            )
            write_lean_certificate(
                record,
                args.lean_out,
                namespace=namespace,
                metadata_constant=metadata_constant,
            )
    except OverlapError as error:
        print(
            _canonical_json({"status": "rejected", "reason": error.report}),
            file=sys.stderr,
        )
        return EXIT_EMPTY_OVERLAP
    except (ArtifactError, OSError) as error:
        print(
            _canonical_json({"status": "rejected", "reason": str(error)}),
            file=sys.stderr,
        )
        return EXIT_INVALID_ARTIFACT

    summary = {
        "status": "merged",
        "out": str(args.out),
        "route": record["route"],
        "max_intersection_width": record["overlap"]["max_intersection_width"],
        "tightest_entry": record["overlap"]["tightest_entry"],
        "symmetrization_narrowed_pairs": record["overlap"][
            "symmetrization_narrowed_pairs"
        ],
        "payload_sha256": record["payload_sha256"],
    }
    print(_canonical_json(summary))
    return EXIT_OK


if __name__ == "__main__":
    raise SystemExit(main())
