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
5. emits a merged artifact in the same schema whose ``route`` field records
   the composition of the two input routes, augmented with an ``overlap``
   report section (maximum intersection width, tightest entry, per-entry
   overlap statistics), written as canonical JSON with a fresh
   ``payload_sha256``.

All interval arithmetic on the serialized decimal endpoints is exact
``Decimal`` arithmetic: intersection endpoints are selected (max of lowers,
min of uppers), never rounded, so the merged intervals are strict enclosures
whenever the inputs are.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from datetime import datetime, timezone
from decimal import Decimal, InvalidOperation, localcontext
from pathlib import Path
from typing import Any, Dict, List, Mapping, Optional, Sequence, Tuple

SCHEMA_VERSION = "weil-extremal-kernel-interval-assembly/v1"
INDEX_CONVENTION = "fourier -N..N row-major"
GENERATOR = "experiments/rh/weil_extremal_interval_overlap.py"

REQUIRED_FIELDS = {
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
    """Validate one ``weil-extremal-kernel-interval-assembly/v1`` artifact.

    Raises :class:`ArtifactError` on any violation.  Extra top-level fields
    beyond the required schema fields are permitted (e.g. an ``overlap``
    report section) and are covered by the self-hash.
    """
    if not isinstance(record, dict):
        raise ArtifactError(f"{label}: top-level value must be a JSON object")
    missing = REQUIRED_FIELDS - set(record)
    if missing:
        raise ArtifactError(f"{label}: missing required fields {sorted(missing)}")
    if record["schema_version"] != SCHEMA_VERSION:
        raise ArtifactError(
            f"{label}: schema_version must be {SCHEMA_VERSION!r}, "
            f"got {record['schema_version']!r}"
        )
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
    if first[1] < second[0]:
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
    if lo > hi:
        return None
    return lo, hi


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
                raise OverlapError(
                    _gap_report(i, j, intervals_a[flat], intervals_b[flat],
                                kind="route_intersection")
                )
            merged.append(enclosure)

        symmetrization_narrowed = 0
        for i in range(-N, N + 1):
            for j in range(i + 1, N + 1):
                upper = entry_index(i, j, N)
                lower = entry_index(j, i, N)
                enclosure = _intersect(merged[upper], merged[lower])
                if enclosure is None:
                    raise OverlapError(
                        _gap_report(i, j, merged[upper], merged[lower],
                                    kind="symmetrization")
                    )
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
        created_utc = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    payload: Dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "c": artifact_a["c"],
        "N": N,
        "dimension": dimension,
        "route": f"overlap({route_a}|{route_b})",
        "prec_bits": min(artifact_a["prec_bits"], artifact_b["prec_bits"]),
        "index_convention": INDEX_CONVENTION,
        "entries": [
            [_decimal_str(lo), _decimal_str(hi)] for lo, hi in merged
        ],
        "provenance": {
            "generator": GENERATOR,
            "note": (
                "entrywise intersection of two independent interval assemblies, "
                "symmetrized by intersection across the transpose; enclosures "
                "remain strict because intersection endpoints are selected, "
                "never rounded"
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
    args = parser.parse_args(argv)

    try:
        record = write_merged_artifact(args.a, args.b, args.out)
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
