"""Deterministic sharded artifacts for full finite Weil matrix assemblies.

Route generation requires python-flint through ``weil_extremal_interval_overlap``.
All artifact verification and cross-route comparison use only the Python
standard library and exact ``Fraction`` arithmetic.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import os
import struct
import zlib
from fractions import Fraction
from pathlib import Path
from typing import Any, Callable, Mapping, Sequence

from experiments.rh import weil_extremal_interval_overlap as overlap


ROUTE_MANIFEST_SCHEMA = "weil-extremal-kernel-arb-route-shards/v1"
ROUTE_TILE_SCHEMA = "weil-extremal-kernel-arb-route-tile/v1"
CROSS_MANIFEST_SCHEMA = (
    "weil-extremal-kernel-arb-cross-precision-shards/v1"
)
CROSS_TILE_SCHEMA = "weil-extremal-kernel-arb-cross-precision-tile/v1"
CLAIM_SCOPE = "finite-sharded-arb-matrix-only"
GATE_A_STATUS = "not_satisfied"
ROUTE_NAMES = ("auxiliary_s_cc_xc", "ccm_hypergeometric_lerch")
LEVEL_NAMES = ("low", "high")
CROSS_FLAG_NAMES = (
    "all_high_route_entries_overlap",
    "all_intersection_entries_contained",
    "all_intersection_entries_strictly_narrower",
    "all_low_route_entries_overlap",
    "all_route_entries_contained",
    "all_route_entries_strictly_narrower",
    "all_symmetric_intersections_nonempty",
)
ROUTE_LIMITATIONS = [
    "A route artifact records one finite Arb matrix enclosure only.",
    "It does not by itself establish agreement with the independent route.",
    "It contains no exact LDL certificate, analytic tail budget, or basis-change transfer.",
    "It makes no statement about the Riemann Hypothesis.",
]
CROSS_LIMITATIONS = [
    "Both formula routes use the same python-flint Arb runtime.",
    "The artifact certifies finite entrywise overlap and precision narrowing only.",
    "It contains no exact or interval LDL sign certificate for the full matrix.",
    "It contains no analytic tail budget, basis-change transfer, or infinite-dimensional argument.",
    "It makes no statement about the Riemann Hypothesis.",
]

Matrix = tuple[tuple[Fraction, ...], ...]
BoundsAccessor = Callable[[int, int], tuple[Fraction, Fraction]]


def _canonical_json(value: Mapping[str, Any]) -> str:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
        allow_nan=False,
    )


def _canonical_bytes(value: Mapping[str, Any]) -> bytes:
    return (_canonical_json(value) + "\n").encode("ascii")


def _payload_digest(payload: Mapping[str, Any]) -> str:
    return hashlib.sha256(_canonical_json(payload).encode("ascii")).hexdigest()


def _file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _source_sha256() -> str:
    return _file_sha256(Path(__file__))


def _formula_source_sha256() -> str:
    return _file_sha256(Path(overlap.__file__))


def _format_fraction(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def _parse_fraction(value: Any) -> Fraction | None:
    if not isinstance(value, str):
        return None
    try:
        parsed = Fraction(value)
    except (ValueError, ZeroDivisionError):
        return None
    return parsed if _format_fraction(parsed) == value else None


def _format_matrix(matrix: Matrix) -> list[list[str]]:
    return [[_format_fraction(value) for value in row] for row in matrix]


def _parse_rectangular_matrix(
    value: Any, rows: int, columns: int
) -> Matrix | None:
    if (
        not isinstance(value, list)
        or len(value) != rows
        or any(not isinstance(row, list) or len(row) != columns for row in value)
    ):
        return None
    parsed_rows = []
    for row in value:
        parsed = tuple(_parse_fraction(entry) for entry in row)
        if any(entry is None for entry in parsed):
            return None
        parsed_rows.append(parsed)
    return tuple(parsed_rows)  # type: ignore[return-value]


def _deterministic_gzip(data: bytes) -> bytes:
    compressor = zlib.compressobj(level=9, wbits=-zlib.MAX_WBITS)
    compressed = compressor.compress(data) + compressor.flush()
    header = b"\x1f\x8b\x08\x00\x00\x00\x00\x00\x02\xff"
    trailer = struct.pack("<II", zlib.crc32(data) & 0xFFFFFFFF, len(data) & 0xFFFFFFFF)
    return header + compressed + trailer


def _write_compressed_record(path: Path, payload: Mapping[str, Any]) -> dict[str, Any]:
    record = {**payload, "payload_sha256": _payload_digest(payload)}
    raw = _canonical_bytes(record)
    compressed = _deterministic_gzip(raw)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(compressed)
    return {
        "compressed_bytes": len(compressed),
        "compressed_sha256": hashlib.sha256(compressed).hexdigest(),
        "content_sha256": hashlib.sha256(raw).hexdigest(),
        "uncompressed_bytes": len(raw),
    }


def _read_compressed_record(path: Path) -> tuple[dict[str, Any], bytes] | None:
    try:
        compressed = path.read_bytes()
        raw = gzip.decompress(compressed)
        record = json.loads(
            raw,
            parse_constant=lambda value: (_ for _ in ()).throw(
                ValueError(f"non-finite JSON constant: {value}")
            ),
        )
        canonical = _canonical_bytes(record)
    except (OSError, EOFError, TypeError, UnicodeError, ValueError):
        return None
    if not isinstance(record, dict) or raw != canonical:
        return None
    payload_sha256 = record.get("payload_sha256")
    if not isinstance(payload_sha256, str):
        return None
    payload = {key: value for key, value in record.items() if key != "payload_sha256"}
    try:
        if _payload_digest(payload) != payload_sha256:
            return None
    except (TypeError, ValueError):
        return None
    return record, raw


def _write_manifest(path: Path, payload: Mapping[str, Any]) -> dict[str, Any]:
    record = {**payload, "payload_sha256": _payload_digest(payload)}
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(_canonical_bytes(record))
    return record


def _read_manifest(path: Path) -> dict[str, Any] | None:
    try:
        source = path.read_bytes()
        record = json.loads(
            source,
            parse_constant=lambda value: (_ for _ in ()).throw(
                ValueError(f"non-finite JSON constant: {value}")
            ),
        )
        canonical = _canonical_bytes(record)
    except (OSError, TypeError, UnicodeError, ValueError):
        return None
    if not isinstance(record, dict) or source != canonical:
        return None
    payload_sha256 = record.get("payload_sha256")
    if not isinstance(payload_sha256, str):
        return None
    payload = {key: value for key, value in record.items() if key != "payload_sha256"}
    try:
        return record if _payload_digest(payload) == payload_sha256 else None
    except (TypeError, ValueError):
        return None


def _require_plain_int(value: Any, name: str, minimum: int) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < minimum:
        raise ValueError(f"{name} must be an integer at least {minimum}")
    return value


def _tile_bounds(dimension: int, tile_size: int) -> tuple[dict[str, int], ...]:
    tiles = []
    for row_start in range(0, dimension, tile_size):
        row_end = min(row_start + tile_size, dimension)
        for col_start in range(0, dimension, tile_size):
            col_end = min(col_start + tile_size, dimension)
            tiles.append(
                {
                    "col_end": col_end,
                    "col_start": col_start,
                    "row_end": row_end,
                    "row_start": row_start,
                }
            )
    return tuple(tiles)


def _tile_name(tile: Mapping[str, int]) -> str:
    return (
        f"tile-r{tile['row_start']:04d}-r{tile['row_end']:04d}"
        f"-c{tile['col_start']:04d}-c{tile['col_end']:04d}.json.gz"
    )


def _route_parameters(
    *,
    c: int,
    N: int,
    prec_bits: int,
    decimal_enclosure_digits: int,
    python_flint_version: str,
    route: str,
    tile_size: int,
) -> dict[str, Any]:
    return {
        "N": N,
        "c": c,
        "decimal_enclosure_digits": decimal_enclosure_digits,
        "dimension": 2 * N + 1,
        "index_order": list(range(-N, N + 1)),
        "prec_bits": prec_bits,
        "python_flint_version": python_flint_version,
        "route": route,
        "tile_size": tile_size,
    }


def _write_route_artifact_from_accessor(
    output_dir: Path,
    bounds_at: BoundsAccessor,
    *,
    c: int,
    N: int,
    prec_bits: int,
    decimal_enclosure_digits: int,
    python_flint_version: str,
    route: str,
    tile_size: int,
) -> dict[str, Any]:
    if route not in ROUTE_NAMES:
        raise ValueError(f"route must be one of {ROUTE_NAMES}")
    _require_plain_int(c, "c", 2)
    _require_plain_int(N, "N", 0)
    _require_plain_int(prec_bits, "prec_bits", 128)
    _require_plain_int(
        decimal_enclosure_digits, "decimal_enclosure_digits", 30
    )
    _require_plain_int(tile_size, "tile_size", 1)
    if not isinstance(python_flint_version, str) or not python_flint_version:
        raise ValueError("python_flint_version must be a nonempty string")

    dimension = 2 * N + 1
    parameters = _route_parameters(
        c=c,
        N=N,
        prec_bits=prec_bits,
        decimal_enclosure_digits=decimal_enclosure_digits,
        python_flint_version=python_flint_version,
        route=route,
        tile_size=tile_size,
    )
    descriptors = []
    all_intervals_nonempty = True
    entry_count = 0
    for tile in _tile_bounds(dimension, tile_size):
        lower_rows = []
        upper_rows = []
        for i in range(tile["row_start"], tile["row_end"]):
            lower_row = []
            upper_row = []
            for j in range(tile["col_start"], tile["col_end"]):
                lower, upper = bounds_at(i, j)
                if not isinstance(lower, Fraction) or not isinstance(upper, Fraction):
                    raise TypeError("bounds accessor must return Fraction endpoints")
                if lower > upper:
                    all_intervals_nonempty = False
                lower_row.append(lower)
                upper_row.append(upper)
            lower_rows.append(tuple(lower_row))
            upper_rows.append(tuple(upper_row))
        rows = tile["row_end"] - tile["row_start"]
        columns = tile["col_end"] - tile["col_start"]
        tile_entry_count = rows * columns
        payload = {
            "enclosure": {
                "lower": _format_matrix(tuple(lower_rows)),
                "upper": _format_matrix(tuple(upper_rows)),
            },
            "parameters": parameters,
            "result": {
                "all_intervals_nonempty": all(
                    lower_rows[i][j] <= upper_rows[i][j]
                    for i in range(rows)
                    for j in range(columns)
                ),
                "entry_count": tile_entry_count,
            },
            "schema_version": ROUTE_TILE_SCHEMA,
            "tile": dict(tile),
        }
        relative_path = Path("chunks") / _tile_name(tile)
        storage = _write_compressed_record(output_dir / relative_path, payload)
        descriptors.append(
            {
                **storage,
                "entry_count": tile_entry_count,
                "path": relative_path.as_posix(),
                "tile": dict(tile),
            }
        )
        entry_count += tile_entry_count

    expected_entries = dimension * dimension
    complete_partition = entry_count == expected_entries
    payload = {
        "chunks": descriptors,
        "claim_scope": CLAIM_SCOPE,
        "formula_source_sha256": _formula_source_sha256(),
        "gate_a_status": GATE_A_STATUS,
        "generator_sha256": _source_sha256(),
        "limitations": ROUTE_LIMITATIONS,
        "parameters": parameters,
        "result": {
            "all_intervals_nonempty": all_intervals_nonempty,
            "chunk_count": len(descriptors),
            "complete_partition": complete_partition,
            "entry_count": entry_count,
        },
        "schema_version": ROUTE_MANIFEST_SCHEMA,
    }
    if not all_intervals_nonempty or not complete_partition:
        raise ValueError("route artifact did not produce a complete nonempty enclosure")
    return _write_manifest(output_dir / "manifest.json", payload)


def write_rational_route_artifact(
    output_dir: str | Path,
    lower: Sequence[Sequence[Fraction]],
    upper: Sequence[Sequence[Fraction]],
    *,
    c: int,
    N: int,
    prec_bits: int,
    decimal_enclosure_digits: int,
    python_flint_version: str,
    route: str,
    tile_size: int,
) -> dict[str, Any]:
    dimension = 2 * N + 1
    if (
        len(lower) != dimension
        or len(upper) != dimension
        or any(len(row) != dimension for row in lower)
        or any(len(row) != dimension for row in upper)
    ):
        raise ValueError("rational bounds must match dimension 2*N+1")
    checked_lower = tuple(
        tuple(value if isinstance(value, Fraction) else Fraction(value) for value in row)
        for row in lower
    )
    checked_upper = tuple(
        tuple(value if isinstance(value, Fraction) else Fraction(value) for value in row)
        for row in upper
    )
    return _write_route_artifact_from_accessor(
        Path(output_dir),
        lambda i, j: (checked_lower[i][j], checked_upper[i][j]),
        c=c,
        N=N,
        prec_bits=prec_bits,
        decimal_enclosure_digits=decimal_enclosure_digits,
        python_flint_version=python_flint_version,
        route=route,
        tile_size=tile_size,
    )


def generate_route_artifact(
    output_dir: str | Path,
    *,
    c: int,
    N: int,
    prec_bits: int,
    decimal_enclosure_digits: int,
    route: str,
    tile_size: int,
) -> dict[str, Any]:
    _arb, _acb, _ctx, flint_version = overlap._flint()
    if route == "auxiliary_s_cc_xc":
        entries = overlap.assemble_auxiliary_s_cc_xc(
            c, N, prec_bits, decimal_enclosure_digits
        )
    elif route == "ccm_hypergeometric_lerch":
        entries = overlap.assemble_ccm_hypergeometric_lerch(
            c, N, prec_bits, decimal_enclosure_digits
        )
    else:
        raise ValueError(f"route must be one of {ROUTE_NAMES}")
    indices = tuple(range(-N, N + 1))
    expected_entries = {(i, j) for i in indices for j in indices}
    if set(entries) != expected_entries:
        raise ValueError("assembled route is missing ordered matrix entries")

    def bounds_at(i: int, j: int) -> tuple[Fraction, Fraction]:
        return overlap.arb_fraction_bounds(
            entries[(indices[i], indices[j])], decimal_enclosure_digits
        )

    return _write_route_artifact_from_accessor(
        Path(output_dir),
        bounds_at,
        c=c,
        N=N,
        prec_bits=prec_bits,
        decimal_enclosure_digits=decimal_enclosure_digits,
        python_flint_version=flint_version,
        route=route,
        tile_size=tile_size,
    )


def _valid_tile(tile: Any, dimension: int) -> bool:
    if not isinstance(tile, dict) or set(tile) != {
        "col_end",
        "col_start",
        "row_end",
        "row_start",
    }:
        return False
    values = tuple(tile[key] for key in sorted(tile))
    if any(isinstance(value, bool) or not isinstance(value, int) for value in values):
        return False
    return (
        0 <= tile["row_start"] < tile["row_end"] <= dimension
        and 0 <= tile["col_start"] < tile["col_end"] <= dimension
    )


def _parse_route_parameters(value: Any) -> dict[str, Any] | None:
    keys = {
        "N",
        "c",
        "decimal_enclosure_digits",
        "dimension",
        "index_order",
        "prec_bits",
        "python_flint_version",
        "route",
        "tile_size",
    }
    if not isinstance(value, dict) or set(value) != keys:
        return None
    integer_keys = (
        "N",
        "c",
        "decimal_enclosure_digits",
        "dimension",
        "prec_bits",
        "tile_size",
    )
    if any(
        isinstance(value[key], bool) or not isinstance(value[key], int)
        for key in integer_keys
    ):
        return None
    N = value["N"]
    if (
        N < 0
        or value["c"] < 2
        or value["decimal_enclosure_digits"] < 30
        or value["prec_bits"] < 128
        or value["tile_size"] < 1
        or value["dimension"] != 2 * N + 1
        or value["index_order"] != list(range(-N, N + 1))
        or value["route"] not in ROUTE_NAMES
        or not isinstance(value["python_flint_version"], str)
        or not value["python_flint_version"]
    ):
        return None
    return value


def _resolve_artifact_path(root: Path, relative: Any) -> Path | None:
    if not isinstance(relative, str):
        return None
    candidate = Path(relative)
    if candidate.is_absolute() or ".." in candidate.parts:
        return None
    resolved_root = root.resolve()
    resolved = (root / candidate).resolve()
    try:
        resolved.relative_to(resolved_root)
    except ValueError:
        return None
    return resolved


def _verify_storage_descriptor(
    root: Path, descriptor: Any, expected_tile: Mapping[str, int]
) -> tuple[dict[str, Any], Matrix, Matrix] | None:
    descriptor_keys = {
        "compressed_bytes",
        "compressed_sha256",
        "content_sha256",
        "entry_count",
        "path",
        "tile",
        "uncompressed_bytes",
    }
    if not isinstance(descriptor, dict) or set(descriptor) != descriptor_keys:
        return None
    if descriptor["tile"] != dict(expected_tile):
        return None
    if any(
        type(descriptor[key]) is not int
        for key in (
            "compressed_bytes",
            "entry_count",
            "uncompressed_bytes",
        )
    ):
        return None
    path = _resolve_artifact_path(root, descriptor["path"])
    if path is None:
        return None
    try:
        compressed = path.read_bytes()
    except OSError:
        return None
    if (
        descriptor["compressed_bytes"] != len(compressed)
        or descriptor["compressed_sha256"]
        != hashlib.sha256(compressed).hexdigest()
    ):
        return None
    parsed = _read_compressed_record(path)
    if parsed is None:
        return None
    record, raw = parsed
    if (
        descriptor["content_sha256"] != hashlib.sha256(raw).hexdigest()
        or descriptor["uncompressed_bytes"] != len(raw)
    ):
        return None
    rows = expected_tile["row_end"] - expected_tile["row_start"]
    columns = expected_tile["col_end"] - expected_tile["col_start"]
    expected_entry_count = rows * columns
    if (
        descriptor["entry_count"] != expected_entry_count
        or record.get("schema_version") != ROUTE_TILE_SCHEMA
        or record.get("tile") != dict(expected_tile)
    ):
        return None
    enclosure = record.get("enclosure")
    result = record.get("result")
    if (
        not isinstance(enclosure, dict)
        or set(enclosure) != {"lower", "upper"}
        or not isinstance(result, dict)
        or set(result) != {"all_intervals_nonempty", "entry_count"}
        or type(result["all_intervals_nonempty"]) is not bool
        or type(result["entry_count"]) is not int
        or result["entry_count"] != expected_entry_count
    ):
        return None
    lower = _parse_rectangular_matrix(enclosure["lower"], rows, columns)
    upper = _parse_rectangular_matrix(enclosure["upper"], rows, columns)
    if lower is None or upper is None:
        return None
    all_nonempty = all(
        lower[i][j] <= upper[i][j]
        for i in range(rows)
        for j in range(columns)
    )
    if result["all_intervals_nonempty"] != all_nonempty or not all_nonempty:
        return None
    return record, lower, upper


def verify_route_artifact(record: Any, manifest_path: str | Path) -> bool:
    required_keys = {
        "chunks",
        "claim_scope",
        "formula_source_sha256",
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
        record["schema_version"] != ROUTE_MANIFEST_SCHEMA
        or record["claim_scope"] != CLAIM_SCOPE
        or record["gate_a_status"] != GATE_A_STATUS
        or record["limitations"] != ROUTE_LIMITATIONS
        or record["generator_sha256"] != _source_sha256()
        or record["formula_source_sha256"] != _formula_source_sha256()
    ):
        return False
    payload = {key: value for key, value in record.items() if key != "payload_sha256"}
    try:
        if _payload_digest(payload) != record["payload_sha256"]:
            return False
    except (KeyError, TypeError, ValueError):
        return False
    parameters = _parse_route_parameters(record["parameters"])
    if parameters is None or not isinstance(record["chunks"], list):
        return False
    expected_tiles = _tile_bounds(
        parameters["dimension"], parameters["tile_size"]
    )
    if len(record["chunks"]) != len(expected_tiles):
        return False
    root = Path(manifest_path).parent
    entry_count = 0
    for descriptor, tile in zip(record["chunks"], expected_tiles):
        parsed = _verify_storage_descriptor(root, descriptor, tile)
        if parsed is None:
            return False
        chunk_record, _lower, _upper = parsed
        if chunk_record.get("parameters") != parameters:
            return False
        entry_count += descriptor["entry_count"]
    expected_result = {
        "all_intervals_nonempty": True,
        "chunk_count": len(expected_tiles),
        "complete_partition": entry_count
        == parameters["dimension"] * parameters["dimension"],
        "entry_count": entry_count,
    }
    result = record["result"]
    return (
        isinstance(result, dict)
        and set(result) == set(expected_result)
        and all(type(result[key]) is type(expected_result[key]) for key in result)
        and result == expected_result
        and all(
            (
                expected_result["all_intervals_nonempty"],
                expected_result["complete_partition"],
            )
        )
    )


def verify_route_artifact_file(path: str | Path) -> bool:
    manifest_path = Path(path)
    record = _read_manifest(manifest_path)
    return record is not None and verify_route_artifact(record, manifest_path)


def _route_source(manifest_path: Path) -> dict[str, Any]:
    record = _read_manifest(manifest_path)
    if record is None or not verify_route_artifact(record, manifest_path):
        raise ValueError(f"route manifest is not canonical and valid: {manifest_path}")
    descriptors = {
        (
            descriptor["tile"]["row_start"],
            descriptor["tile"]["col_start"],
        ): descriptor
        for descriptor in record["chunks"]
    }
    return {
        "descriptors": descriptors,
        "manifest_path": manifest_path,
        "record": record,
        "root": manifest_path.parent,
    }


def _route_tile(
    source: Mapping[str, Any], row_start: int, col_start: int
) -> tuple[Matrix, Matrix]:
    descriptor = source["descriptors"][(row_start, col_start)]
    parsed = _verify_storage_descriptor(
        source["root"], descriptor, descriptor["tile"]
    )
    if parsed is None:
        raise ValueError("route tile changed after manifest verification")
    _record, lower, upper = parsed
    return lower, upper


def _intersection_bounds(
    left_lower: Fraction,
    left_upper: Fraction,
    right_lower: Fraction,
    right_upper: Fraction,
) -> tuple[Fraction, Fraction]:
    return max(left_lower, right_lower), min(left_upper, right_upper)


def _contained_and_strict(
    low_lower: Fraction,
    low_upper: Fraction,
    high_lower: Fraction,
    high_upper: Fraction,
) -> tuple[bool, bool]:
    return (
        low_lower <= high_lower and high_upper <= low_upper,
        high_upper - high_lower < low_upper - low_lower,
    )


def _cross_tile_payload(
    tile: Mapping[str, int],
    parameters: Mapping[str, Any],
    current: Mapping[tuple[str, str], tuple[Matrix, Matrix]],
    transposed: Mapping[tuple[str, str], tuple[Matrix, Matrix]],
) -> dict[str, Any]:
    rows = tile["row_end"] - tile["row_start"]
    columns = tile["col_end"] - tile["col_start"]
    low_lower_rows = []
    low_upper_rows = []
    high_lower_rows = []
    high_upper_rows = []
    flags = {key: True for key in CROSS_FLAG_NAMES}

    for local_i in range(rows):
        low_lower_row = []
        low_upper_row = []
        high_lower_row = []
        high_upper_row = []
        global_i = tile["row_start"] + local_i
        for local_j in range(columns):
            global_j = tile["col_start"] + local_j
            transpose_i = global_j - tile["col_start"]
            transpose_j = global_i - tile["row_start"]
            symmetric = {}
            for level in LEVEL_NAMES:
                auxiliary = current[(level, "auxiliary_s_cc_xc")]
                ccm = current[(level, "ccm_hypergeometric_lerch")]
                raw_lower, raw_upper = _intersection_bounds(
                    auxiliary[0][local_i][local_j],
                    auxiliary[1][local_i][local_j],
                    ccm[0][local_i][local_j],
                    ccm[1][local_i][local_j],
                )
                auxiliary_t = transposed[(level, "auxiliary_s_cc_xc")]
                ccm_t = transposed[(level, "ccm_hypergeometric_lerch")]
                raw_t_lower, raw_t_upper = _intersection_bounds(
                    auxiliary_t[0][transpose_i][transpose_j],
                    auxiliary_t[1][transpose_i][transpose_j],
                    ccm_t[0][transpose_i][transpose_j],
                    ccm_t[1][transpose_i][transpose_j],
                )
                symmetric[level] = (
                    max(raw_lower, raw_t_lower),
                    min(raw_upper, raw_t_upper),
                )
                overlap_flag = raw_lower <= raw_upper
                overlap_t_flag = raw_t_lower <= raw_t_upper
                flags[
                    f"all_{level}_route_entries_overlap"
                ] &= overlap_flag and overlap_t_flag
                flags["all_symmetric_intersections_nonempty"] &= (
                    symmetric[level][0] <= symmetric[level][1]
                )

            for route in ROUTE_NAMES:
                low = current[("low", route)]
                high = current[("high", route)]
                contained, strict = _contained_and_strict(
                    low[0][local_i][local_j],
                    low[1][local_i][local_j],
                    high[0][local_i][local_j],
                    high[1][local_i][local_j],
                )
                flags["all_route_entries_contained"] &= contained
                flags["all_route_entries_strictly_narrower"] &= strict

            contained, strict = _contained_and_strict(
                symmetric["low"][0],
                symmetric["low"][1],
                symmetric["high"][0],
                symmetric["high"][1],
            )
            flags["all_intersection_entries_contained"] &= contained
            flags["all_intersection_entries_strictly_narrower"] &= strict
            low_lower_row.append(symmetric["low"][0])
            low_upper_row.append(symmetric["low"][1])
            high_lower_row.append(symmetric["high"][0])
            high_upper_row.append(symmetric["high"][1])
        low_lower_rows.append(tuple(low_lower_row))
        low_upper_rows.append(tuple(low_upper_row))
        high_lower_rows.append(tuple(high_lower_row))
        high_upper_rows.append(tuple(high_upper_row))

    return {
        "intersection": {
            "high": {
                "lower": _format_matrix(tuple(high_lower_rows)),
                "upper": _format_matrix(tuple(high_upper_rows)),
            },
            "low": {
                "lower": _format_matrix(tuple(low_lower_rows)),
                "upper": _format_matrix(tuple(low_upper_rows)),
            },
        },
        "parameters": dict(parameters),
        "result": {**flags, "entry_count": rows * columns},
        "schema_version": CROSS_TILE_SCHEMA,
        "tile": dict(tile),
    }


def _relative_manifest_path(output_dir: Path, manifest_path: Path) -> str:
    try:
        return manifest_path.resolve().relative_to(output_dir.resolve()).as_posix()
    except ValueError as error:
        raise ValueError("source route manifests must be inside output_dir") from error


def _compatible_cross_sources(
    sources: Mapping[tuple[str, str], Mapping[str, Any]]
) -> dict[str, Any]:
    parameters = {
        key: source["record"]["parameters"] for key, source in sources.items()
    }
    first = parameters[("low", "auxiliary_s_cc_xc")]
    common_keys = (
        "N",
        "c",
        "decimal_enclosure_digits",
        "dimension",
        "index_order",
        "python_flint_version",
        "tile_size",
    )
    if any(
        any(value[key] != first[key] for key in common_keys)
        for value in parameters.values()
    ):
        raise ValueError("route manifests do not share matrix/grid parameters")
    for level in LEVEL_NAMES:
        for route in ROUTE_NAMES:
            value = parameters[(level, route)]
            if value["route"] != route:
                raise ValueError("route manifest is assigned to the wrong route")
    low_prec = parameters[("low", ROUTE_NAMES[0])]["prec_bits"]
    high_prec = parameters[("high", ROUTE_NAMES[0])]["prec_bits"]
    if any(parameters[("low", route)]["prec_bits"] != low_prec for route in ROUTE_NAMES):
        raise ValueError("low route precisions differ")
    if any(
        parameters[("high", route)]["prec_bits"] != high_prec
        for route in ROUTE_NAMES
    ):
        raise ValueError("high route precisions differ")
    if high_prec < low_prec + 512:
        raise ValueError("high precision must exceed low precision by at least 512 bits")
    return {
        "N": first["N"],
        "c": first["c"],
        "decimal_enclosure_digits": first["decimal_enclosure_digits"],
        "dimension": first["dimension"],
        "high_prec_bits": high_prec,
        "index_order": first["index_order"],
        "low_prec_bits": low_prec,
        "python_flint_version": first["python_flint_version"],
        "tile_size": first["tile_size"],
    }


def write_cross_precision_artifact(
    output_dir: str | Path,
    *,
    low_auxiliary_manifest: str | Path,
    low_ccm_manifest: str | Path,
    high_auxiliary_manifest: str | Path,
    high_ccm_manifest: str | Path,
) -> dict[str, Any]:
    output = Path(output_dir)
    manifest_paths = {
        ("low", "auxiliary_s_cc_xc"): Path(low_auxiliary_manifest),
        ("low", "ccm_hypergeometric_lerch"): Path(low_ccm_manifest),
        ("high", "auxiliary_s_cc_xc"): Path(high_auxiliary_manifest),
        ("high", "ccm_hypergeometric_lerch"): Path(high_ccm_manifest),
    }
    sources = {key: _route_source(path) for key, path in manifest_paths.items()}
    parameters = _compatible_cross_sources(sources)
    dimension = parameters["dimension"]
    tile_size = parameters["tile_size"]
    descriptors = []
    aggregate = {key: True for key in CROSS_FLAG_NAMES}
    entry_count = 0
    for tile in _tile_bounds(dimension, tile_size):
        row_start = tile["row_start"]
        col_start = tile["col_start"]
        current = {
            key: _route_tile(source, row_start, col_start)
            for key, source in sources.items()
        }
        transposed = {
            key: _route_tile(source, col_start, row_start)
            for key, source in sources.items()
        }
        payload = _cross_tile_payload(tile, parameters, current, transposed)
        for key in aggregate:
            aggregate[key] &= payload["result"][key]
        tile_entry_count = payload["result"]["entry_count"]
        relative_path = Path("cross-chunks") / _tile_name(tile)
        storage = _write_compressed_record(output / relative_path, payload)
        descriptors.append(
            {
                **storage,
                "entry_count": tile_entry_count,
                "path": relative_path.as_posix(),
                "tile": dict(tile),
            }
        )
        entry_count += tile_entry_count

    source_records = {
        level: {
            route: {
                "manifest_sha256": _file_sha256(
                    manifest_paths[(level, route)]
                ),
                "path": _relative_manifest_path(
                    output, manifest_paths[(level, route)]
                ),
            }
            for route in ROUTE_NAMES
        }
        for level in LEVEL_NAMES
    }
    result = {
        **aggregate,
        "chunk_count": len(descriptors),
        "entry_count": entry_count,
    }
    if not all(aggregate.values()) or entry_count != dimension * dimension:
        raise ValueError("full cross-precision comparison did not pass")
    payload = {
        "chunks": descriptors,
        "claim_scope": CLAIM_SCOPE,
        "formula_source_sha256": _formula_source_sha256(),
        "gate_a_status": GATE_A_STATUS,
        "generator_sha256": _source_sha256(),
        "limitations": CROSS_LIMITATIONS,
        "parameters": parameters,
        "result": result,
        "schema_version": CROSS_MANIFEST_SCHEMA,
        "source_routes": source_records,
    }
    return _write_manifest(output / "manifest.json", payload)


def _load_cross_sources(
    record: Mapping[str, Any], manifest_path: Path
) -> dict[tuple[str, str], dict[str, Any]] | None:
    source_routes = record.get("source_routes")
    if (
        not isinstance(source_routes, dict)
        or set(source_routes) != set(LEVEL_NAMES)
    ):
        return None
    sources = {}
    root = manifest_path.parent
    for level in LEVEL_NAMES:
        level_record = source_routes[level]
        if not isinstance(level_record, dict) or set(level_record) != set(ROUTE_NAMES):
            return None
        for route in ROUTE_NAMES:
            descriptor = level_record[route]
            if not isinstance(descriptor, dict) or set(descriptor) != {
                "manifest_sha256",
                "path",
            }:
                return None
            path = _resolve_artifact_path(root, descriptor["path"])
            if (
                path is None
                or not isinstance(descriptor["manifest_sha256"], str)
                or not path.is_file()
                or _file_sha256(path) != descriptor["manifest_sha256"]
            ):
                return None
            try:
                sources[(level, route)] = _route_source(path)
            except ValueError:
                return None
    return sources


def _verify_cross_chunk_descriptor(
    root: Path,
    descriptor: Any,
    tile: Mapping[str, int],
    parameters: Mapping[str, Any],
    sources: Mapping[tuple[str, str], Mapping[str, Any]],
) -> dict[str, Any] | None:
    descriptor_keys = {
        "compressed_bytes",
        "compressed_sha256",
        "content_sha256",
        "entry_count",
        "path",
        "tile",
        "uncompressed_bytes",
    }
    if not isinstance(descriptor, dict) or set(descriptor) != descriptor_keys:
        return None
    if descriptor["tile"] != dict(tile):
        return None
    rows = tile["row_end"] - tile["row_start"]
    columns = tile["col_end"] - tile["col_start"]
    expected_entry_count = rows * columns
    if (
        any(
            type(descriptor[key]) is not int
            for key in (
                "compressed_bytes",
                "entry_count",
                "uncompressed_bytes",
            )
        )
        or descriptor["entry_count"] != expected_entry_count
    ):
        return None
    path = _resolve_artifact_path(root, descriptor["path"])
    if path is None:
        return None
    try:
        compressed = path.read_bytes()
    except OSError:
        return None
    parsed = _read_compressed_record(path)
    if parsed is None:
        return None
    stored, raw = parsed
    if (
        descriptor["compressed_bytes"] != len(compressed)
        or descriptor["compressed_sha256"]
        != hashlib.sha256(compressed).hexdigest()
        or descriptor["content_sha256"] != hashlib.sha256(raw).hexdigest()
        or descriptor["uncompressed_bytes"] != len(raw)
    ):
        return None
    current = {
        key: _route_tile(source, tile["row_start"], tile["col_start"])
        for key, source in sources.items()
    }
    transposed = {
        key: _route_tile(source, tile["col_start"], tile["row_start"])
        for key, source in sources.items()
    }
    expected_payload = _cross_tile_payload(
        tile, parameters, current, transposed
    )
    expected = {
        **expected_payload,
        "payload_sha256": _payload_digest(expected_payload),
    }
    stored_result = stored.get("result")
    if (
        not isinstance(stored_result, dict)
        or set(stored_result) != set(CROSS_FLAG_NAMES) | {"entry_count"}
        or any(type(stored_result[key]) is not bool for key in CROSS_FLAG_NAMES)
        or type(stored_result["entry_count"]) is not int
        or stored_result["entry_count"] != expected_entry_count
    ):
        return None
    return expected["result"] if stored == expected else None


def verify_cross_precision_artifact(
    record: Any, manifest_path: str | Path
) -> bool:
    required_keys = {
        "chunks",
        "claim_scope",
        "formula_source_sha256",
        "gate_a_status",
        "generator_sha256",
        "limitations",
        "parameters",
        "payload_sha256",
        "result",
        "schema_version",
        "source_routes",
    }
    if not isinstance(record, dict) or set(record) != required_keys:
        return False
    if (
        record["schema_version"] != CROSS_MANIFEST_SCHEMA
        or record["claim_scope"] != CLAIM_SCOPE
        or record["gate_a_status"] != GATE_A_STATUS
        or record["limitations"] != CROSS_LIMITATIONS
        or record["generator_sha256"] != _source_sha256()
        or record["formula_source_sha256"] != _formula_source_sha256()
    ):
        return False
    payload = {key: value for key, value in record.items() if key != "payload_sha256"}
    try:
        if _payload_digest(payload) != record["payload_sha256"]:
            return False
    except (KeyError, TypeError, ValueError):
        return False
    manifest = Path(manifest_path)
    sources = _load_cross_sources(record, manifest)
    if sources is None:
        return False
    try:
        parameters = _compatible_cross_sources(sources)
    except ValueError:
        return False
    if record["parameters"] != parameters or not isinstance(record["chunks"], list):
        return False
    tiles = _tile_bounds(parameters["dimension"], parameters["tile_size"])
    if len(record["chunks"]) != len(tiles):
        return False
    aggregate = {key: True for key in CROSS_FLAG_NAMES}
    entry_count = 0
    for descriptor, tile in zip(record["chunks"], tiles):
        result = _verify_cross_chunk_descriptor(
            manifest.parent, descriptor, tile, parameters, sources
        )
        if result is None:
            return False
        for key in aggregate:
            if type(result.get(key)) is not bool:
                return False
            aggregate[key] &= result[key]
        entry_count += result["entry_count"]
    expected_result = {
        **aggregate,
        "chunk_count": len(tiles),
        "entry_count": entry_count,
    }
    result = record["result"]
    return (
        isinstance(result, dict)
        and set(result) == set(expected_result)
        and all(type(result[key]) is type(expected_result[key]) for key in result)
        and result == expected_result
        and all(aggregate.values())
        and entry_count == parameters["dimension"] * parameters["dimension"]
    )


def verify_cross_precision_artifact_file(path: str | Path) -> bool:
    manifest_path = Path(path)
    record = _read_manifest(manifest_path)
    return record is not None and verify_cross_precision_artifact(
        record, manifest_path
    )


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Generate or verify sharded finite Weil matrix artifacts."
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    route_parser = subparsers.add_parser("generate-route")
    route_parser.add_argument("output_dir", type=Path)
    route_parser.add_argument("--route", choices=ROUTE_NAMES, required=True)
    route_parser.add_argument("--c", type=int, required=True)
    route_parser.add_argument("--N", type=int, required=True)
    route_parser.add_argument("--prec-bits", type=int, required=True)
    route_parser.add_argument("--decimal-enclosure-digits", type=int, required=True)
    route_parser.add_argument("--tile-size", type=int, default=64)

    cross_parser = subparsers.add_parser("generate-cross")
    cross_parser.add_argument("output_dir", type=Path)
    cross_parser.add_argument("--low-auxiliary-manifest", type=Path, required=True)
    cross_parser.add_argument("--low-ccm-manifest", type=Path, required=True)
    cross_parser.add_argument("--high-auxiliary-manifest", type=Path, required=True)
    cross_parser.add_argument("--high-ccm-manifest", type=Path, required=True)

    verify_route_parser = subparsers.add_parser("verify-route")
    verify_route_parser.add_argument("manifest", type=Path)
    verify_cross_parser = subparsers.add_parser("verify-cross")
    verify_cross_parser.add_argument("manifest", type=Path)

    args = parser.parse_args(argv)
    if args.command == "generate-route":
        record = generate_route_artifact(
            args.output_dir,
            c=args.c,
            N=args.N,
            prec_bits=args.prec_bits,
            decimal_enclosure_digits=args.decimal_enclosure_digits,
            route=args.route,
            tile_size=args.tile_size,
        )
        valid = verify_route_artifact_file(args.output_dir / "manifest.json")
        print(
            "generated complete sharded Arb route artifact: "
            f"{str(valid and record['result']['complete_partition']).lower()}"
        )
        return 0 if valid else 1
    if args.command == "generate-cross":
        record = write_cross_precision_artifact(
            args.output_dir,
            low_auxiliary_manifest=args.low_auxiliary_manifest,
            low_ccm_manifest=args.low_ccm_manifest,
            high_auxiliary_manifest=args.high_auxiliary_manifest,
            high_ccm_manifest=args.high_ccm_manifest,
        )
        valid = verify_cross_precision_artifact_file(
            args.output_dir / "manifest.json"
        )
        print(
            "generated complete sharded Arb cross-precision artifact: "
            f"{str(valid and all(record['result'].values())).lower()}"
        )
        return 0 if valid else 1
    if args.command == "verify-route":
        valid = verify_route_artifact_file(args.manifest)
        print(f"valid sharded Arb route artifact: {str(valid).lower()}")
        return 0 if valid else 1
    valid = verify_cross_precision_artifact_file(args.manifest)
    print(
        "valid sharded Arb cross-precision artifact: "
        f"{str(valid).lower()}"
    )
    return 0 if valid else 1


if __name__ == "__main__":
    raise SystemExit(main())
