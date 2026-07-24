"""Streaming rigorous interval LDL checkpoints for sharded Weil matrices.

Factorization requires python-flint. Checkpoint verification uses only the
standard library and the standard-library verifier for the source artifact.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from fractions import Fraction
from pathlib import Path
from typing import Any, Mapping, Sequence

from experiments.rh import weil_extremal_interval_overlap as overlap
from experiments.rh import weil_extremal_sharded as sharded


CHECKPOINT_SCHEMA = "weil-extremal-kernel-streaming-interval-ldlt/v1"
WORKSPACE_SCHEMA = "weil-extremal-kernel-streaming-ldlt-workspace/v1"
BLOCK_SCHEMA = "weil-extremal-kernel-streaming-ldlt-block/v1"
RESUME_SCHEMA = "weil-extremal-kernel-streaming-ldlt-resume/v1"
CLAIM_SCOPE = "finite-sharded-interval-ldlt-only"
GATE_A_STATUS = "not_satisfied"
LIMITATIONS = [
    "The checkpoint concerns only the retained finite matrix intersection.",
    "An unresolved pivot is not evidence of a zero or a negative eigenvalue.",
    "A negative claim requires a separately verified exact rational witness.",
    "The standard-library verifier authenticates the transcript but does not replay Arb arithmetic.",
    "No analytic tail, basis-change transfer, infinite-dimensional criterion, or RH conclusion is included.",
]


class PanelLimitReached(RuntimeError):
    """Raised after a requested number of complete panels is checkpointed."""


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


def _payload_digest(value: Mapping[str, Any]) -> str:
    return hashlib.sha256(_canonical_json(value).encode("ascii")).hexdigest()


def _file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _source_sha256() -> str:
    return _file_sha256(Path(__file__))


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


def _plain_int(value: Any, minimum: int = 0) -> bool:
    return type(value) is int and value >= minimum


def _sha256_string(value: Any) -> bool:
    return (
        isinstance(value, str)
        and len(value) == 64
        and all(character in "0123456789abcdef" for character in value)
    )


def _relative_path(base: Path, target: Path) -> str:
    try:
        return target.resolve().relative_to(base.resolve()).as_posix()
    except ValueError:
        return os.path.relpath(target.resolve(), base.resolve())


def _resolve_path(base: Path, value: Any) -> Path | None:
    if not isinstance(value, str) or not value:
        return None
    candidate = (base / value).resolve()
    try:
        candidate.relative_to(base.resolve().anchor)
    except ValueError:
        return None
    return candidate


def _load_source(manifest_path: Path) -> tuple[dict[str, Any], dict[tuple[int, int], Any]]:
    record = sharded._read_manifest(manifest_path)
    valid = (
        record is not None
        and sharded.verify_cross_precision_artifact_file(manifest_path)
    )
    if not valid:
        from experiments.rh import weil_extremal_high_precision as high_precision

        record = high_precision._read_json_record(manifest_path)
        valid = (
            record is not None
            and high_precision.verify_cross_checkpoint_file(manifest_path)
            and record["result"]["complete"] is True
        )
    if not valid or record is None:
        raise ValueError(
            "source cross-precision artifact is not canonical, complete, and valid"
        )
    parameters = record["parameters"]
    tile_size = parameters["tile_size"]
    descriptors = {
        (item["tile"]["row_start"], item["tile"]["col_start"]): item
        for item in record["chunks"]
    }
    expected = {
        (tile["row_start"], tile["col_start"])
        for tile in sharded._tile_bounds(parameters["dimension"], tile_size)
    }
    if set(descriptors) != expected:
        raise ValueError("source cross-precision tile partition is incomplete")
    return record, descriptors


def _block_bounds(dimension: int, block_size: int) -> tuple[tuple[int, int], ...]:
    return tuple(
        (start, min(start + block_size, dimension))
        for start in range(0, dimension, block_size)
    )


def _fraction_matrix_to_arb(lower: Any, upper: Any, arb: Any, arb_mat: Any) -> Any:
    rows = len(lower)
    columns = len(lower[0]) if rows else 0
    matrix = arb_mat(rows, columns)
    for i in range(rows):
        for j in range(columns):
            lo = lower[i][j]
            hi = upper[i][j]
            if lo > hi:
                raise ValueError("serialized interval has reversed endpoints")
            matrix[i, j] = arb(_format_fraction(lo)).union(
                arb(_format_fraction(hi))
            )
    return matrix


def _parse_enclosure(value: Any, rows: int, columns: int) -> tuple[Any, Any] | None:
    if not isinstance(value, dict) or set(value) != {"lower", "upper"}:
        return None
    lower = sharded._parse_rectangular_matrix(value["lower"], rows, columns)
    upper = sharded._parse_rectangular_matrix(value["upper"], rows, columns)
    if lower is None or upper is None:
        return None
    if any(lower[i][j] > upper[i][j] for i in range(rows) for j in range(columns)):
        return None
    return lower, upper


def _arb_bounds(value: Any, digits: int) -> tuple[Fraction, Fraction]:
    return overlap.arb_fraction_bounds(value, digits)


def _serialize_arb_matrix(matrix: Any, digits: int) -> dict[str, Any]:
    lower_rows = []
    upper_rows = []
    for i in range(matrix.nrows()):
        lower_row = []
        upper_row = []
        for j in range(matrix.ncols()):
            lower, upper = _arb_bounds(matrix[i, j], digits)
            lower_row.append(_format_fraction(lower))
            upper_row.append(_format_fraction(upper))
        lower_rows.append(lower_row)
        upper_rows.append(upper_row)
    return {"lower": lower_rows, "upper": upper_rows}


class BlockStore:
    def __init__(
        self,
        source_manifest: Path,
        source_record: Mapping[str, Any],
        descriptors: Mapping[tuple[int, int], Any],
        workspace: Path,
        block_size: int,
        serialization_digits: int,
        intersection_level: str,
        arb: Any,
        arb_mat: Any,
        completed_panels: int = 0,
    ) -> None:
        self.source_manifest = source_manifest
        self.source_record = source_record
        self.descriptors = descriptors
        self.workspace = workspace
        self.block_size = block_size
        self.serialization_digits = serialization_digits
        self.intersection_level = intersection_level
        self.arb = arb
        self.arb_mat = arb_mat
        self.completed_panels = completed_panels
        self.maximum_loaded_block_entries = 0
        self.workspace.mkdir(parents=True, exist_ok=True)
        (self.workspace / "schur").mkdir(exist_ok=True)
        (self.workspace / "factors").mkdir(exist_ok=True)

    def _shape(self, block_row: int, block_col: int) -> tuple[int, int]:
        dimension = self.source_record["parameters"]["dimension"]
        bounds = _block_bounds(dimension, self.block_size)
        row_start, row_end = bounds[block_row]
        col_start, col_end = bounds[block_col]
        return row_end - row_start, col_end - col_start

    def _source_block(self, block_row: int, block_col: int) -> Any:
        row_start = block_row * self.block_size
        col_start = block_col * self.block_size
        descriptor = self.descriptors[(row_start, col_start)]
        path = self.source_manifest.parent / descriptor["path"]
        parsed = sharded._read_compressed_record(path)
        if parsed is None:
            raise ValueError("source tile changed after manifest verification")
        record, _raw = parsed
        rows, columns = self._shape(block_row, block_col)
        enclosure = _parse_enclosure(
            record.get("intersection", {}).get(self.intersection_level),
            rows,
            columns,
        )
        if enclosure is None:
            raise ValueError("source tile has invalid high intersection")
        return _fraction_matrix_to_arb(
            enclosure[0], enclosure[1], self.arb, self.arb_mat
        )

    def _block_path(
        self,
        kind: str,
        block_row: int,
        block_col: int,
        *,
        for_write: bool = False,
    ) -> Path:
        if kind == "schur":
            generation = self.completed_panels + (1 if for_write else 0)
            return (
                self.workspace
                / kind
                / f"generation-{generation:04d}"
                / f"block-r{block_row:04d}-c{block_col:04d}.json.gz"
            )
        return (
            self.workspace
            / kind
            / f"block-r{block_row:04d}-c{block_col:04d}.json.gz"
        )

    def _read_workspace_block(
        self, path: Path, block_row: int, block_col: int
    ) -> Any:
        parsed = sharded._read_compressed_record(path)
        if parsed is None:
            raise ValueError(f"invalid workspace block: {path}")
        record, _raw = parsed
        rows, columns = self._shape(block_row, block_col)
        if (
            record.get("schema_version") != BLOCK_SCHEMA
            or record.get("block") != {
                "column": block_col,
                "row": block_row,
            }
            or record.get("kind") not in {"schur", "factors"}
        ):
            raise ValueError(f"workspace block metadata mismatch: {path}")
        enclosure = _parse_enclosure(record.get("enclosure"), rows, columns)
        if enclosure is None:
            raise ValueError(f"workspace block enclosure is invalid: {path}")
        return _fraction_matrix_to_arb(
            enclosure[0], enclosure[1], self.arb, self.arb_mat
        )

    def load_schur(self, block_row: int, block_col: int) -> Any:
        path = self._block_path("schur", block_row, block_col)
        if self.completed_panels:
            if not path.is_file():
                raise ValueError(f"committed Schur block is missing: {path}")
            matrix = self._read_workspace_block(path, block_row, block_col)
        else:
            matrix = self._source_block(block_row, block_col)
        self.maximum_loaded_block_entries = max(
            self.maximum_loaded_block_entries,
            matrix.nrows() * matrix.ncols(),
        )
        return matrix

    def load_factor(self, block_row: int, block_col: int) -> Any:
        path = self._block_path("factors", block_row, block_col)
        matrix = self._read_workspace_block(path, block_row, block_col)
        self.maximum_loaded_block_entries = max(
            self.maximum_loaded_block_entries,
            matrix.nrows() * matrix.ncols(),
        )
        return matrix

    def write_block(
        self, kind: str, block_row: int, block_col: int, matrix: Any
    ) -> dict[str, Any]:
        path = self._block_path(
            kind, block_row, block_col, for_write=kind == "schur"
        )
        payload = {
            "block": {"column": block_col, "row": block_row},
            "enclosure": _serialize_arb_matrix(
                matrix, self.serialization_digits
            ),
            "kind": kind,
            "schema_version": BLOCK_SCHEMA,
        }
        return sharded._write_compressed_record(path, payload)

    def write_diagonal(
        self, block_index: int, lower: Any, diagonal: Sequence[Any]
    ) -> None:
        self.write_block("factors", block_index, block_index, lower)
        diagonal_path = (
            self.workspace
            / "factors"
            / f"diagonal-{block_index:04d}.json.gz"
        )
        bounds = [_arb_bounds(value, self.serialization_digits) for value in diagonal]
        sharded._write_compressed_record(
            diagonal_path,
            {
                "block": block_index,
                "diagonal": [
                    {
                        "lower": _format_fraction(lower_bound),
                        "upper": _format_fraction(upper_bound),
                    }
                    for lower_bound, upper_bound in bounds
                ],
                "kind": "diagonal",
                "schema_version": BLOCK_SCHEMA,
            },
        )

    def workspace_manifest(self, completed_panels: int) -> dict[str, Any]:
        descriptors = []
        for path in sorted(self.workspace.rglob("*.json.gz")):
            descriptors.append(
                {
                    "bytes": path.stat().st_size,
                    "path": path.relative_to(self.workspace).as_posix(),
                    "sha256": _file_sha256(path),
                }
            )
        payload = {
            "blocks": descriptors,
            "completed_panels": completed_panels,
            "schema_version": WORKSPACE_SCHEMA,
            "source_manifest_sha256": _file_sha256(self.source_manifest),
        }
        return sharded._write_manifest(
            self.workspace / "manifest.json", payload
        )


def _factor_diagonal_block(matrix: Any, arb: Any, arb_mat: Any) -> tuple[Any, list[Any], int | None, str | None]:
    size = matrix.nrows()
    lower = arb_mat(size, size)
    for i in range(size):
        lower[i, i] = arb(1)
    diagonal: list[Any] = []
    for column in range(size):
        pivot = matrix[column, column]
        for previous in range(column):
            pivot -= (
                lower[column, previous]
                * lower[column, previous]
                * diagonal[previous]
            )
        if not (pivot.lower() > 0):
            reason = (
                "strict_negative_pivot_without_rational_witness"
                if pivot.upper() < 0
                else "pivot_interval_contains_zero"
            )
            return lower, diagonal + [pivot], column, reason
        diagonal.append(pivot)
        for row in range(column + 1, size):
            residual = matrix[row, column]
            for previous in range(column):
                residual -= (
                    lower[row, previous]
                    * lower[column, previous]
                    * diagonal[previous]
                )
            lower[row, column] = residual / pivot
    return lower, diagonal, None, None


def _right_solve_panel(schur: Any, lower: Any, diagonal: Sequence[Any]) -> Any:
    panel = lower.solve(schur.transpose()).transpose()
    for i in range(panel.nrows()):
        for j in range(panel.ncols()):
            panel[i, j] = panel[i, j] / diagonal[j]
    return panel


def _scaled_columns(matrix: Any, diagonal: Sequence[Any], arb_mat: Any) -> Any:
    result = arb_mat(matrix.nrows(), matrix.ncols())
    for i in range(matrix.nrows()):
        for j in range(matrix.ncols()):
            result[i, j] = matrix[i, j] * diagonal[j]
    return result


def _pivot_record(index: int, pivot: Any, digits: int) -> dict[str, Any]:
    lower, upper = _arb_bounds(pivot, digits)
    sign = "positive" if lower > 0 else "negative" if upper < 0 else "unresolved"
    return {
        "index": index,
        "lower": _format_fraction(lower),
        "sign": sign,
        "upper": _format_fraction(upper),
    }


def _workspace_summary(
    workspace: Path,
    manifest: Mapping[str, Any],
    maximum_loaded_block_entries: int,
) -> dict[str, Any]:
    manifest_path = workspace / "manifest.json"
    return {
        "block_file_count": len(manifest["blocks"]),
        "manifest_payload_sha256": manifest["payload_sha256"],
        "manifest_sha256": _file_sha256(manifest_path),
        "maximum_loaded_block_entries": maximum_loaded_block_entries,
        "total_compressed_bytes": sum(item["bytes"] for item in manifest["blocks"]),
    }


def _checkpoint_source(
    checkpoint_path: Path, source_manifest: Path, source_record: Mapping[str, Any]
) -> dict[str, Any]:
    return {
        "manifest_payload_sha256": source_record["payload_sha256"],
        "manifest_sha256": _file_sha256(source_manifest),
        "path": _relative_path(checkpoint_path.parent, source_manifest),
    }


def _write_checkpoint(path: Path, payload: Mapping[str, Any]) -> dict[str, Any]:
    record = {**payload, "payload_sha256": _payload_digest(payload)}
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(_canonical_bytes(record))
    return record


def _atomic_write(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.tmp-{os.getpid()}")
    temporary.write_bytes(data)
    os.replace(temporary, path)


def _resume_parameters(
    *,
    block_size: int,
    arb_prec_bits: int,
    serialization_digits: int,
    intersection_level: str,
) -> dict[str, Any]:
    return {
        "arb_prec_bits": arb_prec_bits,
        "block_size": block_size,
        "intersection_level": intersection_level,
        "serialization_digits": serialization_digits,
    }


def _write_resume_checkpoint(
    workspace: Path,
    source_path: Path,
    source_record: Mapping[str, Any],
    parameters: Mapping[str, Any],
    completed_panels: int,
    pivots: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    payload = {
        "completed_panels": completed_panels,
        "generator_sha256": _source_sha256(),
        "parameters": dict(parameters),
        "pivots": list(pivots),
        "schema_version": RESUME_SCHEMA,
        "source_manifest_payload_sha256": source_record["payload_sha256"],
        "source_manifest_sha256": _file_sha256(source_path),
    }
    digest = _payload_digest(payload)
    snapshot_path = Path("checkpoints") / f"{digest}.json"
    record = {
        **payload,
        "payload_sha256": digest,
        "snapshot_path": snapshot_path.as_posix(),
    }
    raw = _canonical_bytes(record)
    snapshot = workspace / snapshot_path
    if snapshot.exists():
        if snapshot.read_bytes() != raw:
            raise ValueError("content-addressed resume checkpoint collision")
    else:
        _atomic_write(snapshot, raw)
    _atomic_write(workspace / "resume.json", raw)
    return record


def _load_resume_checkpoint(
    workspace: Path,
    source_path: Path,
    source_record: Mapping[str, Any],
    parameters: Mapping[str, Any],
    blocks: Sequence[tuple[int, int]],
) -> tuple[int, list[dict[str, Any]]]:
    path = workspace / "resume.json"
    try:
        raw = path.read_bytes()
        record = json.loads(raw)
    except (OSError, TypeError, UnicodeError, ValueError) as error:
        raise ValueError("resume checkpoint is missing or invalid") from error
    required = {
        "completed_panels",
        "generator_sha256",
        "parameters",
        "payload_sha256",
        "pivots",
        "schema_version",
        "snapshot_path",
        "source_manifest_payload_sha256",
        "source_manifest_sha256",
    }
    payload = {
        key: value
        for key, value in record.items()
        if key not in {"payload_sha256", "snapshot_path"}
    }
    completed = record.get("completed_panels")
    expected_pivots = (
        sum(end - start for start, end in blocks[:completed])
        if type(completed) is int and 0 <= completed <= len(blocks)
        else -1
    )
    snapshot = workspace / str(record.get("snapshot_path", ""))
    if (
        not isinstance(record, dict)
        or set(record) != required
        or raw != _canonical_bytes(record)
        or record["schema_version"] != RESUME_SCHEMA
        or record["generator_sha256"] != _source_sha256()
        or record["parameters"] != dict(parameters)
        or record["source_manifest_payload_sha256"]
        != source_record["payload_sha256"]
        or record["source_manifest_sha256"] != _file_sha256(source_path)
        or _payload_digest(payload) != record["payload_sha256"]
        or record["snapshot_path"]
        != f"checkpoints/{record['payload_sha256']}.json"
        or not snapshot.is_file()
        or snapshot.read_bytes() != raw
        or not isinstance(record["pivots"], list)
        or len(record["pivots"]) != expected_pivots
        or any(
            not _valid_pivot(pivot, index, "positive")
            for index, pivot in enumerate(record["pivots"])
        )
    ):
        raise ValueError("resume checkpoint is incompatible or invalid")
    return completed, list(record["pivots"])


def run_streaming_interval_ldlt(
    source_manifest: str | Path,
    checkpoint_path: str | Path,
    *,
    workspace_dir: str | Path,
    block_size: int,
    arb_prec_bits: int,
    serialization_digits: int,
    intersection_level: str = "high",
    resume: bool = False,
    max_panels: int | None = None,
) -> dict[str, Any]:
    source_path = Path(source_manifest)
    output_path = Path(checkpoint_path)
    workspace = Path(workspace_dir)
    if not _plain_int(block_size, 1):
        raise ValueError("block_size must be a positive integer")
    if not _plain_int(arb_prec_bits, 128):
        raise ValueError("arb_prec_bits must be an integer at least 128")
    if not _plain_int(serialization_digits, 30):
        raise ValueError("serialization_digits must be an integer at least 30")
    if intersection_level not in {"low", "high"}:
        raise ValueError("intersection_level must be low or high")
    if type(resume) is not bool:
        raise ValueError("resume must be a boolean")
    if max_panels is not None and (
        type(max_panels) is not int or max_panels < 1
    ):
        raise ValueError("max_panels must be a positive integer")
    source_record, descriptors = _load_source(source_path)
    parameters = source_record["parameters"]
    if block_size != parameters["tile_size"]:
        raise ValueError("block_size must equal the source tile_size")
    source_precision = parameters[f"{intersection_level}_prec_bits"]
    if arb_prec_bits < source_precision:
        raise ValueError(
            "arb_prec_bits must be at least the selected source precision"
        )
    if not resume and workspace.exists() and any(workspace.iterdir()):
        raise ValueError("workspace_dir must be absent or empty")

    try:
        import flint
        from flint import arb, arb_mat, ctx
    except ImportError as error:
        raise RuntimeError("factorization requires python-flint") from error

    previous_precision = ctx.prec
    ctx.prec = arb_prec_bits
    blocks = _block_bounds(parameters["dimension"], block_size)
    resume_parameters = _resume_parameters(
        block_size=block_size,
        arb_prec_bits=arb_prec_bits,
        serialization_digits=serialization_digits,
        intersection_level=intersection_level,
    )
    if resume:
        completed_panels, pivots = _load_resume_checkpoint(
            workspace,
            source_path,
            source_record,
            resume_parameters,
            blocks,
        )
    else:
        completed_panels = 0
        pivots = []
    first_unresolved = None
    panels_this_run = 0
    store = BlockStore(
        source_path,
        source_record,
        descriptors,
        workspace,
        block_size,
        serialization_digits,
        intersection_level,
        arb,
        arb_mat,
        completed_panels,
    )
    try:
        for panel_index in range(completed_panels, len(blocks)):
            panel_start, _panel_end = blocks[panel_index]
            diagonal_schur = store.load_schur(panel_index, panel_index)
            lower, diagonal, stop_local, stop_reason = _factor_diagonal_block(
                diagonal_schur, arb, arb_mat
            )
            positive_count = len(diagonal) if stop_local is None else stop_local
            for local_index in range(positive_count):
                pivots.append(
                    _pivot_record(
                        panel_start + local_index,
                        diagonal[local_index],
                        serialization_digits,
                    )
                )
            if stop_local is not None:
                first_unresolved = _pivot_record(
                    panel_start + stop_local,
                    diagonal[stop_local],
                    serialization_digits,
                )
                first_unresolved["reason"] = stop_reason
                store.write_diagonal(
                    panel_index, lower, diagonal[: stop_local + 1]
                )
                break

            store.write_diagonal(panel_index, lower, diagonal)
            for block_row in range(panel_index + 1, len(blocks)):
                schur_panel = store.load_schur(block_row, panel_index)
                factor = _right_solve_panel(schur_panel, lower, diagonal)
                store.write_block("factors", block_row, panel_index, factor)

            for block_row in range(panel_index + 1, len(blocks)):
                left = store.load_factor(block_row, panel_index)
                left_scaled = _scaled_columns(left, diagonal, arb_mat)
                for block_col in range(panel_index + 1, block_row + 1):
                    right = store.load_factor(block_col, panel_index)
                    current = store.load_schur(block_row, block_col)
                    updated = current - left_scaled * right.transpose()
                    store.write_block(
                        "schur", block_row, block_col, updated
                    )
            completed_panels += 1
            panels_this_run += 1
            store.completed_panels = completed_panels
            _write_resume_checkpoint(
                workspace,
                source_path,
                source_record,
                resume_parameters,
                completed_panels,
                pivots,
            )
            if (
                max_panels is not None
                and panels_this_run >= max_panels
                and completed_panels < len(blocks)
            ):
                raise PanelLimitReached(
                    f"checkpointed {completed_panels}/{len(blocks)} panels"
                )
    finally:
        ctx.prec = previous_precision

    workspace_manifest = store.workspace_manifest(completed_panels)
    complete = first_unresolved is None and len(pivots) == parameters["dimension"]
    classification = "positive" if complete else "unresolved"
    payload = {
        "claim_scope": CLAIM_SCOPE,
        "classification": classification,
        "gate_a_status": GATE_A_STATUS,
        "generator_sha256": _source_sha256(),
        "limitations": LIMITATIONS,
        "parameters": {
            "N": parameters["N"],
            "arb_prec_bits": arb_prec_bits,
            "block_size": block_size,
            "c": parameters["c"],
            "dimension": parameters["dimension"],
            "intersection_level": intersection_level,
            "python_flint_version": flint.__version__,
            "serialization_digits": serialization_digits,
            "source_high_prec_bits": parameters["high_prec_bits"],
            "source_low_prec_bits": parameters["low_prec_bits"],
        },
        "pivots": pivots,
        "result": {
            "certified_positive_pivot_count": len(pivots),
            "certified_strict_negative_witness": False,
            "complete_factorization": complete,
            "dimension": parameters["dimension"],
            "first_unresolved_pivot": first_unresolved,
        },
        "schema_version": CHECKPOINT_SCHEMA,
        "source": _checkpoint_source(output_path, source_path, source_record),
        "workspace": _workspace_summary(
            workspace,
            workspace_manifest,
            store.maximum_loaded_block_entries,
        ),
    }
    return _write_checkpoint(output_path, payload)


def _load_checkpoint(path: Path) -> dict[str, Any] | None:
    try:
        raw = path.read_bytes()
        record = json.loads(
            raw,
            parse_constant=lambda value: (_ for _ in ()).throw(
                ValueError(f"non-finite JSON constant: {value}")
            ),
        )
    except (OSError, TypeError, UnicodeError, ValueError):
        return None
    if not isinstance(record, dict) or raw != _canonical_bytes(record):
        return None
    return record


def _valid_pivot(value: Any, expected_index: int, expected_sign: str) -> bool:
    if not isinstance(value, dict) or set(value) != {
        "index",
        "lower",
        "sign",
        "upper",
    }:
        return False
    lower = _parse_fraction(value["lower"])
    upper = _parse_fraction(value["upper"])
    return (
        value["index"] == expected_index
        and value["sign"] == expected_sign
        and lower is not None
        and upper is not None
        and lower <= upper
        and (
            (expected_sign == "positive" and lower > 0)
            or (expected_sign == "negative" and upper < 0)
            or (expected_sign == "unresolved" and lower <= 0 <= upper)
        )
    )


def verify_checkpoint(record: Any, checkpoint_path: str | Path) -> bool:
    required = {
        "claim_scope",
        "classification",
        "gate_a_status",
        "generator_sha256",
        "limitations",
        "parameters",
        "payload_sha256",
        "pivots",
        "result",
        "schema_version",
        "source",
        "workspace",
    }
    if not isinstance(record, dict) or set(record) != required:
        return False
    if (
        record["schema_version"] != CHECKPOINT_SCHEMA
        or record["claim_scope"] != CLAIM_SCOPE
        or record["gate_a_status"] != GATE_A_STATUS
        or record["limitations"] != LIMITATIONS
        or record["generator_sha256"] != _source_sha256()
        or record["classification"] not in {"positive", "unresolved"}
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
        "arb_prec_bits",
        "block_size",
        "c",
        "dimension",
        "intersection_level",
        "python_flint_version",
        "serialization_digits",
        "source_high_prec_bits",
        "source_low_prec_bits",
    }
    if (
        not isinstance(parameters, dict)
        or set(parameters) != parameter_keys
        or any(
            not _plain_int(parameters[key], minimum)
            for key, minimum in (
                ("N", 0),
                ("arb_prec_bits", 128),
                ("block_size", 1),
                ("c", 2),
                ("dimension", 1),
                ("serialization_digits", 30),
                ("source_high_prec_bits", 128),
                ("source_low_prec_bits", 128),
            )
        )
        or parameters["intersection_level"] not in {"low", "high"}
        or not isinstance(parameters["python_flint_version"], str)
        or parameters["dimension"] != 2 * parameters["N"] + 1
        or parameters["arb_prec_bits"]
        < parameters[f"source_{parameters['intersection_level']}_prec_bits"]
    ):
        return False

    source = record["source"]
    if not isinstance(source, dict) or set(source) != {
        "manifest_payload_sha256",
        "manifest_sha256",
        "path",
    }:
        return False
    checkpoint = Path(checkpoint_path)
    source_path = _resolve_path(checkpoint.parent, source["path"])
    if (
        source_path is None
        or not source_path.is_file()
        or not _sha256_string(source["manifest_sha256"])
        or not _sha256_string(source["manifest_payload_sha256"])
        or _file_sha256(source_path) != source["manifest_sha256"]
    ):
        return False
    source_record = sharded._read_manifest(source_path)
    if (
        source_record is None
        or source_record.get("payload_sha256")
        != source["manifest_payload_sha256"]
        or not sharded.verify_cross_precision_artifact_file(source_path)
    ):
        return False
    source_parameters = source_record["parameters"]
    if (
        source_parameters["N"] != parameters["N"]
        or source_parameters["c"] != parameters["c"]
        or source_parameters["dimension"] != parameters["dimension"]
        or source_parameters["tile_size"] != parameters["block_size"]
        or source_parameters["high_prec_bits"] != parameters["source_high_prec_bits"]
        or source_parameters["low_prec_bits"] != parameters["source_low_prec_bits"]
    ):
        return False

    pivots = record["pivots"]
    result = record["result"]
    if (
        not isinstance(pivots, list)
        or any(not _valid_pivot(pivot, index, "positive") for index, pivot in enumerate(pivots))
        or not isinstance(result, dict)
        or set(result) != {
            "certified_positive_pivot_count",
            "certified_strict_negative_witness",
            "complete_factorization",
            "dimension",
            "first_unresolved_pivot",
        }
        or result["certified_positive_pivot_count"] != len(pivots)
        or result["certified_strict_negative_witness"] is not False
        or result["dimension"] != parameters["dimension"]
    ):
        return False

    unresolved = result["first_unresolved_pivot"]
    if record["classification"] == "positive":
        if (
            result["complete_factorization"] is not True
            or unresolved is not None
            or len(pivots) != parameters["dimension"]
        ):
            return False
    else:
        if (
            result["complete_factorization"] is not False
            or not isinstance(unresolved, dict)
            or set(unresolved) != {
                "index",
                "lower",
                "reason",
                "sign",
                "upper",
            }
            or unresolved["index"] != len(pivots)
            or unresolved["reason"] not in {
                "pivot_interval_contains_zero",
                "strict_negative_pivot_without_rational_witness",
            }
        ):
            return False
        expected_sign = (
            "negative"
            if unresolved["reason"]
            == "strict_negative_pivot_without_rational_witness"
            else "unresolved"
        )
        pivot_only = {
            key: unresolved[key] for key in ("index", "lower", "sign", "upper")
        }
        if not _valid_pivot(pivot_only, len(pivots), expected_sign):
            return False

    workspace = record["workspace"]
    return (
        isinstance(workspace, dict)
        and set(workspace)
        == {
            "block_file_count",
            "manifest_payload_sha256",
            "manifest_sha256",
            "maximum_loaded_block_entries",
            "total_compressed_bytes",
        }
        and all(
            _plain_int(workspace[key], 0)
            for key in (
                "block_file_count",
                "maximum_loaded_block_entries",
                "total_compressed_bytes",
            )
        )
        and isinstance(workspace["manifest_payload_sha256"], str)
        and _sha256_string(workspace["manifest_payload_sha256"])
        and _sha256_string(workspace["manifest_sha256"])
        and workspace["maximum_loaded_block_entries"]
        <= parameters["block_size"] * parameters["block_size"]
    )


def verify_checkpoint_file(path: str | Path) -> bool:
    checkpoint = Path(path)
    record = _load_checkpoint(checkpoint)
    return record is not None and verify_checkpoint(record, checkpoint)


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Run or verify streaming interval LDL checkpoints."
    )
    subparsers = parser.add_subparsers(dest="command", required=True)
    run = subparsers.add_parser("run")
    run.add_argument("source_manifest", type=Path)
    run.add_argument("checkpoint", type=Path)
    run.add_argument("--workspace-dir", type=Path, required=True)
    run.add_argument("--block-size", type=int, required=True)
    run.add_argument("--arb-prec-bits", type=int, required=True)
    run.add_argument("--serialization-digits", type=int, required=True)
    run.add_argument(
        "--intersection-level", choices=("low", "high"), default="high"
    )
    run.add_argument("--resume", action="store_true")
    run.add_argument("--max-panels", type=int)
    verify = subparsers.add_parser("verify-checkpoint")
    verify.add_argument("checkpoint", type=Path)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _build_parser().parse_args(argv)
    if args.command == "run":
        record = run_streaming_interval_ldlt(
            args.source_manifest,
            args.checkpoint,
            workspace_dir=args.workspace_dir,
            block_size=args.block_size,
            arb_prec_bits=args.arb_prec_bits,
            serialization_digits=args.serialization_digits,
            intersection_level=args.intersection_level,
            resume=args.resume,
            max_panels=args.max_panels,
        )
        print(f"streaming interval LDL classification: {record['classification']}")
        return 0
    valid = verify_checkpoint_file(args.checkpoint)
    print(f"valid streaming interval LDL checkpoint: {str(valid).lower()}")
    return 0 if valid else 1


if __name__ == "__main__":
    raise SystemExit(main())
