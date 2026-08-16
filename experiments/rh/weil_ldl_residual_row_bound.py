"""Rigorous blockwise residual row bound for the c=13, N=200 LDL center.

Given the authenticated high-precision source intersection and streaming LDL
workspace, this tool chooses exact rational midpoints ``L0`` and ``D0``,
reconstructs

    C = L0 * D0 * L0^T

in rigorous Arb arithmetic, and computes

    rho = max_i sum_j sup_{a in A_ij} |a - C_ij|.

The preregistered threshold is ``10^-80``, strictly below the separately
computed sharp coercivity margin ``1.66e-79``.  This artifact proves only the
residual side of that comparison; the final combined certificate must bind
both artifacts.
"""

from __future__ import annotations

import argparse
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, Mapping, Sequence

from weil_extremal_interval_overlap import arb_fraction_bounds
from weil_ldl_coercivity_preflight import (
    _canonical_bytes,
    _file_sha256,
    _fraction,
    _load_canonical,
    _load_compressed,
    _payload_digest,
    _scientific,
)


SCHEMA_VERSION = "weil-ldl-residual-row-bound/v1"
GENERATOR = "experiments/rh/weil_ldl_residual_row_bound.py"
PREREGISTERED_THRESHOLD = Fraction(1, 10**80)

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)


def _center(lower: Any, upper: Any) -> Fraction:
    lo = _fraction(lower)
    hi = _fraction(upper)
    if lo > hi:
        raise ValueError("interval has lower endpoint above upper endpoint")
    return (lo + hi) / 2


def _fraction_ball(lower: Any, upper: Any, arb: Any, fmpq: Any) -> Any:
    lo = _fraction(lower)
    hi = _fraction(upper)
    if lo > hi:
        raise ValueError("source interval has lower endpoint above upper endpoint")
    midpoint = (lo + hi) / 2
    radius = (hi - lo) / 2
    return arb(
        fmpq(midpoint.numerator, midpoint.denominator),
        fmpq(radius.numerator, radius.denominator),
    )


def build_residual_row_bound(
    source_manifest: str | Path,
    workspace_manifest: str | Path,
    ldl_checkpoint: str | Path,
    *,
    arb_prec_bits: int,
    serialization_digits: int,
) -> Dict[str, Any]:
    try:
        import flint
        from flint import arb, arb_mat, ctx, fmpq
    except ImportError as error:
        raise RuntimeError("residual computation requires python-flint") from error

    source_path = Path(source_manifest)
    workspace_manifest_path = Path(workspace_manifest)
    workspace = workspace_manifest_path.parent
    checkpoint_path = Path(ldl_checkpoint)
    source = _load_canonical(source_path)
    workspace_record = _load_canonical(workspace_manifest_path)
    checkpoint = _load_canonical(checkpoint_path)

    parameters = checkpoint.get("parameters")
    checkpoint_source = checkpoint.get("source")
    checkpoint_workspace = checkpoint.get("workspace")
    result = checkpoint.get("result")
    source_parameters = source.get("parameters")
    if (
        checkpoint.get("classification") != "positive"
        or not isinstance(parameters, dict)
        or not isinstance(checkpoint_source, dict)
        or not isinstance(checkpoint_workspace, dict)
        or not isinstance(result, dict)
        or not isinstance(source_parameters, dict)
        or result.get("complete_factorization") is not True
        or result.get("certified_positive_pivot_count")
        != parameters.get("dimension")
        or checkpoint_source.get("manifest_sha256") != _file_sha256(source_path)
        or checkpoint_source.get("manifest_payload_sha256")
        != source.get("payload_sha256")
        or checkpoint_workspace.get("manifest_sha256")
        != _file_sha256(workspace_manifest_path)
        or checkpoint_workspace.get("manifest_payload_sha256")
        != workspace_record.get("payload_sha256")
        or source_parameters.get("c") != parameters.get("c")
        or source_parameters.get("N") != parameters.get("N")
        or source_parameters.get("dimension") != parameters.get("dimension")
    ):
        raise ValueError("source, workspace, and checkpoint bindings disagree")
    if arb_prec_bits < parameters["arb_prec_bits"]:
        raise ValueError("residual precision must not be below LDL precision")

    dimension = parameters["dimension"]
    block_size = parameters["block_size"]
    workspace_descriptors = workspace_record.get("blocks")
    source_descriptors = source.get("chunks")
    if not isinstance(workspace_descriptors, list) or not isinstance(
        source_descriptors, list
    ):
        raise ValueError("manifest block descriptors are missing")

    previous_precision = ctx.prec
    ctx.prec = arb_prec_bits
    try:
        lower_blocks: Dict[tuple[int, int], Any] = {}
        diagonal_blocks: Dict[int, list[Any]] = {}

        for descriptor in workspace_descriptors:
            relative = descriptor.get("path") if isinstance(descriptor, dict) else None
            if not isinstance(relative, str) or not relative.startswith("factors/"):
                continue
            path = workspace / relative
            if _file_sha256(path) != descriptor.get("sha256"):
                raise ValueError(f"workspace block hash mismatch: {relative}")
            record = _load_compressed(path)

            if relative.startswith("factors/diagonal-"):
                block_index = record.get("block")
                values = record.get("diagonal")
                if (
                    record.get("kind") != "diagonal"
                    or not isinstance(block_index, int)
                    or not isinstance(values, list)
                ):
                    raise ValueError(f"invalid diagonal block: {relative}")
                diagonal_blocks[block_index] = [
                    arb(
                        fmpq(center.numerator, center.denominator)
                    )
                    for center in (
                        _center(interval["lower"], interval["upper"])
                        for interval in values
                    )
                ]
                continue

            if not relative.startswith("factors/block-"):
                continue
            block = record.get("block")
            enclosure = record.get("enclosure")
            if (
                record.get("kind") != "factors"
                or not isinstance(block, dict)
                or not isinstance(enclosure, dict)
            ):
                raise ValueError(f"invalid factor block: {relative}")
            lower_rows = enclosure["lower"]
            upper_rows = enclosure["upper"]
            matrix = arb_mat(len(lower_rows), len(lower_rows[0]))
            for row, (lower_row, upper_row) in enumerate(
                zip(lower_rows, upper_rows)
            ):
                for column, (lo, hi) in enumerate(zip(lower_row, upper_row)):
                    center = _center(lo, hi)
                    matrix[row, column] = arb(
                        fmpq(center.numerator, center.denominator)
                    )
            lower_blocks[(block["row"], block["column"])] = matrix

        block_count = (dimension + block_size - 1) // block_size
        expected_factor_blocks = block_count * (block_count + 1) // 2
        if len(lower_blocks) != expected_factor_blocks:
            raise ValueError("factor blocks do not cover the block lower triangle")
        if len(diagonal_blocks) != block_count:
            raise ValueError("diagonal blocks do not cover all panels")

        row_sums = [arb(0) for _ in range(dimension)]
        processed_entries = 0
        processed_tiles = 0

        for descriptor in source_descriptors:
            if not isinstance(descriptor, dict):
                raise ValueError("invalid source descriptor")
            relative = descriptor.get("path")
            tile = descriptor.get("tile")
            if not isinstance(relative, str) or not isinstance(tile, dict):
                raise ValueError("invalid source tile descriptor")
            path = source_path.parent / relative
            if _file_sha256(path) != descriptor.get("compressed_sha256"):
                raise ValueError(f"source tile hash mismatch: {relative}")
            record = _load_compressed(path)
            intersection = record.get("intersection", {}).get("high")
            if not isinstance(intersection, dict):
                raise ValueError(f"source tile has no high intersection: {relative}")

            row_start = tile["row_start"]
            row_end = tile["row_end"]
            column_start = tile["col_start"]
            column_end = tile["col_end"]
            block_row = row_start // block_size
            block_column = column_start // block_size
            rows = row_end - row_start
            columns = column_end - column_start
            center_block = arb_mat(rows, columns)

            for panel in range(min(block_row, block_column) + 1):
                left = lower_blocks[(block_row, panel)]
                right = lower_blocks[(block_column, panel)]
                diagonal = diagonal_blocks[panel]
                left_scaled = arb_mat(left.nrows(), left.ncols())
                for row in range(left.nrows()):
                    for column in range(left.ncols()):
                        left_scaled[row, column] = (
                            left[row, column] * diagonal[column]
                        )
                center_block = center_block + left_scaled * right.transpose()

            lower_rows = intersection.get("lower")
            upper_rows = intersection.get("upper")
            if (
                not isinstance(lower_rows, list)
                or not isinstance(upper_rows, list)
                or len(lower_rows) != rows
                or len(upper_rows) != rows
            ):
                raise ValueError(f"source tile shape mismatch: {relative}")
            for local_row, (lower_row, upper_row) in enumerate(
                zip(lower_rows, upper_rows)
            ):
                global_row = row_start + local_row
                if len(lower_row) != columns or len(upper_row) != columns:
                    raise ValueError(f"source row shape mismatch: {relative}")
                for local_column, (lo, hi) in enumerate(
                    zip(lower_row, upper_row)
                ):
                    source_ball = _fraction_ball(lo, hi, arb, fmpq)
                    row_sums[global_row] += abs(
                        source_ball - center_block[local_row, local_column]
                    )
                    processed_entries += 1
            processed_tiles += 1

        if processed_entries != dimension * dimension:
            raise ValueError("source tiles do not cover every matrix entry")

        row_upper_bounds = []
        for total in row_sums:
            _lower, upper = arb_fraction_bounds(total, serialization_digits)
            row_upper_bounds.append(upper)
    finally:
        ctx.prec = previous_precision

    rho = max(row_upper_bounds)
    maximizing_row = row_upper_bounds.index(rho)
    closes_preregistered_threshold = rho < PREREGISTERED_THRESHOLD
    payload = {
        "bounds": {
            "maximizing_row": maximizing_row,
            "preregistered_threshold": str(PREREGISTERED_THRESHOLD),
            "rho_upper": str(rho),
            "rho_upper_scientific": _scientific(rho),
            "row_upper_bounds": [str(value) for value in row_upper_bounds],
            "strictly_below_preregistered_threshold": (
                closes_preregistered_threshold
            ),
        },
        "checkpoint": {
            "file_sha256": _file_sha256(checkpoint_path),
            "payload_sha256": checkpoint["payload_sha256"],
        },
        "claim_scope": "rigorous-source-to-rational-ldl-center-residual-only",
        "counts": {
            "entry_count": processed_entries,
            "source_tile_count": processed_tiles,
        },
        "generator": GENERATOR,
        "limitations": [
            "The final certificate must also bind the sharp inverse artifact.",
            "Lean has not replayed the Arb block reconstruction.",
            "No infinite-dimensional Weil criterion or RH conclusion is included.",
        ],
        "parameters": {
            "N": parameters["N"],
            "arb_prec_bits": arb_prec_bits,
            "c": parameters["c"],
            "dimension": dimension,
            "python_flint_version": flint.__version__,
            "serialization_digits": serialization_digits,
        },
        "schema_version": SCHEMA_VERSION,
        "source": {
            "manifest_payload_sha256": source["payload_sha256"],
            "manifest_sha256": _file_sha256(source_path),
        },
        "status": (
            "RESIDUAL_BELOW_PREREGISTERED_THRESHOLD"
            if closes_preregistered_threshold
            else "RESIDUAL_BOUND_TOO_LARGE"
        ),
        "workspace": {
            "manifest_payload_sha256": workspace_record["payload_sha256"],
            "manifest_sha256": _file_sha256(workspace_manifest_path),
        },
    }
    return {**payload, "payload_sha256": _payload_digest(payload)}


def write_residual_row_bound(
    output_path: str | Path,
    source_manifest: str | Path,
    workspace_manifest: str | Path,
    ldl_checkpoint: str | Path,
    *,
    arb_prec_bits: int,
    serialization_digits: int,
) -> Dict[str, Any]:
    record = build_residual_row_bound(
        source_manifest,
        workspace_manifest,
        ldl_checkpoint,
        arb_prec_bits=arb_prec_bits,
        serialization_digits=serialization_digits,
    )
    output = Path(output_path)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_bytes(_canonical_bytes(record))
    return record


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Compute the rigorous source-to-LDL-center residual row bound."
    )
    parser.add_argument("--source-manifest", type=Path, required=True)
    parser.add_argument("--workspace-manifest", type=Path, required=True)
    parser.add_argument("--ldl-checkpoint", type=Path, required=True)
    parser.add_argument("--arb-prec-bits", type=int, required=True)
    parser.add_argument("--serialization-digits", type=int, default=2800)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args(argv)
    record = write_residual_row_bound(
        args.out,
        args.source_manifest,
        args.workspace_manifest,
        args.ldl_checkpoint,
        arb_prec_bits=args.arb_prec_bits,
        serialization_digits=args.serialization_digits,
    )
    print(
        "LDL residual row bound: "
        f"rho<={record['bounds']['rho_upper_scientific']} "
        f"threshold=1e-80 status={record['status']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
