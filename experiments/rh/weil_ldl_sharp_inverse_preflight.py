"""Rigorous Arb inverse-norm preflight for the c=13, N=200 LDL center.

The coarse nilpotent/Neumann estimate in
``weil_ldl_coercivity_preflight.py`` is mathematically valid but far too
large.  This tool constructs the exact rational midpoint matrix ``L0`` from
the authenticated factor blocks, encloses ``L0^-1`` with Arb, and uses

    ||L0^-T||_2^2 <= ||L0^-1||_1 * ||L0^-1||_infinity

to obtain a much sharper rigorous ``kappa``.

The source residual ``rho`` is still not computed here, so this remains a
feasibility artifact rather than a positivity certificate.
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


SCHEMA_VERSION = "weil-ldl-sharp-inverse-preflight/v1"
GENERATOR = "experiments/rh/weil_ldl_sharp_inverse_preflight.py"
STATUS = "AWAITING_RESIDUAL_ROW_BOUND"

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)


def _center(lower: Any, upper: Any) -> Fraction:
    lo = _fraction(lower)
    hi = _fraction(upper)
    if lo > hi:
        raise ValueError("factor interval has lower endpoint above upper endpoint")
    return (lo + hi) / 2


def _bound_positive_arb(value: Any, digits: int) -> Fraction:
    lower, upper = arb_fraction_bounds(value, digits)
    if lower < 0:
        raise ValueError("norm accumulation produced a negative lower endpoint")
    return upper


def build_sharp_inverse_preflight(
    workspace_manifest: str | Path,
    ldl_checkpoint: str | Path,
    *,
    arb_prec_bits: int,
    serialization_digits: int,
) -> Dict[str, Any]:
    if (
        isinstance(arb_prec_bits, bool)
        or not isinstance(arb_prec_bits, int)
        or arb_prec_bits < 128
    ):
        raise ValueError("arb_prec_bits must be an integer at least 128")
    if (
        isinstance(serialization_digits, bool)
        or not isinstance(serialization_digits, int)
        or serialization_digits < 30
    ):
        raise ValueError("serialization_digits must be an integer at least 30")

    try:
        import flint
        from flint import arb, arb_mat, ctx, fmpq
    except ImportError as error:
        raise RuntimeError("sharp inverse preflight requires python-flint") from error

    manifest_path = Path(workspace_manifest)
    workspace = manifest_path.parent
    checkpoint_path = Path(ldl_checkpoint)
    manifest = _load_canonical(manifest_path)
    checkpoint = _load_canonical(checkpoint_path)
    parameters = checkpoint.get("parameters")
    summary = checkpoint.get("workspace")
    result = checkpoint.get("result")
    if (
        checkpoint.get("classification") != "positive"
        or not isinstance(parameters, dict)
        or not isinstance(summary, dict)
        or not isinstance(result, dict)
        or result.get("complete_factorization") is not True
        or result.get("certified_positive_pivot_count")
        != parameters.get("dimension")
        or summary.get("manifest_sha256") != _file_sha256(manifest_path)
        or summary.get("manifest_payload_sha256") != manifest.get("payload_sha256")
    ):
        raise ValueError("checkpoint does not bind this complete positive workspace")

    dimension = parameters["dimension"]
    block_size = parameters["block_size"]
    if arb_prec_bits < parameters["arb_prec_bits"]:
        raise ValueError("inverse precision must not be below the LDL precision")
    descriptors = manifest.get("blocks")
    if not isinstance(descriptors, list):
        raise ValueError("workspace manifest has no block descriptors")

    previous_precision = ctx.prec
    ctx.prec = arb_prec_bits
    try:
        lower_matrix = arb_mat(dimension, dimension)
        diagonal_lowers = []
        factor_entry_count = 0
        factor_block_count = 0

        for descriptor in descriptors:
            relative = descriptor.get("path") if isinstance(descriptor, dict) else None
            if not isinstance(relative, str) or not relative.startswith("factors/"):
                continue
            path = workspace / relative
            if _file_sha256(path) != descriptor.get("sha256"):
                raise ValueError(f"workspace block hash mismatch: {relative}")
            record = _load_compressed(path)

            if relative.startswith("factors/diagonal-"):
                values = record.get("diagonal")
                if record.get("kind") != "diagonal" or not isinstance(values, list):
                    raise ValueError(f"invalid diagonal block: {relative}")
                for interval in values:
                    lo = _fraction(interval["lower"])
                    hi = _fraction(interval["upper"])
                    if lo <= 0 or lo > hi:
                        raise ValueError(f"invalid positive diagonal: {relative}")
                    diagonal_lowers.append(lo)
                continue

            if not relative.startswith("factors/block-"):
                continue
            factor_block_count += 1
            block = record.get("block")
            enclosure = record.get("enclosure")
            if (
                record.get("kind") != "factors"
                or not isinstance(block, dict)
                or not isinstance(enclosure, dict)
            ):
                raise ValueError(f"invalid factor block: {relative}")
            block_row = block["row"]
            block_column = block["column"]
            lower_rows = enclosure["lower"]
            upper_rows = enclosure["upper"]
            for local_row, (lower_row, upper_row) in enumerate(
                zip(lower_rows, upper_rows)
            ):
                global_row = block_row * block_size + local_row
                for local_column, (lo, hi) in enumerate(
                    zip(lower_row, upper_row)
                ):
                    global_column = block_column * block_size + local_column
                    if global_row >= dimension or global_column >= dimension:
                        raise ValueError(f"factor entry outside matrix: {relative}")
                    center = _center(lo, hi)
                    if global_row < global_column and center != 0:
                        raise ValueError("factor center is not lower triangular")
                    if global_row == global_column and center != 1:
                        raise ValueError("factor center does not have unit diagonal")
                    lower_matrix[global_row, global_column] = arb(
                        fmpq(center.numerator, center.denominator)
                    )
                    if global_row >= global_column:
                        factor_entry_count += 1

        if len(diagonal_lowers) != dimension:
            raise ValueError("diagonal blocks do not cover the full matrix")
        if factor_entry_count != dimension * (dimension + 1) // 2:
            raise ValueError("factor blocks do not cover the lower triangle")

        identity = arb_mat(dimension, dimension)
        for index in range(dimension):
            identity[index, index] = arb(1)
        inverse = lower_matrix.solve(identity)

        row_norm_upper = Fraction(0)
        for row in range(dimension):
            total = arb(0)
            for column in range(dimension):
                total += abs(inverse[row, column])
            row_norm_upper = max(
                row_norm_upper,
                _bound_positive_arb(total, serialization_digits),
            )

        column_norm_upper = Fraction(0)
        for column in range(dimension):
            total = arb(0)
            for row in range(dimension):
                total += abs(inverse[row, column])
            column_norm_upper = max(
                column_norm_upper,
                _bound_positive_arb(total, serialization_digits),
            )
    finally:
        ctx.prec = previous_precision

    delta = min(diagonal_lowers)
    kappa = row_norm_upper * column_norm_upper
    if kappa <= 0:
        raise ValueError("inverse norm bound is not strictly positive")
    margin = delta / kappa

    payload = {
        "bounds": {
            "coercivity_margin_lower": str(margin),
            "coercivity_margin_lower_scientific": _scientific(margin),
            "delta_lower": str(delta),
            "delta_lower_scientific": _scientific(delta),
            "inverse_column_sum_upper": str(column_norm_upper),
            "inverse_row_sum_upper": str(row_norm_upper),
            "kappa_upper": str(kappa),
            "kappa_upper_scientific": _scientific(kappa),
            "rho": None,
        },
        "checkpoint": {
            "file_sha256": _file_sha256(checkpoint_path),
            "payload_sha256": checkpoint["payload_sha256"],
        },
        "claim_scope": "rigorous-sharp-inverse-bound-without-source-residual",
        "counts": {
            "diagonal_entry_count": len(diagonal_lowers),
            "factor_block_count": factor_block_count,
            "factor_lower_triangle_entry_count": factor_entry_count,
        },
        "generator": GENERATOR,
        "limitations": [
            "The source residual row bound rho has not been computed.",
            "Arb encloses the exact rational center inverse; Lean has not replayed this solve.",
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
        "status": STATUS,
        "workspace": {
            "manifest_payload_sha256": manifest["payload_sha256"],
            "manifest_sha256": _file_sha256(manifest_path),
        },
    }
    return {**payload, "payload_sha256": _payload_digest(payload)}


def write_sharp_inverse_preflight(
    output_path: str | Path,
    workspace_manifest: str | Path,
    ldl_checkpoint: str | Path,
    *,
    arb_prec_bits: int,
    serialization_digits: int,
) -> Dict[str, Any]:
    record = build_sharp_inverse_preflight(
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
        description="Compute a rigorous sharp inverse norm for an LDL center."
    )
    parser.add_argument("--workspace-manifest", type=Path, required=True)
    parser.add_argument("--ldl-checkpoint", type=Path, required=True)
    parser.add_argument("--arb-prec-bits", type=int, required=True)
    parser.add_argument("--serialization-digits", type=int, default=2800)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args(argv)
    record = write_sharp_inverse_preflight(
        args.out,
        args.workspace_manifest,
        args.ldl_checkpoint,
        arb_prec_bits=args.arb_prec_bits,
        serialization_digits=args.serialization_digits,
    )
    bounds = record["bounds"]
    print(
        "sharp inverse preflight: "
        f"kappa<={bounds['kappa_upper_scientific']} "
        f"delta/kappa>={bounds['coercivity_margin_lower_scientific']} "
        f"status={record['status']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
