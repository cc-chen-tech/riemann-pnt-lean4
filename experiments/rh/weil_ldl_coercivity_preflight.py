"""Exact coercivity preflight for a streaming interval-LDL workspace.

This tool extracts two of the three rational quantities required by
``IntervalLDLCoercivity.lean``:

* ``delta``: a positive lower bound for the chosen rational diagonal center;
* ``kappa``: a conservative inverse-coordinate bound for the chosen rational
  lower-triangular center.

For the unit lower-triangular center ``L = I + E``, strict lower triangularity
gives ``E^n = 0``.  If ``s`` bounds the maximum absolute column sum of ``E``,
then

    ||(L^T)^-1||_infinity <= sum_{r=0}^{n-1} s^r.

The emitted bound uses the compact integer majorant

    K = n * max(1, ceil(s))^(n-1),
    kappa = n * K^2.

It is intentionally conservative.  The tool does not compute the source
residual row bound ``rho`` and therefore never emits a positivity claim.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
from decimal import Decimal, localcontext
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, Mapping, Sequence


SCHEMA_VERSION = "weil-ldl-coercivity-preflight/v1"
GENERATOR = "experiments/rh/weil_ldl_coercivity_preflight.py"
STATUS = "AWAITING_RESIDUAL_ROW_BOUND"


def _canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def _canonical_bytes(value: Any) -> bytes:
    return (_canonical_json(value) + "\n").encode("ascii")


def _payload_digest(payload: Mapping[str, Any]) -> str:
    return hashlib.sha256(_canonical_json(payload).encode("ascii")).hexdigest()


def _file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _load_canonical(path: Path) -> Dict[str, Any]:
    raw = path.read_bytes()
    record = json.loads(raw)
    if not isinstance(record, dict) or raw != _canonical_bytes(record):
        raise ValueError(f"noncanonical JSON: {path}")
    payload = {key: value for key, value in record.items() if key != "payload_sha256"}
    if record.get("payload_sha256") != _payload_digest(payload):
        raise ValueError(f"payload hash mismatch: {path}")
    return record


def _load_compressed(path: Path) -> Dict[str, Any]:
    with gzip.open(path, "rb") as source:
        raw = source.read()
    record = json.loads(raw)
    if not isinstance(record, dict) or raw != _canonical_bytes(record):
        raise ValueError(f"noncanonical compressed JSON: {path}")
    payload = {key: value for key, value in record.items() if key != "payload_sha256"}
    if record.get("payload_sha256") != _payload_digest(payload):
        raise ValueError(f"compressed payload hash mismatch: {path}")
    return record


def _fraction(value: Any) -> Fraction:
    if not isinstance(value, str):
        raise ValueError("rational endpoint must be a string")
    return Fraction(value)


def _center(lower: Any, upper: Any) -> Fraction:
    lo = _fraction(lower)
    hi = _fraction(upper)
    if lo > hi:
        raise ValueError("interval has lower endpoint above upper endpoint")
    return (lo + hi) / 2


def _ceil(value: Fraction) -> int:
    return -((-value.numerator) // value.denominator)


def _scientific(value: Fraction, digits: int = 18) -> str:
    with localcontext() as context:
        context.prec = digits
        decimal = Decimal(value.numerator) / Decimal(value.denominator)
        return f"{decimal:.{digits - 1}e}"


def build_preflight(
    workspace_manifest: str | Path,
    ldl_checkpoint: str | Path,
) -> Dict[str, Any]:
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
    descriptors = manifest.get("blocks")
    if (
        not isinstance(dimension, int)
        or dimension < 1
        or not isinstance(block_size, int)
        or block_size < 1
        or not isinstance(descriptors, list)
    ):
        raise ValueError("invalid workspace dimensions")

    column_sums = [Fraction(0) for _ in range(dimension)]
    diagonal_lowers = []
    factor_block_count = 0
    diagonal_block_count = 0
    strict_lower_entry_count = 0

    for descriptor in descriptors:
        if not isinstance(descriptor, dict):
            raise ValueError("invalid workspace descriptor")
        relative = descriptor.get("path")
        if not isinstance(relative, str) or not relative.startswith("factors/"):
            continue
        path = workspace / relative
        if _file_sha256(path) != descriptor.get("sha256"):
            raise ValueError(f"workspace block hash mismatch: {relative}")
        record = _load_compressed(path)

        if relative.startswith("factors/diagonal-"):
            diagonal_block_count += 1
            values = record.get("diagonal")
            if record.get("kind") != "diagonal" or not isinstance(values, list):
                raise ValueError(f"invalid diagonal block: {relative}")
            for interval in values:
                lower = _fraction(interval["lower"])
                upper = _fraction(interval["upper"])
                if lower <= 0 or lower > upper:
                    raise ValueError(f"nonpositive diagonal interval: {relative}")
                diagonal_lowers.append(lower)
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
        block_row = block.get("row")
        block_column = block.get("column")
        lower_rows = enclosure.get("lower")
        upper_rows = enclosure.get("upper")
        if (
            not isinstance(block_row, int)
            or not isinstance(block_column, int)
            or block_row < block_column
            or not isinstance(lower_rows, list)
            or not isinstance(upper_rows, list)
            or len(lower_rows) != len(upper_rows)
        ):
            raise ValueError(f"invalid factor block shape: {relative}")

        for local_row, (lower_row, upper_row) in enumerate(
            zip(lower_rows, upper_rows)
        ):
            if (
                not isinstance(lower_row, list)
                or not isinstance(upper_row, list)
                or len(lower_row) != len(upper_row)
            ):
                raise ValueError(f"invalid factor row: {relative}")
            global_row = block_row * block_size + local_row
            for local_column, (lower, upper) in enumerate(
                zip(lower_row, upper_row)
            ):
                global_column = block_column * block_size + local_column
                if global_row >= dimension or global_column >= dimension:
                    raise ValueError(f"factor entry outside matrix: {relative}")
                value = _center(lower, upper)
                if global_row < global_column:
                    if value != 0:
                        raise ValueError("factor center is not lower triangular")
                elif global_row == global_column:
                    if value != 1:
                        raise ValueError("factor center does not have unit diagonal")
                else:
                    column_sums[global_column] += abs(value)
                    strict_lower_entry_count += 1

    if len(diagonal_lowers) != dimension:
        raise ValueError("diagonal blocks do not cover the full dimension")
    if strict_lower_entry_count != dimension * (dimension - 1) // 2:
        raise ValueError("factor blocks do not cover the strict lower triangle")

    delta = min(diagonal_lowers)
    max_column_sum = max(column_sums, default=Fraction(0))
    column_sum_integer_upper = max(1, _ceil(max_column_sum))
    neumann_sum_upper = (
        dimension * column_sum_integer_upper ** (dimension - 1)
    )
    kappa = dimension * neumann_sum_upper**2
    coercivity_margin = delta / kappa

    payload = {
        "bounds": {
            "coercivity_margin_lower": str(coercivity_margin),
            "coercivity_margin_lower_scientific": _scientific(
                coercivity_margin
            ),
            "delta_lower": str(delta),
            "delta_lower_scientific": _scientific(delta),
            "kappa_upper": str(kappa),
            "max_strict_lower_column_sum": str(max_column_sum),
            "max_strict_lower_column_sum_integer_upper": (
                column_sum_integer_upper
            ),
            "neumann_sum_upper": str(neumann_sum_upper),
            "rho": None,
        },
        "checkpoint": {
            "file_sha256": _file_sha256(checkpoint_path),
            "payload_sha256": checkpoint["payload_sha256"],
        },
        "claim_scope": "coercivity-preflight-without-source-residual",
        "counts": {
            "diagonal_block_count": diagonal_block_count,
            "diagonal_entry_count": len(diagonal_lowers),
            "factor_block_count": factor_block_count,
            "strict_lower_entry_count": strict_lower_entry_count,
        },
        "generator": GENERATOR,
        "limitations": [
            "The source residual row bound rho has not been computed.",
            "The strict positivity condition rho < delta/kappa is not evaluated.",
            "No infinite-dimensional Weil criterion or RH conclusion is included.",
        ],
        "parameters": {
            "N": parameters["N"],
            "c": parameters["c"],
            "dimension": dimension,
        },
        "schema_version": SCHEMA_VERSION,
        "status": STATUS,
        "workspace": {
            "manifest_payload_sha256": manifest["payload_sha256"],
            "manifest_sha256": _file_sha256(manifest_path),
        },
    }
    return {**payload, "payload_sha256": _payload_digest(payload)}


def write_preflight(
    output_path: str | Path,
    workspace_manifest: str | Path,
    ldl_checkpoint: str | Path,
) -> Dict[str, Any]:
    record = build_preflight(workspace_manifest, ldl_checkpoint)
    output = Path(output_path)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_bytes(_canonical_bytes(record))
    return record


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Extract exact delta/kappa bounds from a streaming LDL workspace."
    )
    parser.add_argument("--workspace-manifest", type=Path, required=True)
    parser.add_argument("--ldl-checkpoint", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args(argv)
    record = write_preflight(
        args.out, args.workspace_manifest, args.ldl_checkpoint
    )
    bounds = record["bounds"]
    print(
        "LDL coercivity preflight: "
        f"delta>={bounds['delta_lower_scientific']} "
        f"kappa<={bounds['kappa_upper']} "
        f"delta/kappa>={bounds['coercivity_margin_lower_scientific']} "
        f"status={record['status']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
