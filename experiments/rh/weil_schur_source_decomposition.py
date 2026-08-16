"""Rigorous source decomposition and finite-shell Schur feasibility diagnostic.

The CCM formula has the exact structural decomposition

    Q = L(alpha) + L(prime_value) + 2 c c^T - 2 s s^T.

This program preserves Arb interval enclosures for all four matrices, checks
source additivity and symmetry, and computes conservative rational Schur data
for a finite split

    [-N, N] = [-core_N, core_N] union finite_shell.

The diagnostic is deliberately not an infinite-dimensional theorem.  A finite
shell can reveal scaling and falsify proposed estimates, but the emitted
``infinite_bridge.status`` remains ``UNPROVED`` until separate analytic bounds
cover every Fourier index outside the finite shell.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, Iterable, List, Mapping, Sequence, Tuple

from weil_extremal_interval_ccm import (
    INDEX_CONVENTION,
    SOURCE_ARCHIMEDEAN,
    SOURCE_LABELS,
    SOURCE_POLE,
    SOURCE_PRIME,
    SOURCE_TOTAL,
    _flint,
    _interval_strings,
    _require_parameters,
    assemble_ccm_source_intervals,
)


SCHEMA_VERSION = "weil-schur-source-decomposition/v1"
GENERATOR = "experiments/rh/weil_schur_source_decomposition.py"
FORMULA = "Q=L(alpha)+L(prime_value)+2*c*c^T-2*s*s^T"

RationalInterval = Tuple[Fraction, Fraction]
SerializedMatrix = List[List[str]]


def _canonical_json(value: Mapping[str, Any]) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def _payload_digest(payload: Mapping[str, Any]) -> str:
    return hashlib.sha256(_canonical_json(payload).encode("utf-8")).hexdigest()


def _fraction_text(value: Fraction) -> str:
    return str(value)


def _parse_interval(entry: Sequence[str]) -> RationalInterval:
    return Fraction(entry[0]), Fraction(entry[1])


def _abs_upper(interval: RationalInterval) -> Fraction:
    lo, hi = interval
    return max(abs(lo), abs(hi))


def _overlap(left: RationalInterval, right: RationalInterval) -> bool:
    return max(left[0], right[0]) <= min(left[1], right[1])


def _entry(
    matrix: Sequence[Sequence[str]], N: int, row: int, column: int
) -> RationalInterval:
    dimension = 2 * N + 1
    offset = (row + N) * dimension + column + N
    return _parse_interval(matrix[offset])


def _serialize_sources(
    c: int, N: int, prec_bits: int
) -> Dict[str, SerializedMatrix]:
    sources = assemble_ccm_source_intervals(c, N, prec_bits)
    flint = _flint()
    previous_prec = flint.ctx.prec
    flint.ctx.prec = prec_bits
    try:
        return {
            label: [
                list(_interval_strings(sources[label][(row, column)]))
                for row in range(-N, N + 1)
                for column in range(-N, N + 1)
            ]
            for label in SOURCE_LABELS
        }
    finally:
        flint.ctx.prec = previous_prec


def _matrix_digest(matrix: SerializedMatrix) -> str:
    return hashlib.sha256(
        json.dumps(matrix, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    ).hexdigest()


def _gershgorin_lower(
    matrix: SerializedMatrix, N: int, indices: Sequence[int]
) -> Fraction:
    lower_bounds = []
    for row in indices:
        diagonal_lo, _ = _entry(matrix, N, row, row)
        radius = sum(
            (
                _abs_upper(_entry(matrix, N, row, column))
                for column in indices
                if column != row
            ),
            Fraction(0),
        )
        lower_bounds.append(diagonal_lo - radius)
    if not lower_bounds:
        raise ValueError("Gershgorin bound requires a nonempty index set")
    return min(lower_bounds)


def _operator_norm_squared_upper(
    matrix: SerializedMatrix,
    N: int,
    row_indices: Sequence[int],
    column_indices: Sequence[int],
) -> Fraction:
    if not row_indices or not column_indices:
        return Fraction(0)
    infinity_norm = max(
        sum(
            (
                _abs_upper(_entry(matrix, N, row, column))
                for column in column_indices
            ),
            Fraction(0),
        )
        for row in row_indices
    )
    one_norm = max(
        sum(
            (
                _abs_upper(_entry(matrix, N, row, column))
                for row in row_indices
            ),
            Fraction(0),
        )
        for column in column_indices
    )
    return infinity_norm * one_norm


def _symmetry_holds(matrix: SerializedMatrix, N: int) -> bool:
    return all(
        _overlap(
            _entry(matrix, N, row, column),
            _entry(matrix, N, column, row),
        )
        for row in range(-N, N + 1)
        for column in range(-N, N + 1)
    )


def _decomposition_holds(sources: Mapping[str, SerializedMatrix]) -> bool:
    total = sources[SOURCE_TOTAL]
    components = (
        sources[SOURCE_ARCHIMEDEAN],
        sources[SOURCE_PRIME],
        sources[SOURCE_POLE],
    )
    for offset, total_entry in enumerate(total):
        component_intervals = [_parse_interval(matrix[offset]) for matrix in components]
        component_sum = (
            sum((interval[0] for interval in component_intervals), Fraction(0)),
            sum((interval[1] for interval in component_intervals), Fraction(0)),
        )
        if not _overlap(_parse_interval(total_entry), component_sum):
            return False
    return True


def build_diagnostic(
    c: int, N: int, core_N: int, prec_bits: int
) -> Dict[str, Any]:
    _require_parameters(c, N, prec_bits)
    if isinstance(core_N, bool) or not isinstance(core_N, int):
        raise ValueError("core_N must be an integer")
    if core_N < 0 or core_N >= N:
        raise ValueError("core_N must satisfy 0 <= core_N < N")

    sources = _serialize_sources(c, N, prec_bits)
    core = tuple(range(-core_N, core_N + 1))
    shell = tuple(index for index in range(-N, N + 1) if abs(index) > core_N)
    total = sources[SOURCE_TOTAL]

    epsilon = _gershgorin_lower(total, N, core)
    gamma = _gershgorin_lower(total, N, shell)
    beta_squared = _operator_norm_squared_upper(total, N, core, shell)
    schur_closes = (
        epsilon > 0
        and gamma > 0
        and epsilon * gamma > beta_squared
    )

    source_bounds = {
        label: {
            "core_gershgorin_lower": _fraction_text(
                _gershgorin_lower(sources[label], N, core)
            ),
            "shell_gershgorin_lower": _fraction_text(
                _gershgorin_lower(sources[label], N, shell)
            ),
            "sha256": _matrix_digest(sources[label]),
            "symmetric_interval_overlap": _symmetry_holds(sources[label], N),
        }
        for label in SOURCE_LABELS
    }

    payload = {
        "N": N,
        "c": c,
        "candidate_normalization": {
            "perturbation": "L(prime_value)+2*c*c^T-2*s*s^T",
            "reference": "L(alpha)",
            "status": "CANDIDATE_ONLY",
        },
        "core_N": core_N,
        "decomposition": {
            "formula": FORMULA,
            "interval_additivity_overlap": _decomposition_holds(sources),
            "pole_rank_upper_bound": 2,
            "source_bounds": source_bounds,
        },
        "finite_shell": {
            "beta_squared_upper": _fraction_text(beta_squared),
            "core_epsilon_lower": _fraction_text(epsilon),
            "shell_gamma_lower": _fraction_text(gamma),
            "status": (
                "FINITE_SCHUR_STRICTLY_CLOSES"
                if schur_closes
                else "FINITE_SCHUR_BOUND_FAILS"
            ),
            "strict_schur_gap": _fraction_text(
                epsilon * gamma - beta_squared
            ),
        },
        "generator": GENERATOR,
        "index_convention": INDEX_CONVENTION,
        "infinite_bridge": {
            "missing": [
                "uniform coercive lower bound for L(alpha)",
                "infinite-shell bound for L(prime_value)",
                "infinite-shell coupling bound for the rank-two pole update",
                "proof that the normalized remainder tends to zero",
            ],
            "status": "UNPROVED",
        },
        "prec_bits": prec_bits,
        "schema_version": SCHEMA_VERSION,
    }
    return {**payload, "payload_sha256": _payload_digest(payload)}


def verify_diagnostic(record: Any) -> bool:
    if not isinstance(record, dict) or "payload_sha256" not in record:
        return False
    payload = {key: value for key, value in record.items() if key != "payload_sha256"}
    if payload.get("schema_version") != SCHEMA_VERSION:
        return False
    if payload.get("generator") != GENERATOR:
        return False
    if payload.get("index_convention") != INDEX_CONVENTION:
        return False
    decomposition = payload.get("decomposition")
    infinite_bridge = payload.get("infinite_bridge")
    if not isinstance(decomposition, dict) or decomposition.get("formula") != FORMULA:
        return False
    if (
        not isinstance(infinite_bridge, dict)
        or infinite_bridge.get("status") != "UNPROVED"
    ):
        return False
    return _payload_digest(payload) == record["payload_sha256"]


def write_diagnostic(
    path: str | Path, c: int, N: int, core_N: int, prec_bits: int
) -> Dict[str, Any]:
    record = build_diagnostic(c, N, core_N, prec_bits)
    output = Path(path)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_bytes((_canonical_json(record) + "\n").encode("utf-8"))
    return record


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Build a rigorous finite-shell Schur decomposition diagnostic."
    )
    parser.add_argument("--c", type=int, required=True)
    parser.add_argument("--N", type=int, required=True)
    parser.add_argument("--core-N", type=int, required=True)
    parser.add_argument("--prec-bits", type=int, default=256)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args(argv)
    record = write_diagnostic(
        args.out, args.c, args.N, args.core_N, args.prec_bits
    )
    finite = record["finite_shell"]
    print(
        f"source decomposition c={args.c} N={args.N} core_N={args.core_N}: "
        f"{finite['status']}; gap={finite['strict_schur_gap']}; "
        "infinite bridge UNPROVED"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
