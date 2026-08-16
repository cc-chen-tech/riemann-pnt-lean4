"""Bind a certified full matrix to all of its centered principal sections.

For source order ``[-N, ..., N]``, the section ``[-M, ..., M]`` occupies
zero-based rows and columns

    N-M, ..., N+M.

This generator checks that identity for every ``0 <= M <= N``, binds the
result to the finite-closure artifact and source manifest, and emits matching
Lean metadata.  It does not claim positivity for cutoffs above ``N``.
"""

from __future__ import annotations

import argparse
from pathlib import Path
from typing import Any, Dict, Mapping, Sequence

from weil_ldl_coercivity_preflight import (
    _canonical_bytes,
    _file_sha256,
    _load_canonical,
    _payload_digest,
)


SCHEMA_VERSION = "weil-centered-principal-sections/v1"
GENERATOR = "experiments/rh/weil_centered_nesting_certificate.py"
STATUS = "CENTERED_PRINCIPAL_SECTIONS_CERTIFIED"


def build_centered_nesting_certificate(
    finite_closure_artifact: str | Path,
    source_manifest: str | Path,
) -> Dict[str, Any]:
    closure_path = Path(finite_closure_artifact)
    source_path = Path(source_manifest)
    closure = _load_canonical(closure_path)
    source = _load_canonical(source_path)
    if (
        closure.get("schema_version") != "weil-ldl-finite-closure/v1"
        or closure.get("status")
        != "FINITE_STRICT_POSITIVITY_BUDGET_CLOSES"
    ):
        raise ValueError("finite closure artifact is not successful")

    closure_parameters = closure.get("parameters")
    source_parameters = source.get("parameters")
    if not isinstance(closure_parameters, dict) or not isinstance(
        source_parameters, dict
    ):
        raise ValueError("artifact parameters are missing")
    common = {
        key: closure_parameters.get(key) for key in ("c", "N", "dimension")
    }
    if any(source_parameters.get(key) != value for key, value in common.items()):
        raise ValueError("source and closure parameters disagree")
    c = common["c"]
    N = common["N"]
    dimension = common["dimension"]
    if (
        isinstance(c, bool)
        or not isinstance(c, int)
        or isinstance(N, bool)
        or not isinstance(N, int)
        or isinstance(dimension, bool)
        or not isinstance(dimension, int)
        or dimension != 2 * N + 1
        or source_parameters.get("index_order") != list(range(-N, N + 1))
    ):
        raise ValueError("source does not use registered centered Fourier order")

    sections = []
    source_order = source_parameters["index_order"]
    for M in range(N + 1):
        row_start = N - M
        row_end = N + M + 1
        expected_order = list(range(-M, M + 1))
        if source_order[row_start:row_end] != expected_order:
            raise ValueError(f"centered source slice mismatch at M={M}")
        sections.append(
            {
                "M": M,
                "dimension": 2 * M + 1,
                "index_order": expected_order,
                "row_column_end_exclusive": row_end,
                "row_column_start": row_start,
            }
        )

    source_code_bindings = {
        key: source[key]
        for key in ("formula_source_sha256", "generator_sha256")
        if isinstance(source.get(key), str)
    }
    payload = {
        "claim_scope": f"centered-principal-sections-0-through-{N}",
        "finite_closure": {
            "file_sha256": _file_sha256(closure_path),
            "payload_sha256": closure["payload_sha256"],
        },
        "generator": GENERATOR,
        "limitations": [
            f"No cutoff M greater than {N} is certified.",
            "Formula-level equality with separately regenerated smaller artifacts is not replayed.",
            "No infinite-dimensional Weil criterion or RH conclusion is included.",
        ],
        "parameters": {
            "N": N,
            "c": c,
            "certified_section_count": N + 1,
            "dimension": dimension,
        },
        "schema_version": SCHEMA_VERSION,
        "sections": sections,
        "source": {
            "code_bindings": source_code_bindings,
            "manifest_payload_sha256": source["payload_sha256"],
            "manifest_sha256": _file_sha256(source_path),
        },
        "status": STATUS,
    }
    return {**payload, "payload_sha256": _payload_digest(payload)}


def _lean_source(record: Mapping[str, Any]) -> str:
    parameters = record["parameters"]
    c = parameters["c"]
    N = parameters["N"]
    prefix = f"c{c}N{N}"
    return f"""import WeilExtremalKernels.CenteredPrincipalSection
import WeilExtremalKernels.Generated.C13N200FiniteClosure

/-!
# Generated centered-section metadata for c={c}, N={N}

This module binds the finite closure to the {N + 1} centered principal
sections with cutoffs 0 through {N}.  It does not cover larger cutoffs.
-/

namespace WeilExtremalKernels.Generated

def {prefix}NestingArtifactPayloadSHA256 : String :=
  "{record['payload_sha256']}"

def {prefix}CertifiedCenteredSectionCount : Nat := {N + 1}

theorem {prefix}CertifiedCenteredSectionCount_eq :
    {prefix}CertifiedCenteredSectionCount = {N + 1} := rfl

theorem {prefix}CenteredCoordinatePreserved
    (M : Nat) (hM : M <= {N}) (i : Fin (2 * M + 1)) :
    centeredIndexCoordinate {N} (centeredFinEmbedding hM i) =
      centeredIndexCoordinate M i :=
  centeredIndexCoordinate_centeredFinEmbedding hM i

theorem {prefix}AllSmallerStrictlyPositive
    (Q : Nat -> (n : Nat) -> FiniteMatrix (2 * n + 1))
    (hnested :
      forall M (hM : M <= {N}),
        Q {c} M = centeredPrincipalSection hM (Q {c} {N}))
    (h200 :
      forall x, x != 0 -> 0 < quadraticForm (Q {c} {N}) x) :
    forall M (hM : M <= {N}) x, x != 0 ->
      0 < quadraticForm (Q {c} M) x :=
  all_smaller_cutoffs_pos_of_centered_nested
    Q {c} {N} hnested h200

end WeilExtremalKernels.Generated
"""


def write_outputs(
    json_path: str | Path,
    lean_path: str | Path,
    finite_closure_artifact: str | Path,
    source_manifest: str | Path,
) -> Dict[str, Any]:
    record = build_centered_nesting_certificate(
        finite_closure_artifact, source_manifest
    )
    json_output = Path(json_path)
    json_output.parent.mkdir(parents=True, exist_ok=True)
    json_output.write_bytes(_canonical_bytes(record))
    lean_output = Path(lean_path)
    lean_output.parent.mkdir(parents=True, exist_ok=True)
    lean_output.write_text(_lean_source(record), encoding="ascii")
    return record


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Bind a finite closure to all centered principal sections."
    )
    parser.add_argument("--finite-closure-artifact", type=Path, required=True)
    parser.add_argument("--source-manifest", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--lean-out", type=Path, required=True)
    args = parser.parse_args(argv)
    record = write_outputs(
        args.out,
        args.lean_out,
        args.finite_closure_artifact,
        args.source_manifest,
    )
    parameters = record["parameters"]
    print(
        "centered principal sections: "
        f"c={parameters['c']} M=0..{parameters['N']} "
        f"count={parameters['certified_section_count']} "
        f"status={record['status']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
