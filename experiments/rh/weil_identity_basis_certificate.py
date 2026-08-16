"""Generate and verify the registered full-Fourier identity-basis certificate.

The sharded Weil assemblers serialize rows in the exact order
``[-N, -N+1, ..., N]``.  Lean's ``centeredIndexCoordinate N`` assigns row
``i`` the same label ``i-N``.  Therefore the coordinate bridge for the full
matrix is the identity, not a numerical change of basis.

This artifact binds that assertion to one canonical source manifest.  It does
not authenticate the source matrix chunks; the route/cross verifier remains
responsible for that independent layer.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any, Dict, Mapping, Sequence


SCHEMA_VERSION = "weil-full-fourier-identity-basis/v1"
GENERATOR = "experiments/rh/weil_identity_basis_certificate.py"
SOURCE_CONVENTION = "row i has Fourier index -N+i"
TARGET_CONVENTION = "Fin row i has centeredIndexCoordinate N i = i-N"
CLAIM_SCOPE = "exact-full-matrix-coordinate-identity-only"
LIMITATIONS = (
    "This certificate does not verify source matrix chunks or LDL arithmetic.",
    "It does not construct or certify the separate full-to-even embedding.",
    "It contains no infinite-dimensional Weil criterion or RH conclusion.",
)


def _canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def _canonical_bytes(value: Any) -> bytes:
    return (_canonical_json(value) + "\n").encode("utf-8")


def _payload_digest(payload: Mapping[str, Any]) -> str:
    return hashlib.sha256(_canonical_json(payload).encode("utf-8")).hexdigest()


def _file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _load_canonical_record(path: Path) -> Dict[str, Any]:
    raw = path.read_bytes()
    record = json.loads(
        raw,
        parse_constant=lambda value: (_ for _ in ()).throw(
            ValueError(f"non-finite JSON constant: {value}")
        ),
    )
    if not isinstance(record, dict) or raw != _canonical_bytes(record):
        raise ValueError("source manifest must be canonical JSON")
    payload_hash = record.get("payload_sha256")
    payload = {key: value for key, value in record.items() if key != "payload_sha256"}
    if not isinstance(payload_hash, str) or _payload_digest(payload) != payload_hash:
        raise ValueError("source manifest payload hash mismatch")
    return record


def _coordinate_parameters(record: Mapping[str, Any]) -> Dict[str, Any]:
    parameters = record.get("parameters")
    if not isinstance(parameters, dict):
        raise ValueError("source manifest has no parameters object")
    c = parameters.get("c")
    N = parameters.get("N")
    dimension = parameters.get("dimension")
    index_order = parameters.get("index_order")
    if (
        isinstance(c, bool)
        or not isinstance(c, int)
        or c < 2
        or isinstance(N, bool)
        or not isinstance(N, int)
        or N < 0
        or isinstance(dimension, bool)
        or not isinstance(dimension, int)
        or dimension != 2 * N + 1
        or index_order != list(range(-N, N + 1))
    ):
        raise ValueError("source manifest does not use registered full Fourier order")
    return {
        "N": N,
        "c": c,
        "dimension": dimension,
        "index_order": index_order,
    }


def _identity_sparse_entries(dimension: int) -> list[list[Any]]:
    return [[index, index, "1"] for index in range(dimension)]


def _positive_checkpoint_binding(
    checkpoint_path: Path,
    source_path: Path,
    source_record: Mapping[str, Any],
    coordinate_parameters: Mapping[str, Any],
) -> Dict[str, Any]:
    checkpoint = _load_canonical_record(checkpoint_path)
    parameters = checkpoint.get("parameters")
    source = checkpoint.get("source")
    result = checkpoint.get("result")
    dimension = coordinate_parameters["dimension"]
    if (
        not isinstance(parameters, dict)
        or parameters.get("c") != coordinate_parameters["c"]
        or parameters.get("N") != coordinate_parameters["N"]
        or parameters.get("dimension") != dimension
        or checkpoint.get("classification") != "positive"
        or not isinstance(result, dict)
        or result.get("dimension") != dimension
        or result.get("certified_positive_pivot_count") != dimension
        or result.get("complete_factorization") is not True
        or result.get("first_unresolved_pivot") is not None
        or not isinstance(source, dict)
        or source.get("manifest_sha256") != _file_sha256(source_path)
        or source.get("manifest_payload_sha256")
        != source_record["payload_sha256"]
    ):
        raise ValueError(
            "checkpoint is not a complete positive factorization of the source"
        )
    return {
        "classification": "positive",
        "file_sha256": _file_sha256(checkpoint_path),
        "payload_sha256": checkpoint["payload_sha256"],
        "positive_pivot_count": dimension,
        "schema_version": checkpoint.get("schema_version"),
    }


def build_identity_basis_certificate(
    source_manifest: str | Path, ldl_checkpoint: str | Path
) -> Dict[str, Any]:
    source_path = Path(source_manifest)
    source_record = _load_canonical_record(source_path)
    parameters = _coordinate_parameters(source_record)
    checkpoint_binding = _positive_checkpoint_binding(
        Path(ldl_checkpoint), source_path, source_record, parameters
    )
    dimension = parameters["dimension"]
    entries = _identity_sparse_entries(dimension)
    matrix_payload = {
        "columns": dimension,
        "default_entry": "0",
        "rows": dimension,
        "sparse_entries": entries,
    }
    matrix_sha256 = _payload_digest(matrix_payload)
    payload = {
        "basis": {
            **matrix_payload,
            "kind": "identity",
            "sha256": matrix_sha256,
        },
        "claim_scope": CLAIM_SCOPE,
        "generator": GENERATOR,
        "ldl_checkpoint": checkpoint_binding,
        "left_inverse": {
            **matrix_payload,
            "kind": "identity",
            "sha256": matrix_sha256,
        },
        "limitations": list(LIMITATIONS),
        "parameters": parameters,
        "schema_version": SCHEMA_VERSION,
        "source": {
            "file_sha256": _file_sha256(source_path),
            "manifest_payload_sha256": source_record["payload_sha256"],
            "schema_version": source_record.get("schema_version"),
        },
        "source_index_convention": SOURCE_CONVENTION,
        "target_index_convention": TARGET_CONVENTION,
    }
    return {**payload, "payload_sha256": _payload_digest(payload)}


def verify_identity_basis_certificate(
    record: Any, source_manifest: str | Path, ldl_checkpoint: str | Path
) -> bool:
    if not isinstance(record, dict):
        return False
    required = {
        "basis",
        "claim_scope",
        "generator",
        "ldl_checkpoint",
        "left_inverse",
        "limitations",
        "parameters",
        "payload_sha256",
        "schema_version",
        "source",
        "source_index_convention",
        "target_index_convention",
    }
    if set(record) != required:
        return False
    payload = {key: value for key, value in record.items() if key != "payload_sha256"}
    if (
        record["schema_version"] != SCHEMA_VERSION
        or record["claim_scope"] != CLAIM_SCOPE
        or record["generator"] != GENERATOR
        or record["limitations"] != list(LIMITATIONS)
        or record["source_index_convention"] != SOURCE_CONVENTION
        or record["target_index_convention"] != TARGET_CONVENTION
        or _payload_digest(payload) != record["payload_sha256"]
    ):
        return False
    try:
        source_path = Path(source_manifest)
        source_record = _load_canonical_record(source_path)
        parameters = _coordinate_parameters(source_record)
        checkpoint_binding = _positive_checkpoint_binding(
            Path(ldl_checkpoint), source_path, source_record, parameters
        )
    except (OSError, TypeError, UnicodeError, ValueError):
        return False
    if record["parameters"] != parameters:
        return False
    if record["ldl_checkpoint"] != checkpoint_binding:
        return False
    source = record["source"]
    if source != {
        "file_sha256": _file_sha256(source_path),
        "manifest_payload_sha256": source_record["payload_sha256"],
        "schema_version": source_record.get("schema_version"),
    }:
        return False
    dimension = parameters["dimension"]
    entries = _identity_sparse_entries(dimension)
    matrix_payload = {
        "columns": dimension,
        "default_entry": "0",
        "rows": dimension,
        "sparse_entries": entries,
    }
    matrix_sha256 = _payload_digest(matrix_payload)
    expected = {
        **matrix_payload,
        "kind": "identity",
        "sha256": matrix_sha256,
    }
    return record["basis"] == expected and record["left_inverse"] == expected


def verify_identity_basis_certificate_file(
    certificate_path: str | Path,
    source_manifest: str | Path,
    ldl_checkpoint: str | Path,
) -> bool:
    try:
        path = Path(certificate_path)
        raw = path.read_bytes()
        record = json.loads(raw)
    except (OSError, TypeError, UnicodeError, ValueError):
        return False
    return (
        raw == _canonical_bytes(record)
        and verify_identity_basis_certificate(
            record, source_manifest, ldl_checkpoint
        )
    )


def write_identity_basis_certificate(
    output_path: str | Path,
    source_manifest: str | Path,
    ldl_checkpoint: str | Path,
) -> Dict[str, Any]:
    record = build_identity_basis_certificate(source_manifest, ldl_checkpoint)
    output = Path(output_path)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_bytes(_canonical_bytes(record))
    return record


def _lean_module_source(record: Mapping[str, Any]) -> str:
    parameters = record["parameters"]
    c = parameters["c"]
    N = parameters["N"]
    dimension = parameters["dimension"]
    prefix = f"c{c}N{N}"
    source = record["source"]
    checkpoint = record["ldl_checkpoint"]
    basis = record["basis"]
    return f"""import WeilExtremalKernels.WeilCoordinateBridge

/-!
# Generated full Fourier coordinate certificate for c={c}, N={N}

This file is generated from one authenticated identity-basis record.  It
binds finite coordinate metadata only; it does not state Gate A, an
infinite-dimensional Weil criterion, or RH.
-/

namespace WeilExtremalKernels.Generated

def {prefix}C : Nat := {c}
def {prefix}N : Nat := {N}
def {prefix}Dimension : Nat := {dimension}

def {prefix}ArtifactPayloadSHA256 : String :=
  "{record['payload_sha256']}"

def {prefix}SourceFileSHA256 : String :=
  "{source['file_sha256']}"

def {prefix}SourcePayloadSHA256 : String :=
  "{source['manifest_payload_sha256']}"

def {prefix}LDLCheckpointFileSHA256 : String :=
  "{checkpoint['file_sha256']}"

def {prefix}LDLCheckpointPayloadSHA256 : String :=
  "{checkpoint['payload_sha256']}"

def {prefix}IdentityBasisSHA256 : String :=
  "{basis['sha256']}"

theorem {prefix}Dimension_eq :
    2 * {prefix}N + 1 = {prefix}Dimension := by
  norm_num [{prefix}N, {prefix}Dimension]

def {prefix}Basis :
    RectangularMatrix {prefix}Dimension {prefix}Dimension :=
  fullFourierIdentityBasis {prefix}N

def {prefix}LeftInverseCertificate :
    LeftInverseCertificate {prefix}Basis := by
  simpa [{prefix}Basis] using
    fullFourierIdentityLeftInverseCertificate {prefix}N

theorem {prefix}RegisteredIndex_eq
    (i : Fin {prefix}Dimension) :
    (registeredFullFourierIndex {prefix}N i : Real) =
      centeredIndexCoordinate {prefix}N i :=
  registeredFullFourierIndex_cast_eq_centeredIndexCoordinate {prefix}N i

theorem {prefix}Congruence_eq
    (A : FiniteMatrix {prefix}Dimension) :
    congruenceMatrix A {prefix}Basis = A := by
  simpa [{prefix}Basis] using
    congruenceMatrix_fullFourierIdentityBasis {prefix}N A

theorem {prefix}QuadraticForm_eq
    (A : FiniteMatrix {prefix}Dimension)
    (x : FiniteVector {prefix}Dimension) :
    quadraticForm (congruenceMatrix A {prefix}Basis) x =
      quadraticForm A x := by
  rw [{prefix}Congruence_eq]

end WeilExtremalKernels.Generated
"""


def write_lean_module(path: str | Path, record: Mapping[str, Any]) -> None:
    output = Path(path)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(_lean_module_source(record), encoding="ascii")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Bind a Weil source manifest to the exact full identity basis."
    )
    parser.add_argument("--source-manifest", type=Path, required=True)
    parser.add_argument("--ldl-checkpoint", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--lean-out", type=Path, required=True)
    args = parser.parse_args(argv)
    record = write_identity_basis_certificate(
        args.out, args.source_manifest, args.ldl_checkpoint
    )
    write_lean_module(args.lean_out, record)
    parameters = record["parameters"]
    print(
        "full Fourier identity basis: "
        f"c={parameters['c']} N={parameters['N']} "
        f"dimension={parameters['dimension']} "
        f"sha256={record['payload_sha256']} lean={args.lean_out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
