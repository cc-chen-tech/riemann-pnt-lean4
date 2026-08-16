"""Combine sharp inverse and residual artifacts into one finite closure record.

The combiner accepts only canonical, internally hashed artifacts that bind the
same c, N, dimension, checkpoint, and workspace.  It then checks the exact
rational chain

    rho_upper < 10^-80 < coercivity_margin_lower.

On success it emits both a combined JSON certificate and a Lean module that
checks the large rational inequalities.  The Lean module verifies the scalar
budget comparison; it does not replay the external Arb block arithmetic.
"""

from __future__ import annotations

import argparse
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, Mapping, Sequence

from weil_ldl_coercivity_preflight import (
    _canonical_bytes,
    _file_sha256,
    _load_canonical,
    _payload_digest,
    _scientific,
)


SCHEMA_VERSION = "weil-ldl-finite-closure/v1"
GENERATOR = "experiments/rh/weil_ldl_finite_closure_certificate.py"
STATUS = "FINITE_STRICT_POSITIVITY_BUDGET_CLOSES"
THRESHOLD = Fraction(1, 10**80)

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)


def _common_parameters(record: Mapping[str, Any]) -> Dict[str, int]:
    parameters = record.get("parameters")
    if not isinstance(parameters, dict):
        raise ValueError("artifact parameters are missing")
    result = {
        key: parameters.get(key) for key in ("c", "N", "dimension")
    }
    if any(
        isinstance(value, bool) or not isinstance(value, int)
        for value in result.values()
    ):
        raise ValueError("artifact coordinate parameters are invalid")
    if result["dimension"] != 2 * result["N"] + 1:
        raise ValueError("artifact dimension does not equal 2*N+1")
    return result


def build_finite_closure_certificate(
    sharp_inverse_artifact: str | Path,
    residual_artifact: str | Path,
) -> Dict[str, Any]:
    sharp_path = Path(sharp_inverse_artifact)
    residual_path = Path(residual_artifact)
    sharp = _load_canonical(sharp_path)
    residual = _load_canonical(residual_path)

    if (
        sharp.get("schema_version") != "weil-ldl-sharp-inverse-preflight/v1"
        or sharp.get("status") != "AWAITING_RESIDUAL_ROW_BOUND"
        or residual.get("schema_version") != "weil-ldl-residual-row-bound/v1"
        or residual.get("status")
        != "RESIDUAL_BELOW_PREREGISTERED_THRESHOLD"
    ):
        raise ValueError("input artifacts do not have the required statuses")

    parameters = _common_parameters(sharp)
    if _common_parameters(residual) != parameters:
        raise ValueError("input artifacts describe different matrix parameters")
    if sharp.get("checkpoint") != residual.get("checkpoint"):
        raise ValueError("input artifacts bind different LDL checkpoints")
    if sharp.get("workspace") != residual.get("workspace"):
        raise ValueError("input artifacts bind different LDL workspaces")

    sharp_bounds = sharp.get("bounds")
    residual_bounds = residual.get("bounds")
    if not isinstance(sharp_bounds, dict) or not isinstance(residual_bounds, dict):
        raise ValueError("input artifact bounds are missing")
    delta = Fraction(sharp_bounds["delta_lower"])
    kappa = Fraction(sharp_bounds["kappa_upper"])
    margin = Fraction(sharp_bounds["coercivity_margin_lower"])
    rho = Fraction(residual_bounds["rho_upper"])
    residual_threshold = Fraction(residual_bounds["preregistered_threshold"])
    if (
        delta <= 0
        or kappa <= 0
        or margin != delta / kappa
        or residual_threshold != THRESHOLD
        or not rho < THRESHOLD
        or not THRESHOLD < margin
    ):
        raise ValueError("exact finite positivity budget does not close")

    gap = margin - rho
    payload = {
        "bounds": {
            "coercivity_margin_lower": str(margin),
            "coercivity_margin_lower_scientific": _scientific(margin),
            "delta_lower": str(delta),
            "kappa_upper": str(kappa),
            "preregistered_threshold": str(THRESHOLD),
            "rho_upper": str(rho),
            "rho_upper_scientific": _scientific(rho),
            "strict_gap_lower": str(gap),
            "strict_gap_lower_scientific": _scientific(gap),
        },
        "checkpoint": sharp["checkpoint"],
        "claim_scope": "finite-401-by-401-strict-positivity-budget-only",
        "generator": GENERATOR,
        "inputs": {
            "residual": {
                "file_sha256": _file_sha256(residual_path),
                "payload_sha256": residual["payload_sha256"],
            },
            "sharp_inverse": {
                "file_sha256": _file_sha256(sharp_path),
                "payload_sha256": sharp["payload_sha256"],
            },
        },
        "limitations": [
            "Lean checks the scalar rational inequalities but not the Arb block replay.",
            "This is one finite c=13, N=200 matrix only.",
            "No all-N theorem, infinite-dimensional Weil criterion, or RH conclusion is included.",
        ],
        "parameters": parameters,
        "proof_obligations": {
            "coercivity_margin_above_threshold": True,
            "residual_below_threshold": True,
            "rho_strictly_below_delta_over_kappa": True,
        },
        "schema_version": SCHEMA_VERSION,
        "status": STATUS,
        "workspace": sharp["workspace"],
    }
    return {**payload, "payload_sha256": _payload_digest(payload)}


def _rat_expression(value: Fraction) -> str:
    return f"({value.numerator} : Rat) / {value.denominator}"


def _lean_source(record: Mapping[str, Any]) -> str:
    parameters = record["parameters"]
    bounds = record["bounds"]
    inputs = record["inputs"]
    prefix = f"c{parameters['c']}N{parameters['N']}"
    rho = Fraction(bounds["rho_upper"])
    threshold = Fraction(bounds["preregistered_threshold"])
    margin = Fraction(bounds["coercivity_margin_lower"])
    return f"""import WeilExtremalKernels.IntervalLDLCoercivity

/-!
# Generated scalar closure for c={parameters['c']}, N={parameters['N']}

This module checks the exact rational budget inequalities generated from the
sharp inverse and residual artifacts.  It does not replay Arb matrix blocks.
-/

namespace WeilExtremalKernels.Generated

def {prefix}ClosureArtifactPayloadSHA256 : String :=
  "{record['payload_sha256']}"

def {prefix}SharpInverseArtifactSHA256 : String :=
  "{inputs['sharp_inverse']['file_sha256']}"

def {prefix}ResidualArtifactSHA256 : String :=
  "{inputs['residual']['file_sha256']}"

def {prefix}RhoUpper : Rat := {_rat_expression(rho)}

def {prefix}PreregisteredThreshold : Rat :=
  {_rat_expression(threshold)}

def {prefix}CoercivityMarginLower : Rat :=
  {_rat_expression(margin)}

theorem {prefix}Rho_lt_threshold :
    {prefix}RhoUpper < {prefix}PreregisteredThreshold := by
  native_decide

theorem {prefix}Threshold_lt_coercivityMargin :
    {prefix}PreregisteredThreshold < {prefix}CoercivityMarginLower := by
  native_decide

theorem {prefix}Rho_lt_coercivityMargin :
    {prefix}RhoUpper < {prefix}CoercivityMarginLower :=
  lt_trans {prefix}Rho_lt_threshold
    {prefix}Threshold_lt_coercivityMargin

end WeilExtremalKernels.Generated
"""


def write_outputs(
    json_path: str | Path,
    lean_path: str | Path,
    sharp_inverse_artifact: str | Path,
    residual_artifact: str | Path,
) -> Dict[str, Any]:
    record = build_finite_closure_certificate(
        sharp_inverse_artifact, residual_artifact
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
        description="Combine sharp inverse and residual finite closure artifacts."
    )
    parser.add_argument("--sharp-inverse-artifact", type=Path, required=True)
    parser.add_argument("--residual-artifact", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--lean-out", type=Path, required=True)
    args = parser.parse_args(argv)
    record = write_outputs(
        args.out,
        args.lean_out,
        args.sharp_inverse_artifact,
        args.residual_artifact,
    )
    print(
        "finite closure: "
        f"rho<={record['bounds']['rho_upper_scientific']} "
        f"margin>={record['bounds']['coercivity_margin_lower_scientific']} "
        f"gap>={record['bounds']['strict_gap_lower_scientific']} "
        f"status={record['status']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
