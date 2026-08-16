"""Exact finite-to-infinite feasibility gate for certified Weil blocks.

The diagnostic combines an existing dual-route finite certificate with
separately supplied analytic tail or Schur bounds. It checks only sufficient
inequalities. Missing analytic bounds produce an explicit non-closing verdict;
they are never replaced by numerical guesses.
"""

from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any, Mapping, Optional, Sequence

from experiments.rh import weil_extremal_interval_overlap as overlap

ANALYTIC_SCHEMA_VERSION = "weil-finite-to-infinite-schur-bounds/v1"
NORMALIZATION_ID = "euclidean-fourier-raw/v1"
CLAIM_SCOPE = "finite-to-infinite sufficient bounds only; no RH claim"

OVERALL_CLOSES = "CLOSES"
OVERALL_FAILS = "BOUND_FAILS"
OVERALL_MISSING = "MISSING_ANALYTIC_BOUNDS"

ROUTE_CLOSES = "CLOSES"
ROUTE_FAILS = "BOUND_FAILS"
ROUTE_UNAVAILABLE = "UNAVAILABLE"

BOUND_KEYS = {
    "normalized_tail_operator_norm_upper",
    "high_block_lower",
    "coupling_norm_upper",
}

ANALYTIC_REQUIRED_KEYS = {
    "schema_version",
    "source_overlap_payload_sha256",
    "c",
    "N",
    "dimension",
    "index_convention",
    "normalization_id",
    "claim_scope",
    "bounds",
    "provenance",
    "payload_sha256",
}


class FeasibilityError(ValueError):
    """Raised when an analytic bounds artifact is invalid or mismatched."""


def _fraction(value: Any, *, field: str) -> Fraction:
    if not isinstance(value, str):
        raise FeasibilityError(f"{field} must be an exact rational string")
    try:
        return Fraction(value)
    except (ValueError, ZeroDivisionError) as error:
        raise FeasibilityError(f"{field} is not a valid rational string") from error


def _fraction_str(value: Optional[Fraction]) -> Optional[str]:
    return None if value is None else str(value)


def _analytic_payload_digest(record: Mapping[str, Any]) -> str:
    payload = {key: value for key, value in record.items() if key != "payload_sha256"}
    return overlap._payload_digest(payload)


def validate_analytic_bounds(
    record: Any,
    source_overlap: Mapping[str, Any],
) -> None:
    """Validate one exact analytic-bounds artifact against its finite source."""
    overlap.validate_artifact(source_overlap, label="finite overlap source")
    if not isinstance(record, dict) or set(record) != ANALYTIC_REQUIRED_KEYS:
        raise FeasibilityError("analytic bounds artifact has incorrect fields")
    if record["schema_version"] != ANALYTIC_SCHEMA_VERSION:
        raise FeasibilityError("analytic bounds schema_version mismatch")
    if record["claim_scope"] != CLAIM_SCOPE:
        raise FeasibilityError("analytic bounds claim_scope mismatch")
    if record["normalization_id"] != NORMALIZATION_ID:
        raise FeasibilityError(
            "analytic bounds normalization does not match the finite certificate"
        )
    if record["payload_sha256"] != _analytic_payload_digest(record):
        raise FeasibilityError("analytic bounds payload hash mismatch")
    if record["source_overlap_payload_sha256"] != source_overlap["payload_sha256"]:
        raise FeasibilityError("analytic bounds source overlap hash mismatch")
    for field in ("c", "N", "dimension", "index_convention"):
        if record[field] != source_overlap[field]:
            raise FeasibilityError(f"analytic bounds {field} mismatch")
    if not isinstance(record["provenance"], dict):
        raise FeasibilityError("analytic bounds provenance must be an object")
    bounds = record["bounds"]
    if not isinstance(bounds, dict) or not set(bounds).issubset(BOUND_KEYS):
        raise FeasibilityError("analytic bounds contains unknown fields")
    parsed = {
        key: _fraction(value, field=f"bounds.{key}")
        for key, value in bounds.items()
    }
    delta = parsed.get("normalized_tail_operator_norm_upper")
    gamma = parsed.get("high_block_lower")
    beta = parsed.get("coupling_norm_upper")
    if delta is not None and delta < 0:
        raise FeasibilityError("normalized tail upper bound must be nonnegative")
    if gamma is not None and gamma < 0:
        raise FeasibilityError("high block lower bound must be nonnegative")
    if beta is not None and beta < 0:
        raise FeasibilityError("coupling upper bound must be nonnegative")


def build_analytic_bounds(
    source_overlap: Mapping[str, Any],
    bounds: Mapping[str, str],
    *,
    provenance: Optional[Mapping[str, Any]] = None,
) -> dict[str, Any]:
    """Build a canonical hash-bound analytic artifact for experiments/tests."""
    overlap.validate_artifact(source_overlap, label="finite overlap source")
    payload = {
        "schema_version": ANALYTIC_SCHEMA_VERSION,
        "source_overlap_payload_sha256": source_overlap["payload_sha256"],
        "c": source_overlap["c"],
        "N": source_overlap["N"],
        "dimension": source_overlap["dimension"],
        "index_convention": source_overlap["index_convention"],
        "normalization_id": NORMALIZATION_ID,
        "claim_scope": CLAIM_SCOPE,
        "bounds": dict(bounds),
        "provenance": dict(provenance or {"generator": __name__}),
    }
    record = {**payload, "payload_sha256": overlap._payload_digest(payload)}
    validate_analytic_bounds(record, source_overlap)
    return record


def _route(
    *,
    verdict: str,
    margin: Optional[Fraction],
    missing: Sequence[str],
) -> dict[str, Any]:
    return {
        "verdict": verdict,
        "margin": _fraction_str(margin),
        "missing": list(missing),
    }


def diagnose(
    source_overlap: Mapping[str, Any],
    analytic_bounds: Optional[Mapping[str, Any]] = None,
) -> dict[str, Any]:
    """Return an exact closure diagnosis for one finite overlap artifact."""
    overlap.validate_artifact(source_overlap, label="finite overlap source")
    certificate = source_overlap["certificate"]
    mu = _fraction(certificate["center_lower_bound"], field="center_lower_bound")
    rho = _fraction(
        certificate["perturbation_row_bound"],
        field="perturbation_row_bound",
    )
    epsilon = mu - rho
    if epsilon <= 0:
        raise FeasibilityError("finite certificate has no positive strict margin")

    parsed: dict[str, Fraction] = {}
    analytic_hash: Optional[str] = None
    if analytic_bounds is not None:
        validate_analytic_bounds(analytic_bounds, source_overlap)
        analytic_hash = analytic_bounds["payload_sha256"]
        parsed = {
            key: _fraction(value, field=f"bounds.{key}")
            for key, value in analytic_bounds["bounds"].items()
        }

    delta = parsed.get("normalized_tail_operator_norm_upper")
    gamma = parsed.get("high_block_lower")
    beta = parsed.get("coupling_norm_upper")

    if delta is None:
        normalized = _route(
            verdict=ROUTE_UNAVAILABLE,
            margin=None,
            missing=["normalized_tail_operator_norm_upper"],
        )
    else:
        normalized_margin = epsilon - delta
        normalized = _route(
            verdict=ROUTE_CLOSES if normalized_margin >= 0 else ROUTE_FAILS,
            margin=normalized_margin,
            missing=[],
        )

    schur_missing = [
        field
        for field, value in (
            ("high_block_lower", gamma),
            ("coupling_norm_upper", beta),
        )
        if value is None
    ]
    if schur_missing:
        schur = _route(
            verdict=ROUTE_UNAVAILABLE,
            margin=None,
            missing=schur_missing,
        )
    else:
        assert gamma is not None and beta is not None
        schur_margin = epsilon * gamma - beta * beta
        schur = _route(
            verdict=ROUTE_CLOSES if schur_margin >= 0 else ROUTE_FAILS,
            margin=schur_margin,
            missing=[],
        )

    route_verdicts = {normalized["verdict"], schur["verdict"]}
    if ROUTE_CLOSES in route_verdicts:
        overall = OVERALL_CLOSES
    elif ROUTE_FAILS in route_verdicts:
        overall = OVERALL_FAILS
    else:
        overall = OVERALL_MISSING

    obligations = []
    if normalized["verdict"] == ROUTE_UNAVAILABLE:
        obligations.append(
            "prove a normalized tail operator-norm upper bound in the stated normalization"
        )
    elif normalized["verdict"] == ROUTE_FAILS:
        obligations.append(
            "sharpen the normalized tail bound or improve the certified finite margin"
        )
    if schur["verdict"] == ROUTE_UNAVAILABLE:
        obligations.append(
            "prove both the high-block lower bound and low/high coupling upper bound"
        )
    elif schur["verdict"] == ROUTE_FAILS:
        obligations.append(
            "sharpen Schur bounds until beta^2 <= epsilon*gamma"
        )

    return {
        "schema_version": "weil-finite-to-infinite-schur-diagnostic/v1",
        "source_overlap_payload_sha256": source_overlap["payload_sha256"],
        "analytic_bounds_payload_sha256": analytic_hash,
        "parameters": {
            "c": source_overlap["c"],
            "N": source_overlap["N"],
            "dimension": source_overlap["dimension"],
            "index_convention": source_overlap["index_convention"],
            "normalization_id": NORMALIZATION_ID,
        },
        "finite_certificate": {
            "center_lower_bound": str(mu),
            "perturbation_row_bound": str(rho),
            "epsilon": str(epsilon),
        },
        "analytic_bounds": {
            "delta": _fraction_str(delta),
            "gamma": _fraction_str(gamma),
            "beta": _fraction_str(beta),
        },
        "routes": {
            "normalized_tail": normalized,
            "schur": schur,
        },
        "overall_verdict": overall,
        "remaining_obligations": obligations,
        "scope_warning": (
            "A closing verdict checks only a sufficient implication from supplied "
            "bounds. It is not an RH result unless the actual analytic Weil bounds "
            "and all limiting/support obligations are separately proved."
        ),
    }


def _load_json(path: str | Path, *, label: str) -> dict[str, Any]:
    source = Path(path)
    try:
        value = json.loads(source.read_text())
    except (OSError, json.JSONDecodeError) as error:
        raise FeasibilityError(f"{label}: cannot read JSON: {error}") from error
    if not isinstance(value, dict):
        raise FeasibilityError(f"{label}: root must be an object")
    return value


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Exact finite-to-infinite Schur feasibility diagnostic"
    )
    parser.add_argument("--overlap", required=True, help="validated overlap artifact")
    parser.add_argument(
        "--analytic-bounds",
        help="optional exact analytic tail/Schur bounds artifact",
    )
    args = parser.parse_args(argv)
    try:
        source = overlap.load_artifact(args.overlap, label="finite overlap source")
        analytic = (
            _load_json(args.analytic_bounds, label="analytic bounds")
            if args.analytic_bounds
            else None
        )
        result = diagnose(source, analytic)
    except (overlap.ArtifactError, FeasibilityError) as error:
        print(json.dumps({"error": str(error)}, sort_keys=True), file=sys.stderr)
        return 2
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
