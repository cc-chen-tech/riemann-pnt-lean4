"""Integration gate for certificate-chain links 1/2 at small N.

Regenerates the dual-route interval merge for the frozen small-N cases
(c=13, N=4 and N=8) and asserts:

1. entrywise overlap between the two independent interval assembly routes
   is non-empty everywhere (no OverlapError);
2. the merged, symmetrized intervals are consistent with both routes' frozen
   high-precision audit point values from
   groskin_2607_02828_v1_small_n_high_precision_crosscheck.json, up to that
   artifact's own numerical_tolerance (1e-60).

Note (verified 2026-07-22 by recomputing entry (-8,-8) of the N=8 case at
200 dps with both assembly routes): the frozen artifact's
`ccm_hypergeometric_lerch_high_precision_audit` prints are only accurate to
~71 digits despite the advertised 130 audit digits (they deviate 3.7e-71 from
the 200-dps value, while the auxiliary audits agree to 3.6e-121). The
interval artifacts produced by this branch are sound — the merged intervals
do contain the 200-dps truth — so literal containment against the frozen CCM
audit print is too strong a gate. The correct gate is distance-to-interval
bounded by the frozen artifact's own numerical_tolerance.
3. symmetrization actually happened (entry (i,j) == entry (j,i));
4. the shipped merged artifacts match the regenerated merge.

This is the rigorous-interval successor of the pointwise crosscheck; it
still does not close Gate A (registered target is c=100, N=200).
"""

import copy
import json
from decimal import Decimal
from fractions import Fraction
from pathlib import Path

import pytest

from experiments.rh import weil_extremal_interval_overlap as ov
from experiments.rh import weil_schur_feasibility as schur

ROOT = Path(__file__).resolve().parent.parent
REF = ROOT / "experiments" / "rh" / "reference"

CASES = [(13, 4), (13, 8)]
CERTIFICATE_CASES = [(13, 16), (13, 32)]
LEAN_CERTIFICATES = {
    16: (
        "WeilExtremalKernels.Certificates.C13N16",
        "c13N16ArtifactMetadata",
        ROOT / "WeilExtremalKernels" / "Certificates" / "C13N16.lean",
    ),
    32: (
        "WeilExtremalKernels.Certificates.C13N32",
        "c13N32ArtifactMetadata",
        ROOT / "WeilExtremalKernels" / "Certificates" / "C13N32.lean",
    ),
}

AUX = "weil_extremal_interval_auxiliary_closed_form_interval_arb_c{c}_N{n}_prec256.json"
CCM = "weil_extremal_interval_assembly_ccm_hypergeometric_lerch_c{c}_N{n}_prec256.json"
MERGED = "weil_extremal_interval_overlap_c{c}_N{n}_prec256.json"
FROZEN = "groskin_2607_02828_v1_small_n_high_precision_crosscheck.json"


def _load(name):
    return json.loads((REF / name).read_text())


def _route_artifact(route, entries, *, created_utc="2026-07-24T00:00:00Z"):
    payload = {
        "schema_version": ov.ROUTE_SCHEMA_VERSION,
        "c": 13,
        "N": 0,
        "dimension": 1,
        "route": route,
        "prec_bits": 256,
        "index_convention": ov.INDEX_CONVENTION,
        "entries": entries,
        "provenance": {
            "generator": f"{route}.py",
            "note": "test route",
            "created_utc": created_utc,
        },
    }
    return {**payload, "payload_sha256": ov._payload_digest(payload)}


def _rehash(record):
    payload = {key: value for key, value in record.items() if key != "payload_sha256"}
    record["payload_sha256"] = ov._payload_digest(payload)


def _finite_margin(artifact):
    certificate = artifact["certificate"]
    return Fraction(certificate["center_lower_bound"]) - Fraction(
        certificate["perturbation_row_bound"]
    )


def _frozen_case(c, n):
    frozen = _load(FROZEN)
    for case in frozen["cases"]:
        if case["c"] == c and case["N"] == n:
            return case
    raise AssertionError(f"no frozen case for c={c}, N={n}")


@pytest.mark.parametrize("c,n", CASES)
def test_dual_route_merge_contains_frozen_audit_values(c, n):
    aux = _load(AUX.format(c=c, n=n))
    ccm = _load(CCM.format(c=c, n=n))
    merged = ov.merge_artifacts(aux, ccm)  # raises OverlapError on empty intersection
    case = _frozen_case(c, n)
    tolerance = Decimal(case["numerical_tolerance"])
    dim = merged["dimension"]
    assert len(merged["entries"]) == dim * dim == case["entry_count"]
    worst = Decimal(0)
    violations = []
    for idx, (lo, hi) in enumerate(merged["entries"]):
        lo_d, hi_d = Decimal(lo), Decimal(hi)
        for field in (
            "auxiliary_closed_form_high_precision_audit",
            "ccm_hypergeometric_lerch_high_precision_audit",
        ):
            value = Decimal(case["entries"][idx][field])
            distance = max(lo_d - value, value - hi_d, Decimal(0))
            worst = max(worst, distance)
            if distance > tolerance:
                violations.append((idx, field, str(distance)))
    assert violations == []
    # Sanity: consistency is much better than the frozen tolerance demands.
    assert worst < tolerance


@pytest.mark.parametrize("c,n", CASES)
def test_merged_artifact_is_symmetric(c, n):
    merged = ov.merge_artifacts(_load(AUX.format(c=c, n=n)), _load(CCM.format(c=c, n=n)))
    dim = merged["dimension"]
    entries = merged["entries"]
    for i in range(dim):
        for j in range(i + 1, dim):
            assert entries[i * dim + j] == entries[j * dim + i]


@pytest.mark.parametrize("c,n", CASES)
def test_shipped_merged_artifact_matches_regeneration(c, n):
    shipped = _load(MERGED.format(c=c, n=n))
    regenerated = ov.merge_artifacts(_load(AUX.format(c=c, n=n)), _load(CCM.format(c=c, n=n)))
    assert shipped["entries"] == regenerated["entries"]
    ov.validate_artifact(shipped)


def test_touching_route_intervals_are_rejected_as_non_strict_overlap():
    first = _route_artifact("route-a", [["0", "1"]])
    second = _route_artifact("route-b", [["1", "2"]])

    with pytest.raises(ov.OverlapError) as error:
        ov.merge_artifacts(first, second)

    assert error.value.report["kind"] == "route_intersection"
    assert error.value.report["strict_overlap"] is False
    assert error.value.report["absolute_gap"] == "0"


def test_certificate_output_is_deterministic_and_records_strict_proof():
    first = _route_artifact("route-a", [["0", "2"]])
    second = _route_artifact("route-b", [["0.5", "1.5"]])

    merged_once = ov.merge_artifacts(first, second)
    merged_twice = ov.merge_artifacts(first, second)

    assert merged_once == merged_twice
    assert merged_once["schema_version"] == ov.OVERLAP_SCHEMA_VERSION
    assert merged_once["strict_overlap"] == {
        "all_strict": True,
        "predicate": "max(lower_a,lower_b) < min(upper_a,upper_b)",
        "route_intersection_count": 1,
        "symmetry_intersection_count": 0,
    }
    assert [source["payload_sha256"] for source in merged_once["source_artifacts"]] == [
        first["payload_sha256"],
        second["payload_sha256"],
    ]
    assert merged_once["certificate"]["result"]["certified_pd"] is True
    ov.validate_artifact(merged_once)


@pytest.mark.parametrize(
    "tamper",
    ["strict_overlap", "source_hash", "ldlt_diagonal"],
)
def test_rehashed_semantic_tampering_is_rejected(tamper):
    merged = ov.merge_artifacts(
        _route_artifact("route-a", [["1", "2"]]),
        _route_artifact("route-b", [["1.25", "1.75"]]),
    )
    tampered = copy.deepcopy(merged)
    if tamper == "strict_overlap":
        tampered["strict_overlap"]["all_strict"] = False
    elif tamper == "source_hash":
        tampered["source_artifacts"][0]["payload_sha256"] = "0" * 64
    else:
        tampered["certificate"]["diagonal"][0] = "0"
        certificate_payload = {
            key: value
            for key, value in tampered["certificate"].items()
            if key != "payload_sha256"
        }
        tampered["certificate"]["payload_sha256"] = ov._payload_digest(
            certificate_payload
        )
    _rehash(tampered)

    with pytest.raises(ov.ArtifactError):
        ov.validate_artifact(tampered)


@pytest.mark.parametrize("c,n", CERTIFICATE_CASES)
def test_shipped_primary_certificate_is_replayable_and_pinned_in_lean(c, n):
    artifact = _load(MERGED.format(c=c, n=n))

    ov.validate_artifact(artifact)

    assert artifact["schema_version"] == ov.OVERLAP_SCHEMA_VERSION
    assert artifact["strict_overlap"]["all_strict"] is True
    assert artifact["certificate"]["claim_scope"] == (
        "finite-rational-interval-matrix-only"
    )
    assert artifact["certificate"]["result"] == {
        "center_lower_bound": artifact["certificate"]["center_lower_bound"],
        "certified_pd": True,
        "certified_psd": True,
        "exact_shifted_reconstruction": True,
        "nonnegative_diagonal": True,
        "perturbation_row_bound": artifact["certificate"][
            "perturbation_row_bound"
        ],
        "strict_budget": True,
    }
    lean_source = (
        ROOT / "WeilExtremalKernels" / "FiniteQuadraticForm.lean"
    ).read_text()
    assert artifact["payload_sha256"] in lean_source


@pytest.mark.parametrize("c,n", CERTIFICATE_CASES)
def test_generated_lean_certificate_module_is_current(c, n):
    artifact = _load(MERGED.format(c=c, n=n))
    namespace, metadata_constant, path = LEAN_CERTIFICATES[n]

    expected = ov.render_lean_certificate(
        artifact,
        namespace=namespace,
        metadata_constant=metadata_constant,
    )

    assert path.read_text() == expected
    assert "theorem certificate_valid : certificate.Valid := by" in expected
    assert (
        "theorem certificate_strictValid : certificate.StrictValid := by"
        in expected
    )
    assert "theorem artifact_quadraticForm_pos" in expected
    assert "(hbounds : ∀ i j," in expected
    assert "native_decide" in expected
    assert artifact["payload_sha256"] in expected


@pytest.mark.parametrize("c,n", CERTIFICATE_CASES)
def test_current_finite_certificates_report_missing_analytic_bounds(c, n):
    artifact = _load(MERGED.format(c=c, n=n))

    result = schur.diagnose(artifact)

    assert result["finite_certificate"]["epsilon"] == str(_finite_margin(artifact))
    assert result["overall_verdict"] == schur.OVERALL_MISSING
    assert result["routes"]["normalized_tail"]["verdict"] == schur.ROUTE_UNAVAILABLE
    assert result["routes"]["schur"]["verdict"] == schur.ROUTE_UNAVAILABLE


def test_exact_normalized_tail_boundary_closes():
    artifact = _load(MERGED.format(c=13, n=16))
    epsilon = _finite_margin(artifact)
    bounds = schur.build_analytic_bounds(
        artifact,
        {"normalized_tail_operator_norm_upper": str(epsilon)},
    )

    result = schur.diagnose(artifact, bounds)

    assert result["overall_verdict"] == schur.OVERALL_CLOSES
    assert result["routes"]["normalized_tail"] == {
        "verdict": schur.ROUTE_CLOSES,
        "margin": "0",
        "missing": [],
    }


def test_exact_schur_boundary_closes():
    artifact = _load(MERGED.format(c=13, n=16))
    epsilon = _finite_margin(artifact)
    bounds = schur.build_analytic_bounds(
        artifact,
        {
            "high_block_lower": str(epsilon),
            "coupling_norm_upper": str(epsilon),
        },
    )

    result = schur.diagnose(artifact, bounds)

    assert result["overall_verdict"] == schur.OVERALL_CLOSES
    assert result["routes"]["schur"] == {
        "verdict": schur.ROUTE_CLOSES,
        "margin": "0",
        "missing": [],
    }


def test_complete_insufficient_bounds_report_failure():
    artifact = _load(MERGED.format(c=13, n=16))
    epsilon = _finite_margin(artifact)
    bounds = schur.build_analytic_bounds(
        artifact,
        {
            "normalized_tail_operator_norm_upper": str(epsilon + 1),
            "high_block_lower": "0",
            "coupling_norm_upper": "1",
        },
    )

    result = schur.diagnose(artifact, bounds)

    assert result["overall_verdict"] == schur.OVERALL_FAILS
    assert result["routes"]["normalized_tail"]["verdict"] == schur.ROUTE_FAILS
    assert result["routes"]["schur"]["verdict"] == schur.ROUTE_FAILS


@pytest.mark.parametrize(
    "tamper",
    ["source_hash", "normalization", "payload"],
)
def test_schur_analytic_artifact_tampering_is_rejected(tamper):
    artifact = _load(MERGED.format(c=13, n=16))
    bounds = schur.build_analytic_bounds(
        artifact,
        {"normalized_tail_operator_norm_upper": "0"},
    )
    tampered = copy.deepcopy(bounds)
    if tamper == "source_hash":
        tampered["source_overlap_payload_sha256"] = "0" * 64
        tampered["payload_sha256"] = schur._analytic_payload_digest(tampered)
    elif tamper == "normalization":
        tampered["normalization_id"] = "different-normalization/v1"
        tampered["payload_sha256"] = schur._analytic_payload_digest(tampered)
    else:
        tampered["bounds"]["normalized_tail_operator_norm_upper"] = "1"

    with pytest.raises(schur.FeasibilityError):
        schur.validate_analytic_bounds(tampered, artifact)
