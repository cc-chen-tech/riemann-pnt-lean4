"""Tests for the rigorous CCM hypergeometric/Lerch interval assembly route."""

import copy
import json
from decimal import Decimal
from pathlib import Path

import pytest

from experiments.rh import weil_extremal_interval_ccm as interval_ccm


ROOT = Path(__file__).parents[1]
REFERENCE_DIR = ROOT / "experiments" / "rh" / "reference"
FROZEN_CROSSCHECK = (
    REFERENCE_DIR / "groskin_2607_02828_v1_small_n_high_precision_crosscheck.json"
)
CASES = [(13, 4), (13, 8)]
PREC_BITS = 256
ARTIFACT_PATHS = {
    case: REFERENCE_DIR / interval_ccm.artifact_filename(case[0], case[1], PREC_BITS)
    for case in CASES
}
# Widths are dominated by the documented 70-digit reference-comparison margin
# (see the module docstring); anything at this scale or below is genuine.
MAX_INTERVAL_WIDTH = Decimal("1e-60")


def _load_json(path: Path):
    return json.loads(path.read_bytes())


def _frozen_case_records():
    records = _load_json(FROZEN_CROSSCHECK)["cases"]
    return {(record["c"], record["N"]): record for record in records}


def _frozen_ccm_values(case_record):
    return {
        (entry["i"], entry["j"]): Decimal(entry["ccm_hypergeometric_lerch"])
        for entry in case_record["entries"]
    }


def _interval_at(artifact, i: int, j: int):
    N = artifact["N"]
    dimension = artifact["dimension"]
    lo, hi = artifact["entries"][(i + N) * dimension + (j + N)]
    return Decimal(lo), Decimal(hi)


def test_artifact_files_exist_and_verify():
    for case, path in ARTIFACT_PATHS.items():
        assert path.is_file(), f"missing interval artifact for case {case}: {path}"
        assert interval_ccm.verify_interval_artifact_file(path), (
            f"interval artifact for case {case} failed schema/hash verification"
        )


def test_artifact_schema_and_interval_quality():
    for c, N in CASES:
        artifact = _load_json(ARTIFACT_PATHS[(c, N)])
        assert artifact["schema_version"] == interval_ccm.SCHEMA_VERSION
        assert artifact["route"] == interval_ccm.ROUTE == "ccm_hypergeometric_lerch"
        assert artifact["index_convention"] == "fourier -N..N row-major"
        assert artifact["c"] == c and artifact["N"] == N
        assert artifact["dimension"] == 2 * N + 1
        assert artifact["prec_bits"] == PREC_BITS
        assert len(artifact["entries"]) == artifact["dimension"] ** 2
        for lo, hi in artifact["entries"]:
            lo, hi = Decimal(lo), Decimal(hi)
            assert lo.is_finite() and hi.is_finite()
            assert lo <= hi
            width = hi - lo
            assert width >= 0
            assert width <= MAX_INTERVAL_WIDTH, (
                f"interval width {width} exceeds the rigorous-ball scale bound"
            )


def test_frozen_point_values_are_contained():
    """Hard correctness gate: every frozen CCM point value lies in [lo, hi]."""
    frozen_cases = _frozen_case_records()
    for case in CASES:
        assert case in frozen_cases, f"no frozen cross-check record for {case}"
        artifact = _load_json(ARTIFACT_PATHS[case])
        frozen_values = _frozen_ccm_values(frozen_cases[case])
        assert len(frozen_values) == artifact["dimension"] ** 2
        for (i, j), value in frozen_values.items():
            lo, hi = _interval_at(artifact, i, j)
            assert lo <= value <= hi, (
                f"case {case} entry {(i, j)}: frozen value {value} "
                f"outside [{lo}, {hi}]"
            )


def test_symmetric_entries_have_nonempty_intersection():
    """Symmetric (i, j)/(j, i) intervals must overlap around the frozen value."""
    frozen_cases = _frozen_case_records()
    for case in CASES:
        artifact = _load_json(ARTIFACT_PATHS[case])
        frozen_values = _frozen_ccm_values(frozen_cases[case])
        N = artifact["N"]
        for i in range(-N, N + 1):
            for j in range(i + 1, N + 1):
                lo_ij, hi_ij = _interval_at(artifact, i, j)
                lo_ji, hi_ji = _interval_at(artifact, j, i)
                intersection_lo = max(lo_ij, lo_ji)
                intersection_hi = min(hi_ij, hi_ji)
                assert intersection_lo <= intersection_hi, (
                    f"case {case}: symmetric intervals {(i, j)} and {(j, i)} "
                    "do not overlap"
                )
                assert frozen_values[(i, j)] == frozen_values[(j, i)]
                assert intersection_lo <= frozen_values[(i, j)] <= intersection_hi


def test_regeneration_matches_shipped_artifacts():
    for c, N in CASES:
        rebuilt = interval_ccm.build_interval_artifact(c, N, PREC_BITS)
        shipped = _load_json(ARTIFACT_PATHS[(c, N)])
        assert rebuilt["entries"] == shipped["entries"], (
            f"case {(c, N)}: regenerated intervals differ from the shipped artifact"
        )
        for key in ("c", "N", "dimension", "index_convention", "prec_bits", "route"):
            assert rebuilt[key] == shipped[key]


def test_verify_rejects_tampered_artifacts():
    artifact = _load_json(ARTIFACT_PATHS[(13, 4)])
    assert interval_ccm.verify_interval_artifact(artifact)

    tampered_entry = copy.deepcopy(artifact)
    lo, hi = tampered_entry["entries"][0]
    tampered_entry["entries"][0] = [hi, lo]
    assert not interval_ccm.verify_interval_artifact(tampered_entry)

    tampered_hash = copy.deepcopy(artifact)
    tampered_hash["prec_bits"] = PREC_BITS * 2
    assert not interval_ccm.verify_interval_artifact(tampered_hash)

    tampered_route = copy.deepcopy(artifact)
    tampered_route["route"] = "auxiliary_closed_form"
    assert not interval_ccm.verify_interval_artifact(tampered_route)


def test_cli_writes_verifiable_artifact(tmp_path):
    status = interval_ccm.main(
        [
            "--case",
            "13:4",
            "--prec-bits",
            str(PREC_BITS),
            "--output-dir",
            str(tmp_path),
        ]
    )
    assert status == 0
    output = tmp_path / interval_ccm.artifact_filename(13, 4, PREC_BITS)
    assert interval_ccm.verify_interval_artifact_file(output)


def test_invalid_parameters_are_rejected():
    with pytest.raises(ValueError):
        interval_ccm.assemble_ccm_interval(1, 4, PREC_BITS)
    with pytest.raises(ValueError):
        interval_ccm.assemble_ccm_interval(13, -1, PREC_BITS)
    with pytest.raises(ValueError):
        interval_ccm.assemble_ccm_interval(13, 4, 32)
