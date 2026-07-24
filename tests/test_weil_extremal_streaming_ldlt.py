import copy
import hashlib
import json
import subprocess
import sys
from fractions import Fraction
from pathlib import Path

import pytest


FULL_CHECKPOINT = (
    Path(__file__).parents[1]
    / "experiments"
    / "rh"
    / "reference"
    / "groskin_2607_02828_v1_c100_N200_streaming_ldlt_896_checkpoint.json"
)
FULL_CHECKPOINT_SHA256 = (
    "1af647074af73dd617cdb3d027e5400efd01b67727982d46acca2f88a1f7ceae"
)
HIGH_PRECISION_PLAN = (
    FULL_CHECKPOINT.parent
    / "groskin_2607_02828_v1_c100_N200_streaming_ldlt_high_precision_plan.json"
)


def _matrix(values):
    return tuple(tuple(Fraction(value) for value in row) for row in values)


def _enclosure(center, radius):
    radius = Fraction(radius)
    return (
        tuple(tuple(value - radius for value in row) for row in center),
        tuple(tuple(value + radius for value in row) for row in center),
    )


def _source_artifact(tmp_path, center, high_radius):
    from experiments.rh import weil_extremal_sharded as sharded

    low_radius = 2 * Fraction(high_radius)
    dimension = len(center)
    assert dimension % 2 == 1
    N = (dimension - 1) // 2
    specifications = {
        ("low", "auxiliary_s_cc_xc"): (*_enclosure(center, low_radius), 384),
        ("low", "ccm_hypergeometric_lerch"): (
            *_enclosure(center, low_radius),
            384,
        ),
        ("high", "auxiliary_s_cc_xc"): (
            *_enclosure(center, high_radius),
            896,
        ),
        ("high", "ccm_hypergeometric_lerch"): (
            *_enclosure(center, high_radius),
            896,
        ),
    }
    manifests = {}
    for (level, route), (lower, upper, precision) in specifications.items():
        output = tmp_path / "source" / "routes" / f"{level}-{route}"
        sharded.write_rational_route_artifact(
            output,
            lower,
            upper,
            c=13,
            N=N,
            prec_bits=precision,
            decimal_enclosure_digits=120,
            python_flint_version="fixture",
            route=route,
            tile_size=2,
        )
        manifests[(level, route)] = output / "manifest.json"
    sharded.write_cross_precision_artifact(
        tmp_path / "source",
        low_auxiliary_manifest=manifests[("low", "auxiliary_s_cc_xc")],
        low_ccm_manifest=manifests[("low", "ccm_hypergeometric_lerch")],
        high_auxiliary_manifest=manifests[("high", "auxiliary_s_cc_xc")],
        high_ccm_manifest=manifests[("high", "ccm_hypergeometric_lerch")],
    )
    return tmp_path / "source" / "manifest.json"


def _high_precision_source_artifact(tmp_path, center):
    from experiments.rh import weil_extremal_high_precision as high_precision

    manifests = {}
    for level, precision, radius in (
        ("low", 384, Fraction(1, 100)),
        ("high", 896, Fraction(1, 1000)),
    ):
        for route in (
            "auxiliary_s_cc_xc",
            "ccm_hypergeometric_lerch",
        ):
            output = tmp_path / "high-precision-source" / "routes" / f"{level}-{route}"

            def bounds_at(i, j, *, route=route, radius=radius):
                value = center[i + 1][j + 1]
                if route == "auxiliary_s_cc_xc":
                    return value - 2 * radius, value + radius
                return value - radius, value + 2 * radius

            high_precision.write_resumable_route_from_accessor(
                output,
                bounds_at,
                c=13,
                N=1,
                prec_bits=precision,
                decimal_enclosure_digits=120,
                python_flint_version="fixture",
                route=route,
                tile_size=2,
                minimum_free_disk_bytes=0,
            )
            manifests[(level, route)] = output / "manifest.json"

    root = tmp_path / "high-precision-source"
    high_precision.write_resumable_cross_artifact(
        root,
        low_auxiliary_manifest=manifests[("low", "auxiliary_s_cc_xc")],
        low_ccm_manifest=manifests[("low", "ccm_hypergeometric_lerch")],
        high_auxiliary_manifest=manifests[("high", "auxiliary_s_cc_xc")],
        high_ccm_manifest=manifests[("high", "ccm_hypergeometric_lerch")],
        minimum_free_disk_bytes=0,
    )
    return root / "manifest.json"


def _rehash(record):
    payload = {key: value for key, value in record.items() if key != "payload_sha256"}
    canonical = json.dumps(
        payload,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
        allow_nan=False,
    )
    record["payload_sha256"] = hashlib.sha256(canonical.encode("ascii")).hexdigest()


def test_streaming_interval_ldlt_certifies_positive_fixture(tmp_path):
    from experiments.rh import weil_extremal_streaming_ldlt as streaming

    source = _source_artifact(
        tmp_path,
        _matrix([[4, 1, 0], [1, 3, "1/2"], [0, "1/2", 2]]),
        Fraction(1, 10000),
    )
    checkpoint_path = tmp_path / "positive.json"
    record = streaming.run_streaming_interval_ldlt(
        source,
        checkpoint_path,
        workspace_dir=tmp_path / "workspace",
        block_size=2,
        arb_prec_bits=896,
        serialization_digits=300,
    )

    assert record["classification"] == "positive"
    assert record["gate_a_status"] == "not_satisfied"
    assert record["result"] == {
        "certified_positive_pivot_count": 3,
        "certified_strict_negative_witness": False,
        "complete_factorization": True,
        "dimension": 3,
        "first_unresolved_pivot": None,
    }
    assert all(Fraction(pivot["lower"]) > 0 for pivot in record["pivots"])
    assert streaming.verify_checkpoint_file(checkpoint_path)
    assert list((tmp_path / "workspace" / "factors").glob("*.json.gz"))


def test_streaming_checkpoint_verifier_accepts_high_precision_source(tmp_path):
    from experiments.rh import weil_extremal_streaming_ldlt as streaming

    source = _high_precision_source_artifact(
        tmp_path,
        _matrix([[8, 1, 0], [1, 7, 1], [0, 1, 6]]),
    )
    checkpoint_path = tmp_path / "high-precision-positive.json"
    record = streaming.run_streaming_interval_ldlt(
        source,
        checkpoint_path,
        workspace_dir=tmp_path / "high-precision-workspace",
        block_size=2,
        arb_prec_bits=896,
        serialization_digits=300,
        intersection_level="high",
    )

    assert record["classification"] == "positive"
    assert streaming.verify_checkpoint_file(checkpoint_path)


def test_streaming_interval_ldlt_records_exact_first_unresolved_pivot(tmp_path):
    from experiments.rh import weil_extremal_streaming_ldlt as streaming

    source = _source_artifact(
        tmp_path,
        _matrix([[4, 0, 0], [0, 3, 0], [0, 0, 0]]),
        Fraction(1, 100),
    )
    checkpoint_path = tmp_path / "unresolved.json"
    record = streaming.run_streaming_interval_ldlt(
        source,
        checkpoint_path,
        workspace_dir=tmp_path / "workspace",
        block_size=2,
        arb_prec_bits=896,
        serialization_digits=300,
    )

    assert record["classification"] == "unresolved"
    assert record["result"]["certified_positive_pivot_count"] == 2
    unresolved = record["result"]["first_unresolved_pivot"]
    assert unresolved["index"] == 2
    assert Fraction(unresolved["lower"]) <= 0 <= Fraction(unresolved["upper"])
    assert record["workspace"]["maximum_loaded_block_entries"] <= 4
    assert streaming.verify_checkpoint_file(checkpoint_path)


def test_streaming_checkpoint_verifier_rejects_rehashed_pivot_tampering(tmp_path):
    from experiments.rh import weil_extremal_streaming_ldlt as streaming

    source = _source_artifact(
        tmp_path,
        _matrix([[4, 0, 0], [0, 3, 0], [0, 0, 0]]),
        Fraction(1, 100),
    )
    checkpoint_path = tmp_path / "unresolved.json"
    streaming.run_streaming_interval_ldlt(
        source,
        checkpoint_path,
        workspace_dir=tmp_path / "workspace",
        block_size=2,
        arb_prec_bits=896,
        serialization_digits=300,
    )
    record = json.loads(checkpoint_path.read_text())
    record["result"]["first_unresolved_pivot"]["lower"] = "1"
    _rehash(record)

    assert not streaming.verify_checkpoint(record, checkpoint_path)


def test_strict_negative_pivot_without_rational_witness_stays_unresolved(tmp_path):
    from experiments.rh import weil_extremal_streaming_ldlt as streaming

    source = _source_artifact(
        tmp_path,
        _matrix([[4, 0, 0], [0, 3, 0], [0, 0, -1]]),
        Fraction(1, 100),
    )
    checkpoint_path = tmp_path / "negative-pivot.json"
    record = streaming.run_streaming_interval_ldlt(
        source,
        checkpoint_path,
        workspace_dir=tmp_path / "workspace",
        block_size=2,
        arb_prec_bits=896,
        serialization_digits=300,
    )

    assert record["classification"] == "unresolved"
    assert record["result"]["certified_strict_negative_witness"] is False
    assert record["result"]["first_unresolved_pivot"]["reason"] == (
        "strict_negative_pivot_without_rational_witness"
    )
    assert streaming.verify_checkpoint_file(checkpoint_path)


def test_streaming_checkpoint_cli_uses_standard_library_only(tmp_path):
    source = _source_artifact(
        tmp_path,
        _matrix([[4, 0, 0], [0, 3, 0], [0, 0, 0]]),
        Fraction(1, 100),
    )
    checkpoint_path = tmp_path / "unresolved.json"
    from experiments.rh import weil_extremal_streaming_ldlt as streaming

    streaming.run_streaming_interval_ldlt(
        source,
        checkpoint_path,
        workspace_dir=tmp_path / "workspace",
        block_size=2,
        arb_prec_bits=896,
        serialization_digits=300,
    )
    result = subprocess.run(
        [
            sys.executable,
            "-S",
            "-m",
            "experiments.rh.weil_extremal_streaming_ldlt",
            "verify-checkpoint",
            str(checkpoint_path),
        ],
        check=True,
        capture_output=True,
        text=True,
    )

    assert result.stdout.strip() == "valid streaming interval LDL checkpoint: true"


def test_streaming_block_updates_cross_three_panels_deterministically(tmp_path):
    from experiments.rh import weil_extremal_streaming_ldlt as streaming

    source = _source_artifact(
        tmp_path,
        _matrix(
            [
                [8, 1, 0, 0, 0],
                [1, 7, 1, 0, 0],
                [0, 1, 6, 1, 0],
                [0, 0, 1, 5, 1],
                [0, 0, 0, 1, 4],
            ]
        ),
        Fraction(1, 100000),
    )
    first = streaming.run_streaming_interval_ldlt(
        source,
        tmp_path / "first.json",
        workspace_dir=tmp_path / "first-workspace",
        block_size=2,
        arb_prec_bits=896,
        serialization_digits=300,
    )
    second = streaming.run_streaming_interval_ldlt(
        source,
        tmp_path / "second.json",
        workspace_dir=tmp_path / "second-workspace",
        block_size=2,
        arb_prec_bits=896,
        serialization_digits=300,
    )

    assert first["classification"] == "positive"
    assert first["pivots"] == second["pivots"]
    assert first["result"] == second["result"]
    assert first["workspace"] == second["workspace"]


def test_streaming_factorizer_can_select_low_intersection(tmp_path):
    from experiments.rh import weil_extremal_streaming_ldlt as streaming

    source = _source_artifact(
        tmp_path,
        _matrix([[4, 1, 0], [1, 3, 0], [0, 0, 2]]),
        Fraction(1, 10000),
    )
    record = streaming.run_streaming_interval_ldlt(
        source,
        tmp_path / "low.json",
        workspace_dir=tmp_path / "low-workspace",
        block_size=2,
        arb_prec_bits=384,
        serialization_digits=140,
        intersection_level="low",
    )

    assert record["classification"] == "positive"
    assert record["parameters"]["intersection_level"] == "low"


def test_streaming_factorizer_resumes_from_completed_panel(tmp_path):
    from experiments.rh import weil_extremal_streaming_ldlt as streaming

    source = _source_artifact(
        tmp_path,
        _matrix(
            [
                [8, 1, 0, 0, 0],
                [1, 7, 1, 0, 0],
                [0, 1, 6, 1, 0],
                [0, 0, 1, 5, 1],
                [0, 0, 0, 1, 4],
            ]
        ),
        Fraction(1, 100000),
    )
    workspace = tmp_path / "resumable-workspace"
    with pytest.raises(streaming.PanelLimitReached):
        streaming.run_streaming_interval_ldlt(
            source,
            tmp_path / "resumed.json",
            workspace_dir=workspace,
            block_size=2,
            arb_prec_bits=896,
            serialization_digits=300,
            max_panels=1,
        )

    resume = json.loads((workspace / "resume.json").read_text())
    assert resume["completed_panels"] == 1
    assert len(resume["pivots"]) == 2
    snapshot = workspace / resume["snapshot_path"]
    assert snapshot.name == f"{resume['payload_sha256']}.json"

    resumed = streaming.run_streaming_interval_ldlt(
        source,
        tmp_path / "resumed.json",
        workspace_dir=workspace,
        block_size=2,
        arb_prec_bits=896,
        serialization_digits=300,
        resume=True,
    )
    fresh = streaming.run_streaming_interval_ldlt(
        source,
        tmp_path / "fresh.json",
        workspace_dir=tmp_path / "fresh-workspace",
        block_size=2,
        arb_prec_bits=896,
        serialization_digits=300,
    )

    assert resumed["classification"] == "positive"
    assert resumed["pivots"] == fresh["pivots"]
    assert resumed["result"] == fresh["result"]


def test_full_896_streaming_checkpoint_is_frozen_and_unresolved():
    source = FULL_CHECKPOINT.read_bytes()
    record = json.loads(source)

    assert hashlib.sha256(source).hexdigest() == FULL_CHECKPOINT_SHA256
    assert record["classification"] == "unresolved"
    assert record["gate_a_status"] == "not_satisfied"
    assert record["result"]["certified_positive_pivot_count"] == 67
    assert record["result"]["certified_strict_negative_witness"] is False
    unresolved = record["result"]["first_unresolved_pivot"]
    assert unresolved["index"] == 67
    assert unresolved["reason"] == "pivot_interval_contains_zero"
    assert Fraction(unresolved["lower"]) < 0 < Fraction(unresolved["upper"])
    assert record["workspace"]["maximum_loaded_block_entries"] == 4096


def test_high_precision_plan_binds_existing_provenance():
    record = json.loads(HIGH_PRECISION_PLAN.read_text())

    assert record["gate_a_status"] == "not_satisfied"
    assert record["pipeline"]["route_generation_current_status"] == (
        "design_only_not_executed"
    )
    assert record["precision"] == {
        "decimal_enclosure_digits": 2900,
        "high_bits": 9512,
        "low_bits": 9000,
        "separation_bits": 512,
    }
    for descriptor in record["provenance"].values():
        if not isinstance(descriptor, dict):
            continue
        path = HIGH_PRECISION_PLAN.parent / descriptor["path"]
        assert hashlib.sha256(path.read_bytes()).hexdigest() == descriptor["sha256"]
