import copy
import gzip
import hashlib
import json
import subprocess
import sys
from fractions import Fraction
from pathlib import Path

import pytest


FULL_ARTIFACT_ROOT = (
    Path(__file__).parents[1]
    / "experiments"
    / "rh"
    / "reference"
    / "groskin_2607_02828_v1_c100_N200_arb_cross_precision_sharded"
)
FULL_MANIFEST_SHA256 = (
    "eabc5fdce5e21a0a69e96f7dd7dffd0b1328833a04f95557fa4529c88b07605d"
)


def _matrix(values):
    return tuple(tuple(Fraction(value) for value in row) for row in values)


def _shift(matrix, amount):
    return tuple(
        tuple(value + Fraction(amount) for value in row) for row in matrix
    )


def _enclosure(center, radius):
    radius = Fraction(radius)
    lower = tuple(tuple(value - radius for value in row) for row in center)
    upper = tuple(tuple(value + radius for value in row) for row in center)
    return lower, upper


def _fixture_routes(tmp_path):
    from experiments.rh import weil_extremal_sharded as sharded

    center = _matrix(
        [
            [4, 1, 0],
            [1, 3, "1/2"],
            [0, "1/2", 2],
        ]
    )
    specifications = {
        ("low", "auxiliary_s_cc_xc"): (*_enclosure(center, "1/4"), 384),
        ("low", "ccm_hypergeometric_lerch"): (
            *_enclosure(_shift(center, "1/100"), "1/4"),
            384,
        ),
        ("high", "auxiliary_s_cc_xc"): (*_enclosure(center, "1/20"), 896),
        ("high", "ccm_hypergeometric_lerch"): (
            *_enclosure(_shift(center, "1/1000"), "1/20"),
            896,
        ),
    }
    manifests = {}
    for (level, route), (lower, upper, prec_bits) in specifications.items():
        output_dir = tmp_path / "routes" / f"{level}-{route}"
        manifest = sharded.write_rational_route_artifact(
            output_dir,
            lower,
            upper,
            c=13,
            N=1,
            prec_bits=prec_bits,
            decimal_enclosure_digits=120,
            python_flint_version="fixture",
            route=route,
            tile_size=2,
        )
        manifests[(level, route)] = output_dir / "manifest.json"
        assert manifest["result"] == {
            "all_intervals_nonempty": True,
            "chunk_count": 4,
            "complete_partition": True,
            "entry_count": 9,
        }
        assert sharded.verify_route_artifact_file(output_dir / "manifest.json")
    return manifests


def _build_fixture_cross(tmp_path):
    from experiments.rh import weil_extremal_sharded as sharded

    manifests = _fixture_routes(tmp_path)
    cross_root = tmp_path
    record = sharded.write_cross_precision_artifact(
        cross_root,
        low_auxiliary_manifest=manifests[("low", "auxiliary_s_cc_xc")],
        low_ccm_manifest=manifests[("low", "ccm_hypergeometric_lerch")],
        high_auxiliary_manifest=manifests[("high", "auxiliary_s_cc_xc")],
        high_ccm_manifest=manifests[("high", "ccm_hypergeometric_lerch")],
    )
    return cross_root, record


def _tree_digest(root):
    digest = hashlib.sha256()
    for path in sorted(path for path in root.rglob("*") if path.is_file()):
        digest.update(str(path.relative_to(root)).encode("ascii"))
        digest.update(b"\0")
        digest.update(path.read_bytes())
    return digest.hexdigest()


def test_sharded_route_and_cross_artifacts_replay_exactly(tmp_path):
    from experiments.rh import weil_extremal_sharded as sharded

    cross_root, record = _build_fixture_cross(tmp_path)

    assert record["schema_version"] == (
        "weil-extremal-kernel-arb-cross-precision-shards/v1"
    )
    assert record["claim_scope"] == "finite-sharded-arb-matrix-only"
    assert record["gate_a_status"] == "not_satisfied"
    assert record["parameters"] == {
        "N": 1,
        "c": 13,
        "decimal_enclosure_digits": 120,
        "dimension": 3,
        "high_prec_bits": 896,
        "index_order": [-1, 0, 1],
        "low_prec_bits": 384,
        "python_flint_version": "fixture",
        "tile_size": 2,
    }
    assert record["result"] == {
        "all_high_route_entries_overlap": True,
        "all_intersection_entries_contained": True,
        "all_intersection_entries_strictly_narrower": True,
        "all_low_route_entries_overlap": True,
        "all_route_entries_contained": True,
        "all_route_entries_strictly_narrower": True,
        "all_symmetric_intersections_nonempty": True,
        "chunk_count": 4,
        "entry_count": 9,
    }
    assert sharded.verify_cross_precision_artifact_file(
        cross_root / "manifest.json"
    )

    first_chunk = cross_root / record["chunks"][0]["path"]
    raw = gzip.decompress(first_chunk.read_bytes())
    chunk = json.loads(raw)
    assert chunk["tile"] == {
        "col_end": 2,
        "col_start": 0,
        "row_end": 2,
        "row_start": 0,
    }
    assert chunk["result"]["entry_count"] == 4
    assert chunk["result"]["all_symmetric_intersections_nonempty"] is True


def test_sharded_artifacts_are_byte_deterministic(tmp_path):
    first_root, _record = _build_fixture_cross(tmp_path / "first")
    second_root, _record = _build_fixture_cross(tmp_path / "second")

    assert _tree_digest(tmp_path / "first") == _tree_digest(tmp_path / "second")
    assert (first_root / "manifest.json").read_bytes() == (
        second_root / "manifest.json"
    ).read_bytes()


def test_sharded_route_verifier_rejects_compressed_chunk_tampering(tmp_path):
    from experiments.rh import weil_extremal_sharded as sharded

    manifests = _fixture_routes(tmp_path)
    manifest_path = manifests[("low", "auxiliary_s_cc_xc")]
    record = json.loads(manifest_path.read_text())
    chunk_path = manifest_path.parent / record["chunks"][0]["path"]
    corrupted = bytearray(chunk_path.read_bytes())
    corrupted[-1] ^= 1
    chunk_path.write_bytes(corrupted)

    assert not sharded.verify_route_artifact_file(manifest_path)


def test_sharded_cross_verifier_rejects_rehashed_count_tampering(tmp_path):
    from experiments.rh import weil_extremal_sharded as sharded

    cross_root, record = _build_fixture_cross(tmp_path)
    record = copy.deepcopy(record)
    record["result"]["entry_count"] = 8
    payload = {key: value for key, value in record.items() if key != "payload_sha256"}
    canonical = json.dumps(
        payload,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
        allow_nan=False,
    )
    record["payload_sha256"] = hashlib.sha256(
        canonical.encode("ascii")
    ).hexdigest()

    assert not sharded.verify_cross_precision_artifact(
        record, cross_root / "manifest.json"
    )


def test_sharded_cross_verifier_rejects_rehashed_chunk_count_tampering(tmp_path):
    from experiments.rh import weil_extremal_sharded as sharded

    cross_root, record = _build_fixture_cross(tmp_path)
    record = copy.deepcopy(record)
    record["chunks"][0]["entry_count"] = 0
    payload = {key: value for key, value in record.items() if key != "payload_sha256"}
    canonical = json.dumps(
        payload,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
        allow_nan=False,
    )
    record["payload_sha256"] = hashlib.sha256(
        canonical.encode("ascii")
    ).hexdigest()

    assert not sharded.verify_cross_precision_artifact(
        record, cross_root / "manifest.json"
    )


def test_sharded_cross_cli_replays_without_site_packages(tmp_path):
    cross_root, _record = _build_fixture_cross(tmp_path)

    result = subprocess.run(
        [
            sys.executable,
            "-S",
            "-m",
            "experiments.rh.weil_extremal_sharded",
            "verify-cross",
            str(cross_root / "manifest.json"),
        ],
        check=True,
        capture_output=True,
        text=True,
    )

    assert result.stdout.strip() == (
        "valid sharded Arb cross-precision artifact: true"
    )


def test_sharded_builder_requires_same_grid_and_512_bit_gap(tmp_path):
    from experiments.rh import weil_extremal_sharded as sharded

    manifests = _fixture_routes(tmp_path)
    high_ccm_path = manifests[("high", "ccm_hypergeometric_lerch")]
    high_ccm = json.loads(high_ccm_path.read_text())
    high_ccm["parameters"]["decimal_enclosure_digits"] = 121
    payload = {
        key: value for key, value in high_ccm.items() if key != "payload_sha256"
    }
    canonical = json.dumps(
        payload,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
        allow_nan=False,
    )
    high_ccm["payload_sha256"] = hashlib.sha256(
        canonical.encode("ascii")
    ).hexdigest()
    high_ccm_path.write_text(
        json.dumps(
            high_ccm,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
            allow_nan=False,
        )
        + "\n"
    )

    with pytest.raises(ValueError, match="canonical and valid"):
        sharded.write_cross_precision_artifact(
            tmp_path / "cross",
            low_auxiliary_manifest=manifests[
                ("low", "auxiliary_s_cc_xc")
            ],
            low_ccm_manifest=manifests[
                ("low", "ccm_hypergeometric_lerch")
            ],
            high_auxiliary_manifest=manifests[
                ("high", "auxiliary_s_cc_xc")
            ],
            high_ccm_manifest=high_ccm_path,
        )


def test_full_size_sharded_manifest_is_frozen():
    manifest_path = FULL_ARTIFACT_ROOT / "manifest.json"
    manifest_bytes = manifest_path.read_bytes()
    record = json.loads(manifest_bytes)

    assert hashlib.sha256(manifest_bytes).hexdigest() == FULL_MANIFEST_SHA256
    assert record["claim_scope"] == "finite-sharded-arb-matrix-only"
    assert record["gate_a_status"] == "not_satisfied"
    assert record["parameters"] == {
        "N": 200,
        "c": 100,
        "decimal_enclosure_digits": 120,
        "dimension": 401,
        "high_prec_bits": 896,
        "index_order": list(range(-200, 201)),
        "low_prec_bits": 384,
        "python_flint_version": "0.8.0",
        "tile_size": 64,
    }
    assert record["result"] == {
        "all_high_route_entries_overlap": True,
        "all_intersection_entries_contained": True,
        "all_intersection_entries_strictly_narrower": True,
        "all_low_route_entries_overlap": True,
        "all_route_entries_contained": True,
        "all_route_entries_strictly_narrower": True,
        "all_symmetric_intersections_nonempty": True,
        "chunk_count": 49,
        "entry_count": 160801,
    }
    assert len(
        [path for path in FULL_ARTIFACT_ROOT.rglob("*") if path.is_file()]
    ) == 250
