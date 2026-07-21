"""Unit tests for the interval overlap / symmetrization merge tool.

The tests use synthetic toy artifacts conforming to schema
``weil-extremal-kernel-interval-assembly/v1``; hashing in the fixtures is
implemented independently of the module under test (json + hashlib with
sort_keys and compact separators) so that a broken digest implementation in
the module cannot make these tests vacuous.
"""

from __future__ import annotations

import hashlib
import json
from decimal import Decimal
from pathlib import Path

import pytest

from experiments.rh import weil_extremal_interval_overlap as overlap


SCHEMA_VERSION = "weil-extremal-kernel-interval-assembly/v1"
INDEX_CONVENTION = "fourier -N..N row-major"


def _digest(payload: dict) -> str:
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def make_artifact(
    entries: list[list[str]],
    *,
    c: int = 13,
    N: int = 1,
    route: str = "route_a",
    prec_bits: int = 256,
) -> dict:
    payload = {
        "schema_version": SCHEMA_VERSION,
        "c": c,
        "N": N,
        "dimension": 2 * N + 1,
        "route": route,
        "prec_bits": prec_bits,
        "index_convention": INDEX_CONVENTION,
        "entries": entries,
        "provenance": {
            "generator": "tests/test_weil_interval_overlap.py",
            "note": "synthetic toy artifact",
            "created_utc": "2026-01-01T00:00:00Z",
        },
    }
    return {**payload, "payload_sha256": _digest(payload)}


def toy_entries(center: str, half_width: str) -> list[list[str]]:
    """Nine identical intervals around ``center`` for the N=1 (3x3) case."""
    mid = Decimal(center)
    half = Decimal(half_width)
    return [[str(mid - half), str(mid + half)] for _ in range(9)]


def write_json(path: Path, record: dict) -> Path:
    canonical = json.dumps(record, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    path.write_bytes((canonical + "\n").encode("utf-8"))
    return path


# ---------------------------------------------------------------------------
# artifact validation
# ---------------------------------------------------------------------------


def test_make_artifact_fixture_passes_validation() -> None:
    record = make_artifact(toy_entries("1.5", "0.5"))
    overlap.validate_artifact(record)
    assert overlap.verify_artifact(record)


def test_tampered_hash_rejected() -> None:
    record = make_artifact(toy_entries("1.5", "0.5"))
    tampered = json.loads(json.dumps(record))
    tampered["entries"][3][0] = "1.01"  # mutate without recomputing the hash
    assert not overlap.verify_artifact(tampered)
    with pytest.raises(overlap.ArtifactError, match="payload_sha256"):
        overlap.validate_artifact(tampered)


def test_tampered_hash_rejected_via_load(tmp_path: Path) -> None:
    record = make_artifact(toy_entries("1.5", "0.5"))
    record["entries"][0][1] = "123"
    path = write_json(tmp_path / "tampered.json", record)
    with pytest.raises(overlap.ArtifactError, match="payload_sha256"):
        overlap.load_artifact(path)


def test_wrong_entry_count_rejected() -> None:
    record = make_artifact(toy_entries("1.5", "0.5")[:8])  # 8 != (2*1+1)^2
    with pytest.raises(overlap.ArtifactError, match="entries"):
        overlap.validate_artifact(record)


def test_inverted_interval_rejected() -> None:
    entries = toy_entries("1.5", "0.5")
    entries[0] = ["2.0", "1.0"]
    record = make_artifact(entries)
    with pytest.raises(overlap.ArtifactError, match="lo > hi"):
        overlap.validate_artifact(record)


# ---------------------------------------------------------------------------
# merge: normal overlap
# ---------------------------------------------------------------------------


def test_merge_normal_overlap() -> None:
    artifact_a = make_artifact(toy_entries("1.5", "0.5"), route="route_a", prec_bits=256)
    artifact_b = make_artifact(toy_entries("1.75", "0.5"), route="route_b", prec_bits=512)
    merged = overlap.merge_artifacts(artifact_a, artifact_b)

    # [1.0, 2.0] ∩ [1.25, 2.25] = [1.25, 2] at every entry
    assert merged["entries"] == [["1.25", "2"]] * 9
    assert merged["route"] == "overlap(route_a|route_b)"
    assert merged["prec_bits"] == 256
    assert merged["c"] == 13
    assert merged["N"] == 1
    assert merged["dimension"] == 3
    assert merged["index_convention"] == INDEX_CONVENTION

    # the merged record is itself a valid artifact (hash verified independently)
    payload = {k: v for k, v in merged.items() if k != "payload_sha256"}
    assert _digest(payload) == merged["payload_sha256"]
    overlap.validate_artifact(merged)

    report = merged["overlap"]
    assert report["routes"] == ["route_a", "route_b"]
    assert report["entry_count"] == 9
    assert len(report["per_entry"]) == 9
    assert report["max_intersection_width"]["width"] == "0.75"
    assert report["tightest_entry"]["width"] == "0.75"
    assert report["symmetrization_narrowed_pairs"] == 0
    for row in report["per_entry"]:
        assert row["intersection_width"] == "0.75"
        assert row["width_route_a"] == "1"
        assert row["width_route_b"] == "1"


def test_merge_rejects_identical_routes() -> None:
    artifact_a = make_artifact(toy_entries("1.5", "0.5"), route="same_route")
    artifact_b = make_artifact(toy_entries("1.5", "0.25"), route="same_route")
    with pytest.raises(overlap.ArtifactError, match="independent routes"):
        overlap.merge_artifacts(artifact_a, artifact_b)


def test_merge_rejects_parameter_mismatch() -> None:
    artifact_a = make_artifact(toy_entries("1.5", "0.5"), route="route_a", N=1)
    artifact_b = make_artifact(
        [["0", "1"]] * 25, route="route_b", N=2  # different N (5x5)
    )
    with pytest.raises(overlap.ArtifactError, match="N mismatch"):
        overlap.merge_artifacts(artifact_a, artifact_b)


# ---------------------------------------------------------------------------
# merge: empty intersection must reject
# ---------------------------------------------------------------------------


def test_empty_intersection_rejected() -> None:
    entries_a = toy_entries("1.5", "0.5")
    entries_b = toy_entries("1.5", "0.5")
    entries_b[4] = ["3.0", "3.5"]  # disjoint from [1.0, 2.0] at center entry (0, 0)
    artifact_a = make_artifact(entries_a, route="route_a")
    artifact_b = make_artifact(entries_b, route="route_b")

    with pytest.raises(overlap.OverlapError) as excinfo:
        overlap.merge_artifacts(artifact_a, artifact_b)
    report = excinfo.value.report
    assert report["kind"] == "route_intersection"
    assert report["entry"] == [0, 0]
    assert report["first_interval"] == ["1", "2"]
    assert report["second_interval"] == ["3", "3.5"]
    assert report["absolute_gap"] == "1"
    # gap 1.0 relative to max(|2.0|, |3.0|) = 3.0
    assert report["relative_gap"][:5] == "0.333"


def test_empty_symmetrization_rejected() -> None:
    # Route A is symmetric and wide; route B certifies disjoint enclosures for
    # the transpose pair (-1, 0) and (0, -1), so symmetrize-by-intersection
    # must fail even though every route-level intersection is nonempty.
    entries_a = toy_entries("1.5", "0.5")  # all [1.0, 2.0]
    entries_b = toy_entries("1.5", "0.5")
    upper = overlap.entry_index(-1, 0, 1)
    lower = overlap.entry_index(0, -1, 1)
    entries_b[upper] = ["1.0", "1.2"]
    entries_b[lower] = ["1.8", "2.0"]
    artifact_a = make_artifact(entries_a, route="route_a")
    artifact_b = make_artifact(entries_b, route="route_b")

    with pytest.raises(overlap.OverlapError) as excinfo:
        overlap.merge_artifacts(artifact_a, artifact_b)
    report = excinfo.value.report
    assert report["kind"] == "symmetrization"
    assert report["entry"] == [-1, 0]
    assert report["absolute_gap"] == "0.6"


# ---------------------------------------------------------------------------
# merge: symmetrization narrows
# ---------------------------------------------------------------------------


def test_symmetrization_narrows() -> None:
    entries_a = toy_entries("1.5", "0.5")  # all [1.0, 2.0]
    entries_b = toy_entries("1.5", "0.5")
    upper = overlap.entry_index(-1, 0, 1)
    lower = overlap.entry_index(0, -1, 1)
    entries_b[upper] = ["1.1", "1.9"]  # route-level merge -> [1.1, 1.9]
    entries_b[lower] = ["1.4", "2.0"]  # route-level merge -> [1.4, 2.0]
    artifact_a = make_artifact(entries_a, route="route_a")
    artifact_b = make_artifact(entries_b, route="route_b")

    merged = overlap.merge_artifacts(artifact_a, artifact_b)
    # symmetrize-by-intersection: [1.1, 1.9] ∩ [1.4, 2.0] = [1.4, 1.9] at both
    assert merged["entries"][upper] == ["1.4", "1.9"]
    assert merged["entries"][lower] == ["1.4", "1.9"]
    assert merged["overlap"]["symmetrization_narrowed_pairs"] == 1
    upper_row = merged["overlap"]["per_entry"][upper]
    assert upper_row["intersection_width"] == "0.5"
    assert upper_row["width_route_b"] == "0.8"


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def test_cli_success(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    path_a = write_json(
        tmp_path / "a.json",
        make_artifact(toy_entries("1.5", "0.5"), route="route_a"),
    )
    path_b = write_json(
        tmp_path / "b.json",
        make_artifact(toy_entries("1.75", "0.5"), route="route_b"),
    )
    out = tmp_path / "merged.json"
    code = overlap.main(["--a", str(path_a), "--b", str(path_b), "--out", str(out)])
    assert code == overlap.EXIT_OK
    summary = json.loads(capsys.readouterr().out)
    assert summary["status"] == "merged"
    assert summary["route"] == "overlap(route_a|route_b)"

    written = json.loads(out.read_bytes())
    overlap.validate_artifact(written)
    assert written["entries"] == [["1.25", "2"]] * 9


def test_cli_empty_overlap_exit_code(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    entries_b = toy_entries("1.5", "0.5")
    entries_b[0] = ["5", "6"]
    path_a = write_json(
        tmp_path / "a.json", make_artifact(toy_entries("1.5", "0.5"), route="route_a")
    )
    path_b = write_json(tmp_path / "b.json", make_artifact(entries_b, route="route_b"))
    out = tmp_path / "merged.json"
    code = overlap.main(["--a", str(path_a), "--b", str(path_b), "--out", str(out)])
    assert code == overlap.EXIT_EMPTY_OVERLAP
    assert not out.exists()
    error = json.loads(capsys.readouterr().err)
    assert error["status"] == "rejected"
    assert error["reason"]["entry"] == [-1, -1]
    assert error["reason"]["relative_gap"] is not None


def test_cli_tampered_input_exit_code(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    record = make_artifact(toy_entries("1.5", "0.5"), route="route_a")
    record["route"] = "route_a_tampered"  # mutate without rehashing
    path_a = write_json(tmp_path / "a.json", record)
    path_b = write_json(
        tmp_path / "b.json",
        make_artifact(toy_entries("1.5", "0.5"), route="route_b"),
    )
    out = tmp_path / "merged.json"
    code = overlap.main(["--a", str(path_a), "--b", str(path_b), "--out", str(out)])
    assert code == overlap.EXIT_INVALID_ARTIFACT
    assert not out.exists()
    error = json.loads(capsys.readouterr().err)
    assert error["status"] == "rejected"
    assert "payload_sha256" in error["reason"]


def test_cli_roundtrip_against_frozen_point_values(tmp_path: Path) -> None:
    """Toy analogue of the hard correctness gate: point values stay enclosed."""
    artifact_a = make_artifact(toy_entries("1.5", "0.5"), route="route_a")
    artifact_b = make_artifact(toy_entries("1.6", "0.45"), route="route_b")
    merged = overlap.merge_artifacts(artifact_a, artifact_b)
    point_value = Decimal("1.5")  # lies in both inputs, hence in the merge
    for lo, hi in merged["entries"]:
        assert Decimal(lo) <= point_value <= Decimal(hi)
