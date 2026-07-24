import json
from fractions import Fraction

import pytest


def _bounds(value):
    value = Fraction(value)
    return value - Fraction(1, 1000), value + Fraction(1, 1000)


def test_prepared_route_entries_match_full_assemblers():
    from experiments.rh import weil_extremal_high_precision as high_precision
    from experiments.rh import weil_extremal_interval_overlap as overlap

    for route, assembler in (
        ("auxiliary_s_cc_xc", overlap.assemble_auxiliary_s_cc_xc),
        (
            "ccm_hypergeometric_lerch",
            overlap.assemble_ccm_hypergeometric_lerch,
        ),
    ):
        prepared = high_precision.prepare_route_evaluator(
            route, c=13, N=1, prec_bits=384
        )
        assembled = assembler(13, 1, 384)
        try:
            for i in range(-1, 2):
                for j in range(-1, 2):
                    assert prepared.entry(i, j).overlaps(assembled[(i, j)])
        finally:
            prepared.close()


def test_route_generation_snapshots_each_tile_and_resumes(tmp_path):
    from experiments.rh import weil_extremal_high_precision as high_precision

    calls = []

    def bounds_at(i, j):
        calls.append((i, j))
        return _bounds(10 * i + j)

    output = tmp_path / "route"
    partial = high_precision.write_resumable_route_from_accessor(
        output,
        bounds_at,
        c=13,
        N=1,
        prec_bits=9000,
        decimal_enclosure_digits=2900,
        python_flint_version="fixture",
        route="auxiliary_s_cc_xc",
        tile_size=2,
        minimum_free_disk_bytes=0,
        max_tiles=1,
    )

    assert partial["result"]["completed_tile_count"] == 1
    assert partial["result"]["complete"] is False
    assert not (output / "manifest.json").exists()
    assert len(list((output / "checkpoints").glob("*.json"))) == 1
    descriptor = partial["chunks"][0]
    assert descriptor["path"] == (
        f"objects/{descriptor['compressed_sha256']}.json.gz"
    )
    first_calls = tuple(calls)

    completed = high_precision.write_resumable_route_from_accessor(
        output,
        bounds_at,
        c=13,
        N=1,
        prec_bits=9000,
        decimal_enclosure_digits=2900,
        python_flint_version="fixture",
        route="auxiliary_s_cc_xc",
        tile_size=2,
        minimum_free_disk_bytes=0,
    )

    assert completed["result"] == {
        "complete": True,
        "completed_tile_count": 4,
        "entry_count": 9,
        "total_tile_count": 4,
    }
    assert tuple(calls[: len(first_calls)]) == first_calls
    assert len(calls) == 9
    assert high_precision.verify_route_checkpoint_file(output / "checkpoint.json")
    assert high_precision.verify_route_checkpoint_file(output / "manifest.json")


def test_route_generation_enforces_free_disk_budget(tmp_path, monkeypatch):
    from experiments.rh import weil_extremal_high_precision as high_precision

    class Usage:
        free = 99

    monkeypatch.setattr(high_precision.shutil, "disk_usage", lambda _path: Usage())
    with pytest.raises(RuntimeError, match="free disk budget"):
        high_precision.write_resumable_route_from_accessor(
            tmp_path / "route",
            lambda i, j: _bounds(i + j),
            c=13,
            N=0,
            prec_bits=9000,
            decimal_enclosure_digits=2900,
            python_flint_version="fixture",
            route="auxiliary_s_cc_xc",
            tile_size=1,
            minimum_free_disk_bytes=100,
        )


def _write_route(high_precision, root, level, route, matrix, precision):
    def bounds_at(i, j):
        lower, upper = (Fraction(value) for value in matrix[i + 1][j + 1])
        if level == "low":
            return lower - 1, upper + 1
        return lower, upper

    return high_precision.write_resumable_route_from_accessor(
        root / "routes" / f"{level}-{route}",
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


def test_cross_generation_is_transpose_aware_and_resumable(tmp_path):
    from experiments.rh import weil_extremal_high_precision as high_precision

    root = tmp_path / "artifact"
    auxiliary = (
        ((3, 5), (0, 2), (0, 2)),
        ((1, 3), (4, 6), (5, 7)),
        ((1, 3), (6, 8), (8, 10)),
    )
    ccm = (
        ((3, 5), (0, 2), (0, 2)),
        ((1, 3), (4, 6), (5, 7)),
        ((1, 3), (6, 8), (8, 10)),
    )
    manifests = {}
    for level, precision in (("low", 384), ("high", 896)):
        for route, matrix in (
            ("auxiliary_s_cc_xc", auxiliary),
            ("ccm_hypergeometric_lerch", ccm),
        ):
            _write_route(
                high_precision, root, level, route, matrix, precision
            )
            manifests[(level, route)] = (
                root / "routes" / f"{level}-{route}" / "manifest.json"
            )

    partial = high_precision.write_resumable_cross_artifact(
        root,
        low_auxiliary_manifest=manifests[("low", "auxiliary_s_cc_xc")],
        low_ccm_manifest=manifests[("low", "ccm_hypergeometric_lerch")],
        high_auxiliary_manifest=manifests[("high", "auxiliary_s_cc_xc")],
        high_ccm_manifest=manifests[("high", "ccm_hypergeometric_lerch")],
        minimum_free_disk_bytes=0,
        max_tiles=1,
    )
    assert partial["result"]["completed_tile_count"] == 1
    assert partial["result"]["complete"] is False

    complete = high_precision.write_resumable_cross_artifact(
        root,
        low_auxiliary_manifest=manifests[("low", "auxiliary_s_cc_xc")],
        low_ccm_manifest=manifests[("low", "ccm_hypergeometric_lerch")],
        high_auxiliary_manifest=manifests[("high", "auxiliary_s_cc_xc")],
        high_ccm_manifest=manifests[("high", "ccm_hypergeometric_lerch")],
        minimum_free_disk_bytes=0,
    )
    assert complete["result"]["complete"] is True
    assert complete["result"]["all_symmetric_intersections_nonempty"] is True
    assert high_precision.verify_cross_checkpoint_file(root / "manifest.json")
    from experiments.rh import weil_extremal_streaming_ldlt as streaming

    source_record, descriptors = streaming._load_source(root / "manifest.json")
    assert source_record["schema_version"] == high_precision.CROSS_SCHEMA
    assert len(descriptors) == 4

    off_diagonal = next(
        item
        for item in complete["chunks"]
        if item["tile"]["row_start"] == 0 and item["tile"]["col_start"] == 2
    )
    record = high_precision.read_compressed_record(
        root / off_diagonal["path"]
    )
    lower = Fraction(record["intersection"]["high"]["lower"][0][0])
    upper = Fraction(record["intersection"]["high"]["upper"][0][0])
    assert lower == 1
    assert upper == 2


def test_high_precision_checkpoint_is_canonical_json(tmp_path):
    from experiments.rh import weil_extremal_high_precision as high_precision

    output = tmp_path / "route"
    record = high_precision.write_resumable_route_from_accessor(
        output,
        lambda i, j: _bounds(1),
        c=13,
        N=0,
        prec_bits=9000,
        decimal_enclosure_digits=2900,
        python_flint_version="fixture",
        route="auxiliary_s_cc_xc",
        tile_size=1,
        minimum_free_disk_bytes=0,
    )
    assert json.loads((output / "manifest.json").read_text()) == record
