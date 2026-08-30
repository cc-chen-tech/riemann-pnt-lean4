import importlib.util
import json
import sys
from pathlib import Path


SCRIPTS = Path(__file__).resolve().parents[1] / "scripts"
ROOT = SCRIPTS.parent
sys.path.insert(0, str(SCRIPTS))

SPEC = importlib.util.spec_from_file_location(
    "update_target_status", SCRIPTS / "update-target-status.py"
)
assert SPEC is not None and SPEC.loader is not None
update_target_status = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(update_target_status)


def test_selberg_target_reports_native_mainline_proof():
    status = update_target_status.build_status()
    selberg = next(
        item
        for entries in status["remaining_prop_targets"].values()
        for item in entries
        if item["qualified_name"]
        == "HardyTheorem.selberg_odd_zero_proportion_target"
    )

    assert selberg["proved_by"] == (
        "HardyTheorem.selberg_odd_zero_proportion_target_proved_mainline"
    )
    assert selberg["independently_closed_by_zeta23_bridge"] is True


def test_critical_line_summary_distinguishes_native_selberg_from_conrey_gap():
    status = update_target_status.build_status()
    summary = next(
        item
        for item in status["chain_summary"]
        if item["name"] == "Quantitative critical-line extensions"
    )

    assert "native Selberg" in summary["status"]
    assert "Conrey's genuine strict two-fifths" in summary["status"]


def test_committed_status_matches_generator_semantically():
    generated = update_target_status.build_status()
    committed = json.loads(
        (ROOT / "docs" / "current-target-status.json").read_text(encoding="utf-8")
    )

    generated.pop("timestamp")
    committed.pop("timestamp")
    assert committed == generated


def test_native_legacy_alias_and_genuine_conrey_boundary():
    status = update_target_status.build_status()
    targets = {
        item["qualified_name"]: item
        for entries in status["remaining_prop_targets"].values()
        for item in entries
    }

    legacy = targets[
        "KnownResults.conrey_40_percent_zeros_on_critical_line_target"
    ]
    assert legacy["proved_by"] == (
        "HardyTheorem.selberg_zero_proportion_target_proved_mainline + "
        "KnownResults.conrey_40_percent_zeros_on_critical_line_target_of_selberg"
    )
    assert legacy["independently_closed_by_zeta23_bridge"] is True

    genuine = targets["HardyTheorem.conreyTwoFifthsSimpleZerosTarget"]
    assert "proved_by" not in genuine
    assert "independently_closed_by_zeta23_bridge" not in genuine


def test_native_endpoint_contracts_are_default_lake_roots():
    lakefile = (ROOT / "lakefile.lean").read_text(encoding="utf-8")
    assert "`Test.SelbergStrictCancellationZeroCoverContract" in lakefile
    assert "`Test.ExponentialPolynomialFirstMomentContract" in lakefile
