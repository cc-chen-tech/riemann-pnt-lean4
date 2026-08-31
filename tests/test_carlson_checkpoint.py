"""Audit behavior: missing reports and any nonstandard axiom must fail closed."""

import json
import sys
import subprocess
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from check_carlson_checkpoint import audit_traces
import check_carlson_checkpoint as checkpoint


def write_fixture(root, source, messages):
    source_path = root / "Test" / "Example.lean"
    source_path.parent.mkdir(parents=True, exist_ok=True)
    source_path.write_text(source)
    trace = root / ".lake/build/lib/lean/Test/Example.trace"
    trace.parent.mkdir(parents=True, exist_ok=True)
    trace.write_text(json.dumps({"log": [{"message": m} for m in messages]}))


def test_accepts_real_trace_shape_and_counts_distinct_declarations(tmp_path):
    write_fixture(tmp_path, "#print axioms Example.bound\n", [
        "'Example.bound' depends on axioms: [propext, Classical.choice, Quot.sound]",
    ])
    result = audit_traces(tmp_path, ["Test.Example"])
    assert result["errors"] == []
    assert result["reports"] == result["unique_declarations"] == 1
    assert result["observed"] == ["Classical.choice", "Quot.sound", "propext"]


@pytest.mark.parametrize("include_multiline_report", [False, True])
def test_multiline_print_is_required_even_when_another_report_exists(tmp_path, include_multiline_report):
    messages = ["'Example.bound' depends on axioms: [propext]"]
    if include_multiline_report:
        messages.append("'Example.bound'' depends on axioms: [propext, Classical.choice, Quot.sound]")
    write_fixture(tmp_path, "#print axioms Example.bound\n#print axioms\n  Example.bound'\n", messages)
    result = audit_traces(tmp_path, ["Test.Example"])
    if include_multiline_report:
        assert result["errors"] == []
        assert result["reports"] == result["unique_declarations"] == 2
    else:
        assert any("missing axiom report for Example.bound'" in error for error in result["errors"])


@pytest.mark.parametrize("messages, fragment", [
    ([], "missing axiom report"),
    (["'Example.bound' depends on axioms: [sorryAx]"], "sorryAx"),
    (["'Example.bound' depends on axioms: [propext]",
      "'Example.unexpected' depends on axioms: [Bad.gate]"], "Bad.gate"),
    (["'Example.bound' depends on axioms: [Bad.gate]",
      "'Example.bound' depends on axioms: [propext]"], "Bad.gate"),
])
def test_rejects_missing_or_unsafe_reports_including_unrequested_ones(tmp_path, messages, fragment):
    write_fixture(tmp_path, "#print axioms Example.bound\n", messages)
    result = audit_traces(tmp_path, ["Test.Example"])
    assert any(fragment in error for error in result["errors"])


def test_missing_trace_cannot_count_as_a_successful_audit(tmp_path):
    result = audit_traces(tmp_path, ["Test.Example"])
    assert result["errors"]


def test_empty_target_list_cannot_count_as_a_successful_audit(tmp_path):
    assert audit_traces(tmp_path, [])["errors"]


@pytest.mark.parametrize("mutation", ["drop", "duplicate", "replace"])
def test_frozen_manifest_rejects_scope_reduction_and_same_length_substitution(tmp_path, mutation):
    manifest = json.loads((checkpoint.ROOT / checkpoint.MANIFEST).read_text())
    targets = manifest["lean"]["targets"]
    if mutation == "drop":
        targets.pop()
    elif mutation == "duplicate":
        targets[-1] = targets[0]
    else:
        targets[-1] = "Test.UnrelatedContract"
    path = tmp_path / checkpoint.MANIFEST
    path.parent.mkdir(parents=True)
    path.write_text(json.dumps(manifest))
    with pytest.raises(ValueError, match="frozen"):
        checkpoint.load_targets(tmp_path)


def test_fingerprint_detects_manifest_change_during_verification(tmp_path):
    subprocess.run(["git", "init", "-q", str(tmp_path)], check=True)
    path = tmp_path / checkpoint.MANIFEST
    path.parent.mkdir(parents=True)
    path.write_text('{"lean": {"targets": []}}')
    before = checkpoint.source_fingerprint(tmp_path)
    path.write_text('{"lean": {"targets": ["Test.UnrelatedContract"]}}')
    assert checkpoint.source_fingerprint(tmp_path) != before
