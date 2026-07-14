import sys
from pathlib import Path


SCRIPTS = Path(__file__).resolve().parents[1] / "scripts"
sys.path.insert(0, str(SCRIPTS))

import check_axiom_allowlist  # noqa: E402


def test_parse_axiom_report_handles_multiline_axiom_lists():
    output = """
'Example.first' depends on axioms: [propext, Classical.choice,
 Quot.sound]
'Example.second' depends on axioms: [Classical.choice]
"""

    assert check_axiom_allowlist.parse_axiom_report(output) == {
        "Example.first": {"propext", "Classical.choice", "Quot.sound"},
        "Example.second": {"Classical.choice"},
    }


def test_validate_axioms_rejects_missing_declarations_and_unexpected_axioms():
    reports = {
        "Example.first": {"propext", "Classical.choice", "Quot.sound", "Bad.axiom"},
    }

    errors = check_axiom_allowlist.validate_axioms(
        reports,
        expected_declarations={"Example.first", "Example.second"},
        allowed_axioms={"propext", "Classical.choice", "Quot.sound"},
    )

    assert errors == [
        "missing axiom report for Example.second",
        "Example.first uses unexpected axioms: Bad.axiom",
    ]


def test_validate_axioms_accepts_the_standard_lean_allowlist():
    reports = {
        "Example.first": {"propext", "Classical.choice", "Quot.sound"},
        "Example.second": {"Classical.choice"},
    }

    assert check_axiom_allowlist.validate_axioms(
        reports,
        expected_declarations=set(reports),
        allowed_axioms={"propext", "Classical.choice", "Quot.sound"},
    ) == []
