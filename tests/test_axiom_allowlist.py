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


def test_parse_axiom_report_handles_lean_names_ending_in_prime():
    output = """
'Example.bound\'' depends on axioms: [propext, Classical.choice, Quot.sound]
"""

    assert check_axiom_allowlist.parse_axiom_report(output) == {
        "Example.bound'": {"propext", "Classical.choice", "Quot.sound"},
    }


def test_parse_axiom_report_handles_declarations_without_axioms():
    output = "'Example.unconditional' does not depend on any axioms"

    assert check_axiom_allowlist.parse_axiom_report(output) == {
        "Example.unconditional": set(),
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


def test_validate_axioms_rejects_bad_axioms_outside_selected_expectations():
    errors = check_axiom_allowlist.validate_axioms(
        {"HardyTheorem.unlisted": {"Bad.mock_axiom"}},
        expected_declarations=set(),
        allowed_axioms=check_axiom_allowlist.ALLOWED_AXIOMS,
    )

    assert errors == [
        "HardyTheorem.unlisted uses unexpected axioms: Bad.mock_axiom"
    ]


def test_validate_axioms_requires_each_conrey_print_report():
    reports = {
        "HardyTheorem.first": {"propext"},
        "HardyTheorem.second": {"Classical.choice"},
    }

    assert check_axiom_allowlist.validate_axioms(
        reports,
        expected_declarations=set(),
        allowed_axioms=check_axiom_allowlist.ALLOWED_AXIOMS,
        required_printed_declarations={"first", "second"},
    ) == []
    assert check_axiom_allowlist.validate_axioms(
        {"HardyTheorem.first": {"propext"}},
        expected_declarations=set(),
        allowed_axioms=check_axiom_allowlist.ALLOWED_AXIOMS,
        required_printed_declarations={"first", "second"},
    ) == ["missing Conrey axiom report for second"]


def test_carlson_unconditional_density_and_forcing_are_audited():
    assert "Test.CarlsonTwoThirdsImprovementAxiomAudit" in check_axiom_allowlist.AXIOM_AUDIT_MODULES
    required = {
        "PrimeNumberTheorem.carlson_halfRange_closed_zeroDensity_isBigO",
        "PrimeNumberTheorem.carlson_halfRange_zeroDensity_isBigO",
        "PrimeNumberTheorem.exists_carlson_halfRange_densityCertificate",
        "PrimeNumberTheorem.singleLayerForcing_halfRange_contradiction",
        "PrimeNumberTheorem.no_nontrivial_zero_re_gt_14_over_17_of_forcing_halfRange",
        "PrimeNumberTheorem.no_nontrivial_zero_re_ge_14_over_17_of_seed_forcing_halfRange",
    }
    assert required <= check_axiom_allowlist.EXPECTED_DECLARATIONS


def test_conrey_local_contracts_are_continuously_audited():
    modules = {
        "Test.ConreyV1HalfMeanSquareContract",
        "Test.ConreyLocalSimpleZeroWitnessContract",
    }
    declarations = {
        "HardyTheorem.conreyMollifiedV1_half_meanSquare_le_V_and_zeta",
        "HardyTheorem.exists_conrey_local_simpleZero_finset_lower_bound_meanSquare",
    }

    assert modules <= set(check_axiom_allowlist.AXIOM_AUDIT_MODULES)
    assert declarations <= check_axiom_allowlist.EXPECTED_DECLARATIONS

    standard_reports = {
        declaration: {"propext", "Classical.choice", "Quot.sound"}
        for declaration in declarations
    }
    assert check_axiom_allowlist.validate_axioms(
        standard_reports,
        expected_declarations=declarations,
        allowed_axioms=check_axiom_allowlist.ALLOWED_AXIOMS,
    ) == []

    bad_reports = dict(standard_reports)
    bad_reports[
        "HardyTheorem.conreyMollifiedV1_half_meanSquare_le_V_and_zeta"
    ] = {"Bad.mock_axiom"}
    assert check_axiom_allowlist.validate_axioms(
        bad_reports,
        expected_declarations=declarations,
        allowed_axioms=check_axiom_allowlist.ALLOWED_AXIOMS,
    ) == [
        "HardyTheorem.conreyMollifiedV1_half_meanSquare_le_V_and_zeta "
        "uses unexpected axioms: Bad.mock_axiom"
    ]


def test_all_conrey_contract_axiom_prints_are_continuously_audited():
    named_modules = {
        ".".join(path.relative_to(check_axiom_allowlist.ROOT).with_suffix("").parts)
        for path in check_axiom_allowlist.ROOT.glob("Test/Conrey*Contract.lean")
        if "#print axioms" in path.read_text(encoding="utf-8")
    }
    stack_modules = set(check_axiom_allowlist.CONREY_STACK_AXIOM_AUDIT_MODULES)
    expected_modules = named_modules | stack_modules

    assert expected_modules == set(check_axiom_allowlist.CONREY_AXIOM_AUDIT_MODULES)
    assert expected_modules <= set(check_axiom_allowlist.AXIOM_AUDIT_MODULES)
    assert len(stack_modules) == 45
    assert all(
        path.is_file()
        for path in check_axiom_allowlist.CONREY_STACK_AXIOM_AUDIT_PATHS
    )
    expected_prints = [
        declaration
        for path in check_axiom_allowlist.CONREY_AXIOM_AUDIT_PATHS
        for declaration in check_axiom_allowlist.re.findall(
            r"#print\s+axioms\s+([A-Za-z0-9_'.]+)",
            path.read_text(encoding="utf-8"),
        )
    ]
    assert expected_prints == check_axiom_allowlist.CONREY_PRINTED_DECLARATIONS
