import importlib
import math


def li_module():
    return importlib.import_module("experiments.rh.li_coefficients")


def write_sample_zero_fixture(path):
    path.write_text(
        "\n".join(
            [
                "index,ordinate,source,source_url,note",
                (
                    "1,14.134725141734693,local test fixture,"
                    "https://example.invalid/zeros,"
                    "rounded positive ordinate for empirical truncation tests"
                ),
                (
                    "2,21.022039638771556,local test fixture,"
                    "https://example.invalid/zeros,"
                    "rounded positive ordinate for empirical truncation tests"
                ),
                "",
            ]
        )
    )


def test_paired_zero_contribution_is_real_within_tolerance():
    li = li_module()

    contribution = li.paired_zero_contribution(4, li.ZETA_ZERO_IMAGINARY_PARTS[0])

    assert isinstance(contribution, float)
    direct_pair = sum(
        li.zero_term(4, rho)
        for rho in li.zeta_zero_pair(li.ZETA_ZERO_IMAGINARY_PARTS[0])
    )
    assert math.isclose(contribution, direct_pair.real, rel_tol=0, abs_tol=1e-12)
    assert math.isclose(direct_pair.imag, 0.0, rel_tol=0, abs_tol=1e-12)


def test_load_zero_fixture_csv_keeps_provenance_fields(tmp_path):
    li = li_module()
    fixture_path = tmp_path / "zeros_fixture.csv"
    write_sample_zero_fixture(fixture_path)

    fixture = li.load_zero_fixture(fixture_path)

    assert fixture.ordinates == (14.134725141734693, 21.022039638771556)
    assert fixture.records[0].index == 1
    assert fixture.records[0].source == "local test fixture"
    assert fixture.records[0].source_url == "https://example.invalid/zeros"
    assert "empirical truncation tests" in fixture.records[0].note
    assert fixture.provenance_notes == (
        (
            "local test fixture; https://example.invalid/zeros; "
            "rounded positive ordinate for empirical truncation tests"
        ),
    )


def test_first_fixture_li_coefficients_are_positive():
    li = li_module()

    coefficients = [li.li_coefficient_approximation(n) for n in range(1, 8)]

    assert all(isinstance(value, float) for value in coefficients)
    assert all(value > 0.0 for value in coefficients)


def test_cli_writes_report_with_empirical_warning(tmp_path):
    li = li_module()
    output = tmp_path / "li_coefficients_report.md"

    exit_code = li.main(["--n-max", "3", "--output", str(output)])

    report = output.read_text()
    assert exit_code == 0
    assert "# Truncated Li Coefficient Experiment" in report
    assert "empirical/truncated" in report
    assert "not a proof" in report
    assert "| n | truncated lambda_n | sign |" in report
    assert "| 3 |" in report


def test_truncation_sensitivity_table_tracks_cutoff_changes():
    li = li_module()

    rows = li.truncation_sensitivity_table(n_values=[1, 3], zero_pair_counts=[1, 2, 5])

    assert [row.n for row in rows] == [1, 1, 1, 3, 3, 3]
    assert [row.zero_pairs for row in rows[:3]] == [1, 2, 5]
    assert all(row.value > 0.0 for row in rows)
    assert rows[2].delta_from_previous_cutoff is not None
    assert rows[2].delta_from_previous_cutoff > 0.0


def test_csv_exports_include_headers_and_empirical_warning(tmp_path):
    li = li_module()
    coefficients_csv = tmp_path / "li_coefficients.csv"
    sensitivity_csv = tmp_path / "li_truncation_sensitivity.csv"
    coefficient_rows = li.li_coefficient_table(
        n_max=2,
        ordinates=li.ZETA_ZERO_IMAGINARY_PARTS[:2],
    )
    sensitivity_rows = li.truncation_sensitivity_table(
        n_values=[1, 2],
        zero_pair_counts=[1, 2],
        ordinates=li.ZETA_ZERO_IMAGINARY_PARTS[:2],
    )

    li.write_li_coefficient_csv(
        coefficients_csv,
        coefficient_rows,
        zero_pair_count=2,
    )
    li.write_truncation_sensitivity_csv(sensitivity_csv, sensitivity_rows)

    coefficient_export = coefficients_csv.read_text()
    sensitivity_export = sensitivity_csv.read_text()
    assert coefficient_export.splitlines()[0] == (
        "n,truncated_lambda_n,sign,positive_zero_pairs,"
        "paired_nontrivial_zeros,empirical_note"
    )
    assert "not a proof of the Riemann Hypothesis" in coefficient_export
    assert "| n |" not in coefficient_export
    assert sensitivity_export.splitlines()[0] == (
        "n,zero_pairs,truncated_lambda_n,delta_from_previous_cutoff,"
        "empirical_note"
    )
    assert "empirical/truncated" in sensitivity_export


def test_report_includes_truncation_sensitivity_section(tmp_path):
    li = li_module()
    output = tmp_path / "li_coefficients_report.md"

    li.write_report(output=output, n_max=4, zero_pairs=5, sensitivity_cutoffs=[1, 2, 5])

    report = output.read_text()
    assert "## Truncation Sensitivity" in report
    assert "| n | zero pairs | truncated lambda_n | delta from previous cutoff |" in report
    assert "finite cutoff" in report


def test_cli_loads_zero_fixture_and_writes_csv_exports(tmp_path, capsys):
    li = li_module()
    fixture_path = tmp_path / "zeros_fixture.csv"
    write_sample_zero_fixture(fixture_path)
    report_path = tmp_path / "li_coefficients_report.md"
    coefficients_csv = tmp_path / "li_coefficients.csv"
    sensitivity_csv = tmp_path / "li_truncation_sensitivity.csv"

    exit_code = li.main(
        [
            "--zeros",
            str(fixture_path),
            "--n-max",
            "2",
            "--zero-pairs",
            "2",
            "--sensitivity-cutoffs",
            "1",
            "2",
            "--output",
            str(report_path),
            "--coefficients-csv",
            str(coefficients_csv),
            "--sensitivity-csv",
            str(sensitivity_csv),
        ]
    )

    stdout = capsys.readouterr().out
    report = report_path.read_text()
    assert exit_code == 0
    assert "wrote truncated Li coefficient report" in stdout
    assert "wrote Li coefficient CSV" in stdout
    assert "wrote truncation sensitivity CSV" in stdout
    assert "## Fixture Provenance" in report
    assert "local test fixture" in report
    assert coefficients_csv.exists()
    assert sensitivity_csv.exists()


def test_cli_with_short_fixture_uses_valid_default_sensitivity_cutoffs(tmp_path):
    li = li_module()
    fixture_path = tmp_path / "zeros_fixture.csv"
    write_sample_zero_fixture(fixture_path)
    report_path = tmp_path / "li_coefficients_report.md"
    coefficients_csv = tmp_path / "li_coefficients.csv"
    sensitivity_csv = tmp_path / "li_truncation_sensitivity.csv"

    exit_code = li.main(
        [
            "--zeros",
            str(fixture_path),
            "--n-max",
            "2",
            "--output",
            str(report_path),
            "--coefficients-csv",
            str(coefficients_csv),
            "--sensitivity-csv",
            str(sensitivity_csv),
        ]
    )

    sensitivity_export = sensitivity_csv.read_text()
    assert exit_code == 0
    assert ",1," in sensitivity_export
    assert ",2," in sensitivity_export
    assert ",5," not in sensitivity_export
