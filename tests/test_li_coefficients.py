import importlib
import math


def li_module():
    return importlib.import_module("experiments.rh.li_coefficients")


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


def test_report_includes_truncation_sensitivity_section(tmp_path):
    li = li_module()
    output = tmp_path / "li_coefficients_report.md"

    li.write_report(output=output, n_max=4, zero_pairs=5, sensitivity_cutoffs=[1, 2, 5])

    report = output.read_text()
    assert "## Truncation Sensitivity" in report
    assert "| n | zero pairs | truncated lambda_n | delta from previous cutoff |" in report
    assert "finite cutoff" in report
