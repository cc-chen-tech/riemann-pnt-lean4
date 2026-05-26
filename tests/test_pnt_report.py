from pathlib import Path

from experiments.pnt import report
from experiments.pnt.pnt_experiments import PNTSample


def make_row(x: int, psi_error: float, pi_minus_li: float) -> PNTSample:
    return PNTSample(
        x=x,
        pi_x=0,
        theta_x=0.0,
        psi_x=x + psi_error,
        li_x=-pi_minus_li,
        psi_error=psi_error,
        pi_minus_li=pi_minus_li,
    )


def test_summary_reports_extrema_and_psi_error_sign_changes_in_row_order():
    rows = [
        make_row(10, -3.0, 1.5),
        make_row(20, -1.0, -4.0),
        make_row(30, 2.5, 0.0),
        make_row(40, -0.5, 6.0),
    ]

    summary = report.summarize_rows(rows)

    assert summary.row_count == 4
    assert summary.x_min == 10
    assert summary.x_max == 40
    assert summary.min_psi_error == (10, -3.0)
    assert summary.max_psi_error == (30, 2.5)
    assert summary.min_pi_minus_li == (20, -4.0)
    assert summary.max_pi_minus_li == (40, 6.0)
    assert summary.psi_error_sign_changes == 2


def test_write_report_generates_empirical_markdown_file(tmp_path: Path):
    rows = [
        make_row(10, -3.0, 1.5),
        make_row(20, 1.0, -4.0),
    ]
    output = tmp_path / "pnt_report.md"

    report.write_report(rows, output)

    contents = output.read_text()
    assert contents.startswith("# Prime Number Theorem Numerical Experiment Report")
    assert "empirical numerical data" in contents
    assert "not a proof" in contents
    assert "- Row count: 2" in contents
    assert "- x range: 10 to 20" in contents
    assert "- psi_error sign changes: 1" in contents
