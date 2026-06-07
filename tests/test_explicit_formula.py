import importlib
import math
import subprocess
import sys
from pathlib import Path

from experiments.pnt.pnt_experiments import sample_row


def explicit_formula_module():
    return importlib.import_module("experiments.rh.explicit_formula")


def test_paired_zero_contribution_is_real_and_matches_conjugate_sum():
    explicit = explicit_formula_module()
    x = 100
    ordinate = explicit.ZETA_ZERO_IMAGINARY_PARTS[0]

    contribution = explicit.paired_zero_contribution(x, ordinate)

    rho, conjugate = explicit.zeta_zero_pair(ordinate)
    direct_pair = -(
        explicit.zero_term(x, rho)
        + explicit.zero_term(x, conjugate)
    )

    assert isinstance(contribution, float)
    assert math.isclose(direct_pair.imag, 0.0, rel_tol=0, abs_tol=1e-10)
    assert math.isclose(contribution, direct_pair.real, rel_tol=0, abs_tol=1e-10)
    assert math.isclose(
        contribution,
        -2.0 * explicit.zero_term(x, rho).real,
        rel_tol=0,
        abs_tol=1e-10,
    )


def test_comparison_table_uses_raw_psi_error_and_truncated_zero_terms():
    explicit = explicit_formula_module()
    x_values = [10, 100]

    rows = explicit.comparison_table(x_values=x_values, zero_pairs=2)

    assert [row.x for row in rows] == x_values
    assert all(isinstance(row.truncated_zero_contribution, float) for row in rows)
    assert rows[0].zero_pairs == 2
    assert math.isclose(
        rows[0].psi_minus_x,
        sample_row(10).psi_error,
        rel_tol=0,
        abs_tol=1e-12,
    )
    assert math.isclose(
        rows[0].residual_after_truncation,
        rows[0].psi_minus_x - rows[0].truncated_zero_contribution,
        rel_tol=0,
        abs_tol=1e-12,
    )


def test_report_generation_contains_warning_language_and_table(tmp_path: Path):
    explicit = explicit_formula_module()
    output = tmp_path / "explicit_formula_report.md"

    exit_code = explicit.main(
        [
            "--x-values",
            "10",
            "100",
            "--zero-pairs",
            "2",
            "--output",
            str(output),
        ]
    )

    report = output.read_text()
    assert exit_code == 0
    assert report.startswith("# Explicit Formula Route Toy Experiment")
    assert "empirical" in report
    assert "numerical illustration" in report
    assert "not a proof" in report
    assert "does not prove `explicit_formula_von_mangoldt`" in report
    assert "omits pole, trivial-zero, constant, and convergence terms" in report
    assert "| x | psi(x) - x | truncated zero contribution | residual | zero pairs |" in report
    assert "| 10 |" in report


def test_script_path_execution_writes_report(tmp_path: Path):
    repo_root = Path(__file__).resolve().parents[1]
    script = repo_root / "experiments" / "rh" / "explicit_formula.py"
    output = tmp_path / "explicit_formula_report.md"

    result = subprocess.run(
        [
            sys.executable,
            str(script),
            "--x-values",
            "10",
            "--zero-pairs",
            "1",
            "--output",
            str(output),
        ],
        cwd=repo_root,
        text=True,
        capture_output=True,
        check=False,
    )

    assert result.returncode == 0, result.stderr
    assert output.exists()
    assert "wrote explicit-formula toy report" in result.stdout
