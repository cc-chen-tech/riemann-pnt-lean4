from __future__ import annotations

import argparse
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

if __package__ in {None, ""}:
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from experiments.pnt.pnt_experiments import sample_row
from experiments.rh.li_coefficients import ZETA_ZERO_IMAGINARY_PARTS


DEFAULT_X_VALUES: tuple[int, ...] = (10, 100, 1_000, 10_000)
DEFAULT_ZERO_PAIRS = 5
DEFAULT_REPORT_PATH = Path(__file__).resolve().parent / "output" / "explicit_formula_report.md"
REPORT_WARNING = (
    "This is an empirical numerical illustration only, not a proof, and it "
    "does not prove `explicit_formula_von_mangoldt`. The toy truncation "
    "omits pole, trivial-zero, constant, and convergence terms from the "
    "rigorous von Mangoldt explicit formula."
)


@dataclass(frozen=True)
class ExplicitFormulaComparisonRow:
    x: int
    psi_minus_x: float
    truncated_zero_contribution: float
    residual_after_truncation: float
    zero_pairs: int


def _validate_x(x: int | float) -> None:
    if x <= 1:
        raise ValueError("x must be greater than 1 for the zero contribution")


def _selected_ordinates(
    ordinates: Sequence[float],
    zero_pairs: int | None,
) -> Sequence[float]:
    if zero_pairs is None:
        zero_pairs = len(ordinates)
    if zero_pairs < 1 or zero_pairs > len(ordinates):
        raise ValueError(f"zero_pairs must be between 1 and {len(ordinates)}")
    return ordinates[:zero_pairs]


def zeta_zero_pair(ordinate: float) -> tuple[complex, complex]:
    if ordinate <= 0.0:
        raise ValueError("zero ordinates must be positive")

    rho = complex(0.5, ordinate)
    return rho, rho.conjugate()


def zero_term(x: int | float, rho: complex) -> complex:
    _validate_x(x)
    if rho == 0:
        raise ValueError("rho must be nonzero")
    return complex(float(x), 0.0) ** rho / rho


def paired_zero_contribution(
    x: int | float,
    ordinate: float,
    tolerance: float = 1e-10,
) -> float:
    pair_sum = -sum(zero_term(x, rho) for rho in zeta_zero_pair(ordinate))
    if abs(pair_sum.imag) > tolerance:
        raise ArithmeticError(f"paired contribution is not real: {pair_sum.imag!r}")
    return float(pair_sum.real)


def truncated_zero_contribution(
    x: int | float,
    ordinates: Sequence[float] = ZETA_ZERO_IMAGINARY_PARTS,
    zero_pairs: int | None = DEFAULT_ZERO_PAIRS,
) -> float:
    return sum(
        paired_zero_contribution(x, ordinate)
        for ordinate in _selected_ordinates(ordinates, zero_pairs)
    )


def comparison_table(
    x_values: Iterable[int] = DEFAULT_X_VALUES,
    ordinates: Sequence[float] = ZETA_ZERO_IMAGINARY_PARTS,
    zero_pairs: int | None = DEFAULT_ZERO_PAIRS,
) -> list[ExplicitFormulaComparisonRow]:
    selected_ordinates = _selected_ordinates(ordinates, zero_pairs)
    rows: list[ExplicitFormulaComparisonRow] = []
    for x in x_values:
        pnt_row = sample_row(x)
        zero_contribution = truncated_zero_contribution(
            x,
            ordinates=selected_ordinates,
            zero_pairs=len(selected_ordinates),
        )
        rows.append(
            ExplicitFormulaComparisonRow(
                x=x,
                psi_minus_x=pnt_row.psi_error,
                truncated_zero_contribution=zero_contribution,
                residual_after_truncation=pnt_row.psi_error - zero_contribution,
                zero_pairs=len(selected_ordinates),
            )
        )
    return rows


def render_report(
    rows: Sequence[ExplicitFormulaComparisonRow],
    ordinates: Sequence[float] = ZETA_ZERO_IMAGINARY_PARTS,
) -> str:
    used_pairs = rows[0].zero_pairs if rows else 0
    lines = [
        "# Explicit Formula Route Toy Experiment",
        "",
        f"Warning: {REPORT_WARNING}",
        "",
        "The table compares raw `psi(x) - x` values from the existing PNT",
        "experiment code with a finite sum of paired nontrivial-zero terms",
        "`-2*Re(x^rho/rho)` using rho = 1/2 + i*t. It is intended only as a",
        "dependency-mapping aid for the explicit-formula route.",
        "",
        f"- x values sampled: {', '.join(str(row.x) for row in rows)}",
        f"- positive zero ordinates used: {used_pairs}",
        f"- paired nontrivial zeros used: {used_pairs * 2}",
        "",
        "| x | psi(x) - x | truncated zero contribution | residual | zero pairs |",
        "|---:|---:|---:|---:|---:|",
    ]
    for row in rows:
        lines.append(
            "| "
            f"{row.x} | "
            f"{row.psi_minus_x:.12g} | "
            f"{row.truncated_zero_contribution:.12g} | "
            f"{row.residual_after_truncation:.12g} | "
            f"{row.zero_pairs} |"
        )

    lines.extend(
        [
            "",
            "Fixture ordinates used:",
            "",
            *[f"- {ordinate:.15g}" for ordinate in ordinates[:used_pairs]],
            "",
        ]
    )
    return "\n".join(lines)


def write_report(
    output: Path = DEFAULT_REPORT_PATH,
    x_values: Iterable[int] = DEFAULT_X_VALUES,
    ordinates: Sequence[float] = ZETA_ZERO_IMAGINARY_PARTS,
    zero_pairs: int | None = DEFAULT_ZERO_PAIRS,
) -> Path:
    rows = comparison_table(
        x_values=x_values,
        ordinates=ordinates,
        zero_pairs=zero_pairs,
    )
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(render_report(rows, ordinates=ordinates))
    return output


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Generate a toy truncated explicit-formula comparison report."
    )
    parser.add_argument("--x-values", type=int, nargs="+", default=list(DEFAULT_X_VALUES))
    parser.add_argument("--zero-pairs", type=int, default=DEFAULT_ZERO_PAIRS)
    parser.add_argument("--output", type=Path, default=DEFAULT_REPORT_PATH)
    args = parser.parse_args(argv)

    write_report(
        output=args.output,
        x_values=args.x_values,
        ordinates=ZETA_ZERO_IMAGINARY_PARTS,
        zero_pairs=args.zero_pairs,
    )
    print(f"wrote explicit-formula toy report to {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
