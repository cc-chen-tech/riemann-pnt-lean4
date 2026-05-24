from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence


ZETA_ZERO_IMAGINARY_PARTS: tuple[float, ...] = (
    14.134725141734693,
    21.022039638771556,
    25.01085758014569,
    30.424876125859512,
    32.93506158773919,
    37.58617815882567,
    40.9187190121475,
    43.32707328091499,
    48.00515088116716,
    49.7738324776723,
)

DEFAULT_REPORT_PATH = Path(__file__).resolve().parent / "output" / "li_coefficients_report.md"
REPORT_WARNING = (
    "These values are empirical/truncated finite zero-sum approximations "
    "and are not a proof of the Riemann Hypothesis."
)


@dataclass(frozen=True)
class LiCoefficientApproximation:
    n: int
    value: float

    @property
    def sign(self) -> str:
        if self.value > 0.0:
            return "positive"
        if self.value < 0.0:
            return "negative"
        return "zero"


@dataclass(frozen=True)
class TruncationSensitivityRow:
    n: int
    zero_pairs: int
    value: float
    delta_from_previous_cutoff: float | None


def _validate_n(n: int) -> None:
    if n < 1:
        raise ValueError("Li coefficient index n must be at least 1")


def zeta_zero_pair(ordinate: float) -> tuple[complex, complex]:
    if ordinate <= 0.0:
        raise ValueError("zero ordinates must be positive")

    rho = complex(0.5, ordinate)
    return rho, rho.conjugate()


def zero_term(n: int, rho: complex) -> complex:
    _validate_n(n)
    return 1.0 - (1.0 - 1.0 / rho) ** n


def paired_zero_contribution(n: int, ordinate: float, tolerance: float = 1e-12) -> float:
    pair_sum = sum(zero_term(n, rho) for rho in zeta_zero_pair(ordinate))
    if abs(pair_sum.imag) > tolerance:
        raise ArithmeticError(
            f"paired contribution has non-real residue {pair_sum.imag!r}"
        )
    return float(pair_sum.real)


def li_coefficient_approximation(
    n: int,
    ordinates: Iterable[float] = ZETA_ZERO_IMAGINARY_PARTS,
) -> float:
    _validate_n(n)
    return sum(paired_zero_contribution(n, ordinate) for ordinate in ordinates)


def li_coefficient_table(
    n_max: int = 10,
    ordinates: Sequence[float] = ZETA_ZERO_IMAGINARY_PARTS,
) -> list[LiCoefficientApproximation]:
    _validate_n(n_max)
    return [
        LiCoefficientApproximation(n=n, value=li_coefficient_approximation(n, ordinates))
        for n in range(1, n_max + 1)
    ]


def truncation_sensitivity_table(
    n_values: Sequence[int],
    zero_pair_counts: Sequence[int],
    ordinates: Sequence[float] = ZETA_ZERO_IMAGINARY_PARTS,
) -> list[TruncationSensitivityRow]:
    if not n_values:
        raise ValueError("n_values must not be empty")
    if not zero_pair_counts:
        raise ValueError("zero_pair_counts must not be empty")

    normalized_cutoffs = sorted(set(zero_pair_counts))
    for n in n_values:
        _validate_n(n)
    for cutoff in normalized_cutoffs:
        if cutoff < 1 or cutoff > len(ordinates):
            raise ValueError(f"zero pair cutoff must be between 1 and {len(ordinates)}")

    rows: list[TruncationSensitivityRow] = []
    for n in sorted(n_values):
        previous_value: float | None = None
        for cutoff in normalized_cutoffs:
            value = li_coefficient_approximation(n, ordinates[:cutoff])
            delta = None if previous_value is None else value - previous_value
            rows.append(
                TruncationSensitivityRow(
                    n=n,
                    zero_pairs=cutoff,
                    value=value,
                    delta_from_previous_cutoff=delta,
                )
            )
            previous_value = value
    return rows


def render_report(
    rows: Sequence[LiCoefficientApproximation],
    ordinates: Sequence[float],
    sensitivity_rows: Sequence[TruncationSensitivityRow] = (),
) -> str:
    positive_pair_count = len(ordinates)
    zero_count = positive_pair_count * 2

    lines = [
        "# Truncated Li Coefficient Experiment",
        "",
        f"Warning: {REPORT_WARNING}",
        "",
        "This report uses a fixed fixture of early zeta-zero ordinates and pairs",
        "them as rho = 1/2 +/- i*t. The zero-sum is finite, so every value below",
        "is empirical/truncated and should only be used as numerical evidence.",
        "",
        f"- positive ordinates used: {positive_pair_count}",
        f"- paired nontrivial zeros used: {zero_count}",
        f"- n range: 1..{rows[-1].n if rows else 0}",
        "",
        "| n | truncated lambda_n | sign |",
        "|---:|---:|:---|",
    ]
    for row in rows:
        lines.append(f"| {row.n} | {row.value:.12g} | {row.sign} |")

    if sensitivity_rows:
        lines.extend(
            [
                "",
                "## Truncation Sensitivity",
                "",
                "This table varies the finite cutoff. It shows sensitivity to the",
                "number of zero pairs included, not convergence of the full Li",
                "coefficient series.",
                "",
                "| n | zero pairs | truncated lambda_n | delta from previous cutoff |",
                "|---:|---:|---:|---:|",
            ]
        )
        for row in sensitivity_rows:
            delta = (
                "n/a"
                if row.delta_from_previous_cutoff is None
                else f"{row.delta_from_previous_cutoff:.12g}"
            )
            lines.append(f"| {row.n} | {row.zero_pairs} | {row.value:.12g} | {delta} |")

    lines.extend(
        [
            "",
            "Fixture ordinates:",
            "",
            *[f"- {ordinate:.15g}" for ordinate in ordinates],
            "",
        ]
    )
    return "\n".join(lines)


def write_report(
    output: Path = DEFAULT_REPORT_PATH,
    n_max: int = 10,
    ordinates: Sequence[float] = ZETA_ZERO_IMAGINARY_PARTS,
    zero_pairs: int | None = None,
    sensitivity_cutoffs: Sequence[int] = (),
) -> Path:
    selected_ordinates = ordinates[:zero_pairs] if zero_pairs is not None else ordinates
    rows = li_coefficient_table(n_max=n_max, ordinates=selected_ordinates)
    sensitivity_rows = (
        truncation_sensitivity_table(
            n_values=range(1, n_max + 1),
            zero_pair_counts=sensitivity_cutoffs,
            ordinates=ordinates,
        )
        if sensitivity_cutoffs
        else []
    )
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(render_report(rows, selected_ordinates, sensitivity_rows))
    return output


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Generate a truncated Li coefficient experiment report."
    )
    parser.add_argument("--n-max", type=int, default=10)
    parser.add_argument("--zero-pairs", type=int, default=len(ZETA_ZERO_IMAGINARY_PARTS))
    parser.add_argument(
        "--sensitivity-cutoffs",
        type=int,
        nargs="*",
        default=[1, 2, 5, len(ZETA_ZERO_IMAGINARY_PARTS)],
        help="zero-pair cutoffs to compare in the truncation sensitivity table",
    )
    parser.add_argument("--output", type=Path, default=DEFAULT_REPORT_PATH)
    args = parser.parse_args(argv)

    if args.n_max < 1:
        parser.error("--n-max must be at least 1")
    if args.zero_pairs < 1 or args.zero_pairs > len(ZETA_ZERO_IMAGINARY_PARTS):
        parser.error(
            f"--zero-pairs must be between 1 and {len(ZETA_ZERO_IMAGINARY_PARTS)}"
        )

    output = write_report(
        output=args.output,
        n_max=args.n_max,
        ordinates=ZETA_ZERO_IMAGINARY_PARTS,
        zero_pairs=args.zero_pairs,
        sensitivity_cutoffs=args.sensitivity_cutoffs,
    )
    print(f"wrote truncated Li coefficient report to {output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
