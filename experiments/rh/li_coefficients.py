from __future__ import annotations

import argparse
import csv
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

DEFAULT_OUTPUT_DIR = Path(__file__).resolve().parent / "output"
DEFAULT_REPORT_PATH = DEFAULT_OUTPUT_DIR / "li_coefficients_report.md"
DEFAULT_COEFFICIENTS_CSV_PATH = DEFAULT_OUTPUT_DIR / "li_coefficients.csv"
DEFAULT_SENSITIVITY_CSV_PATH = DEFAULT_OUTPUT_DIR / "li_truncation_sensitivity.csv"
DEFAULT_ZERO_FIXTURE_PATH = Path(__file__).resolve().parent / "zeros_fixture.csv"
DEFAULT_SENSITIVITY_CUTOFF_CANDIDATES = (1, 2, 5, len(ZETA_ZERO_IMAGINARY_PARTS))
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


@dataclass(frozen=True)
class ZetaZeroRecord:
    index: int
    ordinate: float
    source: str = ""
    source_url: str = ""
    note: str = ""


@dataclass(frozen=True)
class ZetaZeroFixture:
    records: tuple[ZetaZeroRecord, ...]
    path: Path | None = None

    @property
    def ordinates(self) -> tuple[float, ...]:
        return tuple(record.ordinate for record in self.records)

    @property
    def provenance_notes(self) -> tuple[str, ...]:
        notes: list[str] = []
        seen: set[str] = set()
        for record in self.records:
            parts = [
                part
                for part in (record.source, record.source_url, record.note)
                if part
            ]
            if not parts:
                continue
            note = "; ".join(parts)
            if note not in seen:
                notes.append(note)
                seen.add(note)
        return tuple(notes)


def _validate_n(n: int) -> None:
    if n < 1:
        raise ValueError("Li coefficient index n must be at least 1")


def zeta_zero_pair(ordinate: float) -> tuple[complex, complex]:
    if ordinate <= 0.0:
        raise ValueError("zero ordinates must be positive")

    rho = complex(0.5, ordinate)
    return rho, rho.conjugate()


def _nonempty_csv_lines(path: Path):
    with path.open(newline="", encoding="utf-8") as handle:
        for line in handle:
            if not line.strip() or line.lstrip().startswith("#"):
                continue
            yield line


def load_zero_fixture(path: Path | str = DEFAULT_ZERO_FIXTURE_PATH) -> ZetaZeroFixture:
    fixture_path = Path(path)
    reader = csv.DictReader(_nonempty_csv_lines(fixture_path))
    if reader.fieldnames is None:
        raise ValueError(f"{fixture_path} does not contain a CSV header")
    if "ordinate" not in reader.fieldnames:
        raise ValueError(f"{fixture_path} must include an 'ordinate' column")

    records: list[ZetaZeroRecord] = []
    for row_number, row in enumerate(reader, start=2):
        try:
            ordinate = float((row.get("ordinate") or "").strip())
        except ValueError as exc:
            raise ValueError(
                f"{fixture_path}:{row_number} has a non-numeric ordinate"
            ) from exc
        if ordinate <= 0.0:
            raise ValueError(f"{fixture_path}:{row_number} ordinate must be positive")

        raw_index = (row.get("index") or "").strip()
        try:
            index = int(raw_index) if raw_index else len(records) + 1
        except ValueError as exc:
            raise ValueError(
                f"{fixture_path}:{row_number} has a non-integer index"
            ) from exc
        if index < 1:
            raise ValueError(f"{fixture_path}:{row_number} index must be positive")

        source = (row.get("source") or "").strip()
        source_url = (row.get("source_url") or "").strip()
        note = (row.get("note") or "").strip()
        if not (source or source_url or note):
            raise ValueError(
                f"{fixture_path}:{row_number} must include source, source_url, or note"
            )

        records.append(
            ZetaZeroRecord(
                index=index,
                ordinate=ordinate,
                source=source,
                source_url=source_url,
                note=note,
            )
        )

    if not records:
        raise ValueError(f"{fixture_path} does not contain any zero ordinates")
    return ZetaZeroFixture(records=tuple(records), path=fixture_path)


def default_zero_fixture() -> ZetaZeroFixture:
    if DEFAULT_ZERO_FIXTURE_PATH.exists():
        return load_zero_fixture(DEFAULT_ZERO_FIXTURE_PATH)

    records = tuple(
        ZetaZeroRecord(
            index=index,
            ordinate=ordinate,
            source="embedded repository fallback",
            note=(
                "Existing in-module fixture of early positive zeta-zero ordinates; "
                "rounded decimal data for empirical truncation tests only."
            ),
        )
        for index, ordinate in enumerate(ZETA_ZERO_IMAGINARY_PARTS, start=1)
    )
    return ZetaZeroFixture(records=records)


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
    source_notes: Sequence[str] = (),
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
    ]
    if source_notes:
        lines.extend(
            [
                "",
                "## Fixture Provenance",
                "",
                *[f"- {note}" for note in source_notes],
                "",
                "These provenance notes identify the finite input data only.",
                "They do not certify the Li criterion or prove RH.",
            ]
        )

    lines.extend(
        [
            "",
            "| n | truncated lambda_n | sign |",
            "|---:|---:|:---|",
        ]
    )
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
    source_notes: Sequence[str] = (),
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
    output.write_text(
        render_report(
            rows,
            selected_ordinates,
            sensitivity_rows,
            source_notes=source_notes,
        ),
        encoding="utf-8",
    )
    return output


def write_li_coefficient_csv(
    output: Path,
    rows: Sequence[LiCoefficientApproximation],
    zero_pair_count: int,
) -> Path:
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle)
        writer.writerow(
            [
                "n",
                "truncated_lambda_n",
                "sign",
                "positive_zero_pairs",
                "paired_nontrivial_zeros",
                "empirical_note",
            ]
        )
        for row in rows:
            writer.writerow(
                [
                    row.n,
                    f"{row.value:.12g}",
                    row.sign,
                    zero_pair_count,
                    zero_pair_count * 2,
                    REPORT_WARNING,
                ]
            )
    return output


def write_truncation_sensitivity_csv(
    output: Path,
    rows: Sequence[TruncationSensitivityRow],
) -> Path:
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle)
        writer.writerow(
            [
                "n",
                "zero_pairs",
                "truncated_lambda_n",
                "delta_from_previous_cutoff",
                "empirical_note",
            ]
        )
        for row in rows:
            delta = (
                ""
                if row.delta_from_previous_cutoff is None
                else f"{row.delta_from_previous_cutoff:.12g}"
            )
            writer.writerow(
                [
                    row.n,
                    row.zero_pairs,
                    f"{row.value:.12g}",
                    delta,
                    REPORT_WARNING,
                ]
            )
    return output


def default_sensitivity_cutoffs(zero_pair_count: int) -> list[int]:
    if zero_pair_count < 1:
        raise ValueError("zero_pair_count must be at least 1")

    cutoffs = [
        cutoff
        for cutoff in DEFAULT_SENSITIVITY_CUTOFF_CANDIDATES
        if cutoff <= zero_pair_count
    ]
    if zero_pair_count not in cutoffs:
        cutoffs.append(zero_pair_count)
    return sorted(set(cutoffs))


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Generate a truncated Li coefficient experiment report."
    )
    parser.add_argument("--n-max", type=int, default=10)
    parser.add_argument(
        "--zeros",
        type=Path,
        default=None,
        help="CSV fixture with index, ordinate, and provenance columns",
    )
    parser.add_argument("--zero-pairs", type=int, default=None)
    parser.add_argument(
        "--sensitivity-cutoffs",
        type=int,
        nargs="*",
        default=None,
        help="zero-pair cutoffs to compare in the truncation sensitivity table",
    )
    parser.add_argument("--output", type=Path, default=DEFAULT_REPORT_PATH)
    parser.add_argument(
        "--coefficients-csv",
        type=Path,
        default=DEFAULT_COEFFICIENTS_CSV_PATH,
        help="CSV output for the Li coefficient table",
    )
    parser.add_argument(
        "--sensitivity-csv",
        type=Path,
        default=DEFAULT_SENSITIVITY_CSV_PATH,
        help="CSV output for the truncation sensitivity table",
    )
    args = parser.parse_args(argv)

    fixture = load_zero_fixture(args.zeros) if args.zeros else default_zero_fixture()
    ordinates = fixture.ordinates
    zero_pairs = args.zero_pairs if args.zero_pairs is not None else len(ordinates)
    sensitivity_cutoffs = (
        args.sensitivity_cutoffs
        if args.sensitivity_cutoffs is not None
        else default_sensitivity_cutoffs(len(ordinates))
    )

    if args.n_max < 1:
        parser.error("--n-max must be at least 1")
    if zero_pairs < 1 or zero_pairs > len(ordinates):
        parser.error(f"--zero-pairs must be between 1 and {len(ordinates)}")
    invalid_cutoffs = [
        cutoff for cutoff in sensitivity_cutoffs if cutoff < 1 or cutoff > len(ordinates)
    ]
    if invalid_cutoffs:
        parser.error(
            f"--sensitivity-cutoffs must be between 1 and {len(ordinates)}"
        )

    output = write_report(
        output=args.output,
        n_max=args.n_max,
        ordinates=ordinates,
        zero_pairs=zero_pairs,
        sensitivity_cutoffs=sensitivity_cutoffs,
        source_notes=fixture.provenance_notes,
    )
    selected_ordinates = ordinates[:zero_pairs]
    coefficient_rows = li_coefficient_table(
        n_max=args.n_max,
        ordinates=selected_ordinates,
    )
    sensitivity_rows = (
        truncation_sensitivity_table(
            n_values=range(1, args.n_max + 1),
            zero_pair_counts=sensitivity_cutoffs,
            ordinates=ordinates,
        )
        if sensitivity_cutoffs
        else []
    )
    coefficients_csv = write_li_coefficient_csv(
        args.coefficients_csv,
        coefficient_rows,
        zero_pair_count=zero_pairs,
    )
    sensitivity_csv = write_truncation_sensitivity_csv(
        args.sensitivity_csv,
        sensitivity_rows,
    )
    print(f"wrote truncated Li coefficient report to {output}")
    print(f"wrote Li coefficient CSV to {coefficients_csv}")
    print(f"wrote truncation sensitivity CSV to {sensitivity_csv}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
