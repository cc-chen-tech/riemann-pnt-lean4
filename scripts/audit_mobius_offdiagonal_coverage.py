#!/usr/bin/env python3
"""Exact exponent ledger for published MWKF coverage.

The functions in this module check rational exponent inequalities only.
They do not prove the coupled-kernel estimate or any oscillatory-sum bound.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

try:
    from scripts.audit_mwkf_ranges import (
        ExponentBox,
        boundary_witnesses,
        is_admissible,
    )
except ModuleNotFoundError:  # Direct invocation: python3 scripts/this_file.py
    from audit_mwkf_ranges import (  # type: ignore[no-redef]
        ExponentBox,
        boundary_witnesses,
        is_admissible,
    )


@dataclass(frozen=True)
class BettinChandeeSavings:
    """Savings over the local ``RS`` target from BC Theorem 1's terms."""

    first: Fraction
    second: Fraction


@dataclass(frozen=True)
class WrightApplicability:
    """Whether Wright's fixed-denominator result directly improves BC."""

    improves_bc: bool
    reason: str


@dataclass(frozen=True)
class CoverageResult:
    """Primary route assigned by the published-estimate audit."""

    route: str
    reason: str


def bettin_chandee_savings(box: ExponentBox) -> BettinChandeeSavings:
    """Return the exact savings supplied by the two BC terms."""

    a = box.third_length
    largest = max(box.rho, box.sigma)
    smallest = min(box.rho, box.sigma)
    return BettinChandeeSavings(
        first=(
            Fraction(3, 20) * (box.rho + box.sigma)
            - Fraction(17, 20) * a
            - Fraction(1, 4) * largest
        ),
        second=Fraction(1, 8) * smallest - a,
    )


def bettin_chandee_covers(box: ExponentBox) -> bool:
    """Whether both BC terms are at most ``RS T^epsilon``."""

    savings = bettin_chandee_savings(box)
    return (
        is_admissible(box)
        and savings.first >= 0
        and savings.second >= 0
    )


def completion_exponents(
    box: ExponentBox,
) -> tuple[Fraction, Fraction, Fraction]:
    """Losses from trivial summation and one-factor completion.

    The entries are the exponents of ``LH``, completion in ``h``, and
    completion in ``delta`` after the ``RS`` outer scale is removed.
    """

    return (
        box.third_length,
        max(box.sigma, box.ell),
        max(box.sigma, box.h),
    )


def completion_covers(box: ExponentBox) -> bool:
    """Whether elementary completion alone reaches ``RS T^epsilon``."""

    return is_admissible(box) and min(completion_exponents(box)) <= 0


def joint_completion_loss(box: ExponentBox) -> Fraction:
    """Loss after completing one product factor and averaging a modulus.

    Completion in ``h`` followed by the ``r`` residue permutation costs
    ``L``; the reciprocal orientation with ``delta`` costs ``H``.  The
    better bound therefore loses ``min(L, H)`` over the local target.
    """

    return min(box.ell, box.h)


def joint_completion_covers(box: ExponentBox) -> bool:
    """Whether joint completion reaches the local target."""

    return is_admissible(box) and joint_completion_loss(box) <= 0


def wright_direct_applicability(
    box: ExponentBox, fixed_denominator_factor: Fraction
) -> WrightApplicability:
    """Audit direct use of Wright Theorem 2.1 on the original ``s`` sum.

    ``fixed_denominator_factor`` is the exponent of Wright's fixed integer
    ``R0``. The original sum has ``R0 = 1``, hence exponent zero. A
    positive exponent is available only after a structured factorization
    ``s = R0 n``, which is not a direct Region-C application.
    """

    if not is_admissible(box):
        return WrightApplicability(False, "the exponent box is inadmissible")
    if fixed_denominator_factor == 0:
        return WrightApplicability(
            False, "R0=1 recovers BC equation (7.2), so gives no improvement"
        )
    return WrightApplicability(
        False,
        "a positive fixed factor requires a prior factorization of s "
        "and belongs to Region D",
    )


def classify_box(box: ExponentBox) -> CoverageResult:
    """Assign an admissible box to the first directly proved route."""

    if not is_admissible(box):
        return CoverageResult("invalid", "the exponent box is inadmissible")
    if bettin_chandee_covers(box):
        return CoverageResult(
            "A", "both BC saving exponents are nonnegative"
        )
    if joint_completion_covers(box):
        return CoverageResult(
            "B", "one of the separate h and delta lengths has exponent zero"
        )
    return CoverageResult(
        "D", "no direct Region A-C theorem covers the box"
    )


def _format_fraction(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def main() -> None:
    for name, box in sorted(boundary_witnesses().items()):
        savings = bettin_chandee_savings(box)
        completion = completion_exponents(box)
        joint_loss = joint_completion_loss(box)
        result = classify_box(box)
        completion_text = ",".join(_format_fraction(x) for x in completion)
        print(
            f"{name}: route={result.route} "
            f"bc_first={_format_fraction(savings.first)} "
            f"bc_second={_format_fraction(savings.second)} "
            f"completion={completion_text} "
            f"joint_completion={_format_fraction(joint_loss)}"
        )


if __name__ == "__main__":
    main()
