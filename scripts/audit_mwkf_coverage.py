#!/usr/bin/env python3
"""Exact-rational adapters for published MWKF core estimates.

The adapters only certify a route when every encoded hypothesis and the
fixed target saving hold.  A rejected result is a coverage witness, not a
claim that the corresponding theorem is false.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).parents[1]))

from scripts.audit_mwkf_ranges import (
    ExponentBox,
    boundary_witnesses,
    is_admissible,
)


F = Fraction
TARGET_SAVING = F(1, 1000)


@dataclass(frozen=True)
class RouteResult:
    route: str
    applicable: bool
    saving: Fraction | None
    source: str
    reason: str
    conditions: tuple[str, ...]


def _positive_part(value: Fraction) -> Fraction:
    return max(F(0), value)


def bcr_adapter(box: ExponentBox) -> RouteResult:
    """Apply Bettin--Chandee Theorem 1 to separated coefficients.

    Norm exponents are ``rho/2``, ``sigma/2``, and ``a/2``.  The returned
    saving is ``rho + sigma`` minus the larger of the two theorem terms.
    """
    a = box.third_length
    total = a + box.rho + box.sigma
    longest = max(box.rho, box.sigma)
    large_a = F(1, 2) * _positive_part(a - box.rho - box.sigma)
    term_1 = F(17, 20) * total + F(1, 4) * longest + large_a
    term_2 = (
        F(7, 8) * (box.rho + box.sigma)
        + a
        + F(1, 8) * longest
        + large_a
    )
    saving = box.rho + box.sigma - max(term_1, term_2)
    admissible = is_admissible(box)
    # Strictness absorbs every fixed polylogarithmic separation norm.
    applicable = admissible and saving > TARGET_SAVING
    reason = "covered" if applicable else (
        "inadmissible_box" if not admissible else "insufficient_saving"
    )
    return RouteResult(
        route="bcr",
        applicable=applicable,
        saving=saving,
        source="Bettin-Chandee, arXiv:1502.00769, Theorem 1",
        reason=reason,
        conditions=(
            "(r,s)=1",
            "a,r,s supported on dyadic intervals",
            "L2 coefficient norms used exactly",
        ),
    )


def h_completion_adapter(box: ExponentBox) -> RouteResult:
    kinematic = box.h >= box.sigma
    return RouteResult(
        route="h_completion",
        applicable=False,
        saving=None,
        source="finite Poisson completion modulo s",
        reason=(
            "no_cited_completed_kernel_bound"
            if kinematic else "frequency_shorter_than_modulus"
        ),
        conditions=("h >= sigma", "coupled kernel retained"),
    )


def delta_completion_adapter(box: ExponentBox) -> RouteResult:
    kinematic = box.ell >= box.sigma
    return RouteResult(
        route="delta_completion",
        applicable=False,
        saving=None,
        source="finite Poisson completion modulo s",
        reason=(
            "no_cited_completed_kernel_bound"
            if kinematic else "shift_shorter_than_modulus"
        ),
        conditions=("ell >= sigma", "coupled kernel retained"),
    )


def wright_fixed_factor_adapter(
    box: ExponentBox,
    *,
    fixed_factor: Fraction | None,
) -> RouteResult:
    """Apply Wright v2 only after a genuine denominator factor is fixed.

    With ``s = n * R_fix`` the theorem variables have exponent
    ``M=rho``, ``N=sigma-fixed_factor``, ``A=ell+h``.
    """
    if fixed_factor is None:
        return RouteResult(
            route="wright_fixed_factor",
            applicable=False,
            saving=None,
            source="Wright, arXiv:2604.25177v2, main theorem",
            reason="no_fixed_denominator_factor",
            conditions=("s=n*R_fix with R_fix fixed",),
        )

    f = fixed_factor
    n = box.sigma - f
    m = box.rho
    a = box.third_length
    if f < 0 or n < 0:
        return RouteResult(
            route="wright_fixed_factor",
            applicable=False,
            saving=None,
            source="Wright, arXiv:2604.25177v2, main theorem",
            reason="invalid_fixed_factor_scale",
            conditions=("0 <= fixed_factor <= sigma",),
        )

    theorem_conditions = m <= 2 * n and (f == 0 or m > 0)
    prefactor = a + m + n + f / 4
    prefactor += F(1, 4) * _positive_part(a - m - n)
    bracket = max(
        -n / 8,
        f / 8 + n / 8 - m / 4,
        m / 10 - 3 * f / 20 - a / 20 - 3 * n / 20,
        3 * n / 20 - 3 * a / 20 - m / 5,
        3 * n / 8 - m / 2,
    )
    bound = prefactor + bracket
    saving = box.rho + box.sigma - bound
    applicable = theorem_conditions and saving >= TARGET_SAVING
    if applicable:
        reason = "covered"
    elif not theorem_conditions:
        reason = "wright_hypotheses_fail"
    else:
        reason = "insufficient_saving"
    return RouteResult(
        route="wright_fixed_factor",
        applicable=applicable,
        saving=saving,
        source="Wright, arXiv:2604.25177v2, main theorem",
        reason=reason,
        conditions=("M <= N^2", "R_fix <= M^C", "(m,n*R_fix)=1"),
    )


def wright_type_i_adapter(
    box: ExponentBox,
    *,
    a_factor: Fraction,
    b_factor: Fraction,
) -> RouteResult:
    """Map a Type-I factorization ``r=a*b`` after reciprocity.

    The phase becomes ``e(h*delta*bar(s)/(a*b))``.  For each fixed ``a``
    Wright has ``M=S``, ``N=B``, ``A=LH``, and ``R_fix=A_0``.  The final
    exponent includes the outer trivial sum over the fixed ``a`` values.
    """
    if a_factor < 0 or b_factor < 0 or a_factor + b_factor != box.rho:
        return RouteResult(
            route="wright_type_i",
            applicable=False,
            saving=None,
            source="Wright, arXiv:2604.25177v2, main theorem",
            reason="invalid_type_i_factorization",
            conditions=("a_factor+b_factor=rho",),
        )

    m = box.sigma
    n = b_factor
    a = box.third_length
    f = a_factor
    theorem_conditions = m <= 2 * n and (f == 0 or m > 0)
    prefactor = a + m + n + f / 4
    prefactor += F(1, 4) * _positive_part(a - m - n)
    bracket = max(
        -n / 8,
        f / 8 + n / 8 - m / 4,
        m / 10 - 3 * f / 20 - a / 20 - 3 * n / 20,
        3 * n / 20 - 3 * a / 20 - m / 5,
        3 * n / 8 - m / 2,
    )
    # Wright is applied for each fixed a; summing those values costs A_0.
    bound = prefactor + bracket + f
    saving = box.rho + box.sigma - bound
    applicable = theorem_conditions and saving > TARGET_SAVING
    if applicable:
        reason = "covered"
    elif not theorem_conditions:
        reason = "wright_hypotheses_fail"
    else:
        reason = "insufficient_saving"
    return RouteResult(
        route="wright_type_i",
        applicable=applicable,
        saving=saving,
        source="Wright, arXiv:2604.25177v2, main theorem",
        reason=reason,
        conditions=(
            "reciprocity applied",
            "M=S and N=B_0",
            "M <= N^2",
            "outer fixed-factor sum included",
        ),
    )


def wright_denominator_factor_adapter(
    box: ExponentBox,
    *,
    fixed_factor: Fraction,
    remaining_factor: Fraction,
) -> RouteResult:
    """Audit Wright after splitting the denominator ``s=c*d``.

    For each fixed ``c`` the theorem has ``M=R``, ``N=D``,
    ``R_fix=C``, and ``A=LH``.  The returned exponent subtracts the
    unavoidable outer trivial sum over all fixed ``c`` values.
    """
    if (
        fixed_factor < 0
        or remaining_factor < 0
        or fixed_factor + remaining_factor != box.sigma
    ):
        return RouteResult(
            route="wright_denominator_factor",
            applicable=False,
            saving=None,
            source="Wright, arXiv:2604.25177v2, main theorem",
            reason="invalid_denominator_factorization",
            conditions=("fixed_factor+remaining_factor=sigma",),
        )

    fixed = wright_fixed_factor_adapter(box, fixed_factor=fixed_factor)
    assert fixed.saving is not None
    saving = fixed.saving - fixed_factor
    theorem_conditions = box.rho <= 2 * remaining_factor
    applicable = theorem_conditions and saving > TARGET_SAVING
    if applicable:
        reason = "covered"
    elif not theorem_conditions:
        reason = "wright_hypotheses_fail"
    else:
        reason = "insufficient_saving"
    return RouteResult(
        route="wright_denominator_factor",
        applicable=applicable,
        saving=saving,
        source="Wright, arXiv:2604.25177v2, main theorem",
        reason=reason,
        conditions=(
            "s=C_0*D_0",
            "M=R and N=D_0",
            "M <= N^2",
            "outer fixed-factor sum included",
        ),
    )


def route_box(box: ExponentBox) -> RouteResult:
    """Return the unique primary route in the approved priority order."""
    bcr = bcr_adapter(box)
    if bcr.applicable:
        return bcr
    for adapter in (h_completion_adapter, delta_completion_adapter):
        result = adapter(box)
        if result.applicable:
            return result
    wright = wright_fixed_factor_adapter(box, fixed_factor=None)
    if wright.applicable:
        return wright
    return RouteResult(
        route="mobius_type_i_ii",
        applicable=False,
        saving=None,
        source="new estimate required",
        reason="published_routes_exhausted",
        conditions=("preserve both Mobius weights", "retain h*delta coupling"),
    )


def _fmt(value: Fraction | None) -> str:
    if value is None:
        return "none"
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def main() -> None:
    small = ExponentBox(F(1), F(1), F(0), F(0), F(0), F(0), F(2))
    boxes = {"bcr_small_a": small, **boundary_witnesses()}
    for name, box in sorted(boxes.items()):
        result = route_box(box)
        bcr = bcr_adapter(box)
        print(
            f"{name}: primary={result.route} reason={result.reason} "
            f"bcr_saving={_fmt(bcr.saving)} target={_fmt(TARGET_SAVING)}"
        )


if __name__ == "__main__":
    main()
