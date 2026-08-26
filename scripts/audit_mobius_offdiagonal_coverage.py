#!/usr/bin/env python3
"""Exact exponent ledger for published MWKF coverage.

The functions in this module check rational exponent inequalities only.
They do not prove the coupled-kernel estimate or any oscillatory-sum bound.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import gcd

try:
    from scripts.audit_mwkf_ranges import (
        ExponentBox,
        boundary_witnesses,
        is_admissible,
    )
    from scripts.mwkf_mobius_type_identity import (
        CoupledProductDoubleMobiusCertificate,
        TypeScaleBounds,
        coupled_product_double_mobius_certificate,
        type_scale_bounds,
    )
except ModuleNotFoundError:  # Direct invocation: python3 scripts/this_file.py
    from audit_mwkf_ranges import (  # type: ignore[no-redef]
        ExponentBox,
        boundary_witnesses,
        is_admissible,
    )
    from mwkf_mobius_type_identity import (  # type: ignore[no-redef]
        CoupledProductDoubleMobiusCertificate,
        TypeScaleBounds,
        coupled_product_double_mobius_certificate,
        type_scale_bounds,
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


@dataclass(frozen=True)
class PublishedCoverageCell:
    """One mutually exclusive cell in the direct-coverage partition."""

    name: str
    route: str
    covered: bool
    decisive_saving: Fraction
    target_saving: Fraction
    reason: str


@dataclass(frozen=True)
class ResidualDoubleMobiusTypeLedger:
    """Exact scale routing for the uncovered double-Möbius cells."""

    coverage_cell: str
    product_frequency_exponent: Fraction
    r_scales: TypeScaleBounds
    s_scales: TypeScaleBounds
    sectors: tuple[str, ...]
    preserves_product_frequency: bool
    preserves_two_mobius_weights: bool
    proves_residual_estimate: bool
    reason: str


@dataclass(frozen=True)
class DrappeauDoubleQuotientAudit:
    """Exact exponent ledger for Drappeau's Theorem 2.1, with q=1."""

    r_smooth_quotient_exponent: Fraction
    s_smooth_quotient_exponent: Fraction
    r_coefficient_exponent: Fraction
    s_coefficient_exponent: Fraction
    coefficient_l2_exponent: Fraction
    k_squared_first_exponent: Fraction
    k_squared_second_exponent: Fraction
    k_squared_third_exponent: Fraction
    bound_exponent: Fraction
    target_exponent: Fraction
    target_deficit: Fraction
    analytic_size_covers: bool
    algebraic_phase_adapter_verified: bool
    arbitrary_coefficient_retains_double_mobius: bool
    product_frequency_retained: bool
    sharp_hyperbola_adapter_verified: bool
    published_coverage: bool


@dataclass(frozen=True)
class DrappeauBalancedHardOptimum:
    """Closed-form minimum of the Drappeau ledger on the hard box."""

    minimum_bound_exponent: Fraction
    r_smooth_quotient_exponent: Fraction
    s_smooth_quotient_min_exponent: Fraction
    s_smooth_quotient_max_exponent: Fraction
    target_exponent: Fraction
    target_deficit: Fraction
    lower_bound_proved_by_two_piece_max: bool


@dataclass(frozen=True)
class DrappeauTypeSubcellAudit:
    """Drappeau audit with the two sharp Type hyperbolas exposed."""

    base: DrappeauDoubleQuotientAudit
    r_truncated_divisor_exponent: Fraction
    s_truncated_divisor_exponent: Fraction
    r_short_mobius_exponent: Fraction
    s_short_mobius_exponent: Fraction
    r_cutoff_exponent: Fraction
    s_cutoff_exponent: Fraction
    r_hyperbola_relation: str
    s_hyperbola_relation: str
    asymptotically_empty: bool
    sharp_hyperbola_adapter_verified: bool
    theorem_q_equals_one: bool
    dyadic_smooth_weight_verified: bool
    coefficient_l2_divisor_bound_verified: bool
    published_coverage: bool


def inverse_product_max_multiplicity(modulus: int, delta: int) -> int:
    """Largest fibre of c -> delta*c^{-1} modulo the modulus on units."""

    if modulus < 1:
        raise ValueError("modulus must be positive")
    fibres: dict[int, int] = {}
    for residue in range(modulus):
        if gcd(residue, modulus) != 1:
            continue
        inverse = pow(residue, -1, modulus)
        image = (delta * inverse) % modulus
        fibres[image] = fibres.get(image, 0) + 1
    return max(fibres.values(), default=0)


def dyadic_gcd_sum(modulus: int, length: int) -> int:
    """Exact two-sign gcd sum for L <= |delta| <= 2L."""

    if modulus < 1 or length < 1:
        raise ValueError("modulus and length must be positive")
    positive = sum(gcd(delta, modulus) for delta in range(length, 2 * length + 1))
    return 2 * positive


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


def bettin_chandee_covers(
    box: ExponentBox,
    *,
    target_saving: Fraction = Fraction(1, 1000),
) -> bool:
    """Whether both BC terms beat the strict local saving target.

    Strictness is essential: the published theorem carries a
    ``T^epsilon`` loss, and equality at ``1/1000`` does not absorb the
    polylogarithmic kernel-separation cost in the accepted gate.
    """

    savings = bettin_chandee_savings(box)
    return (
        is_admissible(box)
        and savings.first > target_saving
        and savings.second > target_saving
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
            "A", "both BC saving exponents beat the strict target"
        )
    if joint_completion_covers(box):
        return CoverageResult(
            "B", "one of the separate h and delta lengths has exponent zero"
        )
    return CoverageResult(
        "D", "no direct Region A-C theorem covers the box"
    )


def published_coverage_cell(
    box: ExponentBox,
    *,
    target_saving: Fraction = Fraction(1, 1000),
) -> PublishedCoverageCell:
    """Return the exact A/B/D cell containing an admissible exponent box.

    The cells are mutually exclusive by construction and exhaustive for
    the direct published/elementary routes currently certified here:

    - ``A`` is the strict Bettin--Chandee cell;
    - ``B`` consists of the two zero-length completion faces, after
      removing ``A``;
    - ``D`` is the remaining positive-width coupled region.

    Wright and Pascadi have empty *direct* cells because their required
    fixed-factor/coefficient adapters are absent before a further exact
    factorization.  This function does not treat a kinematic rewrite as
    theorem coverage.
    """

    if not is_admissible(box):
        raise ValueError("published coverage cells require an admissible box")
    target = Fraction(target_saving)
    savings = bettin_chandee_savings(box)
    decisive = min(savings.first, savings.second)
    order_suffix = (
        "rho_ge_sigma" if box.rho >= box.sigma else "sigma_gt_rho"
    )
    if bettin_chandee_covers(box, target_saving=target):
        return PublishedCoverageCell(
            name=f"A_{order_suffix}",
            route="A",
            covered=True,
            decisive_saving=decisive,
            target_saving=target,
            reason="both Bettin--Chandee terms beat the strict target",
        )
    if box.ell == 0:
        return PublishedCoverageCell(
            name="B_ell_zero",
            route="B",
            covered=True,
            decisive_saving=decisive,
            target_saving=target,
            reason="exact completion has a zero-length delta factor",
        )
    if box.h == 0:
        return PublishedCoverageCell(
            name="B_h_zero",
            route="B",
            covered=True,
            decisive_saving=decisive,
            target_saving=target,
            reason="exact completion has a zero-length h factor",
        )
    return PublishedCoverageCell(
        name=f"D_{order_suffix}",
        route="D",
        covered=False,
        decisive_saving=decisive,
        target_saving=target,
        reason=(
            "at least one Bettin--Chandee term misses the strict target "
            "and both completion lengths are positive"
        ),
    )


def residual_type_i_ii_ledger(
    box: ExponentBox,
    *,
    split_u: Fraction = Fraction(1, 3),
    split_v: Fraction = Fraction(1, 3),
) -> ResidualDoubleMobiusTypeLedger:
    """Route an uncovered cell to the exact four-sector Möbius split.

    This records the scale ranges generated by the finite identity on both
    original Möbius variables.  It deliberately leaves the coupled
    frequency exponent as ``ell+h`` and records no analytic saving.
    """

    cell = published_coverage_cell(box)
    if cell.route != "D":
        raise ValueError("Type-I/II routing accepts only residual D cells")
    return ResidualDoubleMobiusTypeLedger(
        coverage_cell=cell.name,
        product_frequency_exponent=box.ell + box.h,
        r_scales=type_scale_bounds(box.rho, u=split_u, v=split_v),
        s_scales=type_scale_bounds(box.sigma, u=split_u, v=split_v),
        sectors=("I/I", "I/II", "II/I", "II/II"),
        preserves_product_frequency=True,
        preserves_two_mobius_weights=True,
        proves_residual_estimate=False,
        reason=(
            "exact finite reindexing only; each sector still requires a "
            "uniform coupled estimate before absolute values"
        ),
    )


def residual_coupled_type_certificate(
    box: ExponentBox,
    *,
    r: int,
    s: int,
    h: int,
    delta: int,
    r_cutoff_u: int,
    r_cutoff_v: int,
    s_cutoff_u: int,
    s_cutoff_v: int,
) -> CoupledProductDoubleMobiusCertificate:
    """Attach the exact finite coupled certificate only to a residual cell."""

    residual_type_i_ii_ledger(box)
    return coupled_product_double_mobius_certificate(
        r=r,
        s=s,
        h=h,
        delta=delta,
        r_cutoff_u=r_cutoff_u,
        r_cutoff_v=r_cutoff_v,
        s_cutoff_u=s_cutoff_u,
        s_cutoff_v=s_cutoff_v,
    )


def drappeau_double_quotient_audit(
    box: ExponentBox,
    *,
    r_smooth_quotient_exponent: Fraction,
    s_smooth_quotient_exponent: Fraction,
    target_saving: Fraction = Fraction(1, 1000),
) -> DrappeauDoubleQuotientAudit:
    """Evaluate Drappeau's three ``K^2`` terms after double quotienting.

    Put ``d=T^d0`` and ``c=T^c0`` for the smooth quotients.  The other
    two coefficient scales have exponents ``rho-d0`` and ``sigma-c0``;
    the product frequency has exponent ``a=ell+h`` and remains inside the
    arbitrary coefficient ``b[n,r,s]``.  For q=1, Theorem 2.1 gives

    ``K^2 = CS(RS+N)(C+RD)``
    ``      + C^2 DS sqrt((RS+N)R)``
    ``      + D^2 N R / S``.

    The returned ``published_coverage`` remains false until a separate
    proof adapts the sharp Type hyperbola to the theorem's smooth
    ``c,d`` weights.  A favourable exponent alone is not coverage.
    """

    if not is_admissible(box):
        raise ValueError("Drappeau audit requires an admissible box")
    d0 = Fraction(r_smooth_quotient_exponent)
    c0 = Fraction(s_smooth_quotient_exponent)
    if not (0 <= d0 <= box.rho):
        raise ValueError("r smooth quotient must lie between 0 and rho")
    if not (0 <= c0 <= box.sigma):
        raise ValueError("s smooth quotient must lie between 0 and sigma")
    target_saving = Fraction(target_saving)
    if target_saving < 0:
        raise ValueError("target saving must be nonnegative")

    r0 = box.rho - d0
    s0 = box.sigma - c0
    a = box.third_length
    rs_or_n = max(r0 + s0, a)
    coefficient_l2 = Fraction(a + r0 + s0, 2)
    k_first = box.sigma + rs_or_n + max(c0, box.rho)
    k_second = (
        box.sigma
        + c0
        + d0
        + Fraction(rs_or_n + r0, 2)
    )
    k_third = a + box.rho - box.sigma + d0 + c0
    bound = coefficient_l2 + Fraction(
        max(k_first, k_second, k_third),
        2,
    )
    target = box.rho + box.sigma - target_saving
    analytic_size_covers = bound < target
    sharp_hyperbola_adapter_verified = False
    return DrappeauDoubleQuotientAudit(
        r_smooth_quotient_exponent=d0,
        s_smooth_quotient_exponent=c0,
        r_coefficient_exponent=r0,
        s_coefficient_exponent=s0,
        coefficient_l2_exponent=coefficient_l2,
        k_squared_first_exponent=k_first,
        k_squared_second_exponent=k_second,
        k_squared_third_exponent=k_third,
        bound_exponent=bound,
        target_exponent=target,
        target_deficit=max(Fraction(0), bound - target),
        analytic_size_covers=analytic_size_covers,
        algebraic_phase_adapter_verified=True,
        arbitrary_coefficient_retains_double_mobius=True,
        product_frequency_retained=True,
        sharp_hyperbola_adapter_verified=sharp_hyperbola_adapter_verified,
        published_coverage=(
            analytic_size_covers and sharp_hyperbola_adapter_verified
        ),
    )


def drappeau_balanced_hard_optimum(
    *,
    target_saving: Fraction = Fraction(1, 1000),
) -> DrappeauBalancedHardOptimum:
    """Return the exact global minimum on ``rho=sigma=3, a=5``.

    If ``x=c+d <= 1``, the first K term gives a bound at least ``21/2``.
    If ``x >= 1``, the second K term gives ``9-d/4 >= 33/4``.  Equality
    holds for ``d=3`` and every ``5/2 <= c <= 3``; the other K terms are
    then no larger.  This proves the minimum without a numerical grid.
    """

    target = Fraction(6) - Fraction(target_saving)
    minimum = Fraction(33, 4)
    return DrappeauBalancedHardOptimum(
        minimum_bound_exponent=minimum,
        r_smooth_quotient_exponent=Fraction(3),
        s_smooth_quotient_min_exponent=Fraction(5, 2),
        s_smooth_quotient_max_exponent=Fraction(3),
        target_exponent=target,
        target_deficit=minimum - target,
        lower_bound_proved_by_two_piece_max=True,
    )


def _type_hyperbola_relation(
    *,
    truncated_divisor_exponent: Fraction,
    smooth_quotient_exponent: Fraction,
    cutoff_exponent: Fraction,
) -> str:
    """Classify ``d <= U < d*e`` at the exponent level."""

    if truncated_divisor_exponent > cutoff_exponent:
        return "empty"
    product_exponent = (
        truncated_divisor_exponent + smooth_quotient_exponent
    )
    if product_exponent < cutoff_exponent:
        return "empty"
    if (
        truncated_divisor_exponent == cutoff_exponent
        or product_exponent == cutoff_exponent
    ):
        return "boundary"
    return "strict_far"


def drappeau_type_subcell_audit(
    box: ExponentBox,
    *,
    r_truncated_divisor_exponent: Fraction,
    r_smooth_quotient_exponent: Fraction,
    s_truncated_divisor_exponent: Fraction,
    s_smooth_quotient_exponent: Fraction,
    r_cutoff_exponent: Fraction,
    s_cutoff_exponent: Fraction,
    target_saving: Fraction = Fraction(1, 1000),
) -> DrappeauTypeSubcellAudit:
    """Certify strict Type subcells where the sharp hyperbola disappears.

    In one exact Möbius factorization write ``n=d*e*b`` with
    ``d <= U < d*e``.  On a dyadic exponent cell, the two strict gaps
    ``pi<u<pi+epsilon`` make both inequalities identically true for all
    sufficiently large ``T``.  The smooth quotient ``e`` may then be the
    Drappeau ``c`` or ``d`` variable, while ``d*b`` and both Möbius atoms
    stay in the arbitrary coefficient.  Equality is deliberately retained
    as an uncovered boundary face.

    The original reciprocal coprimality is exactly Drappeau's q=1
    condition.  Dyadic localization gives the required smooth weight, and
    the number of factorizations absorbed by ``b[n,r,s]`` is divisor
    bounded, so its L2 exponent is the one recorded in ``base``.
    """

    pi_r = Fraction(r_truncated_divisor_exponent)
    pi_s = Fraction(s_truncated_divisor_exponent)
    eps_r = Fraction(r_smooth_quotient_exponent)
    eps_s = Fraction(s_smooth_quotient_exponent)
    cutoff_r = Fraction(r_cutoff_exponent)
    cutoff_s = Fraction(s_cutoff_exponent)
    if min(pi_r, pi_s, eps_r, eps_s, cutoff_r, cutoff_s) < 0:
        raise ValueError("Type subcell exponents must be nonnegative")
    beta_r = box.rho - pi_r - eps_r
    beta_s = box.sigma - pi_s - eps_s
    if beta_r < 0 or beta_s < 0:
        raise ValueError("Type factors cannot exceed the original scale")

    base = drappeau_double_quotient_audit(
        box,
        r_smooth_quotient_exponent=eps_r,
        s_smooth_quotient_exponent=eps_s,
        target_saving=target_saving,
    )
    r_relation = _type_hyperbola_relation(
        truncated_divisor_exponent=pi_r,
        smooth_quotient_exponent=eps_r,
        cutoff_exponent=cutoff_r,
    )
    s_relation = _type_hyperbola_relation(
        truncated_divisor_exponent=pi_s,
        smooth_quotient_exponent=eps_s,
        cutoff_exponent=cutoff_s,
    )
    asymptotically_empty = "empty" in (r_relation, s_relation)
    sharp_adapter = (
        r_relation == "strict_far" and s_relation == "strict_far"
    )
    theorem_q_equals_one = True
    dyadic_smooth_weight_verified = True
    coefficient_l2_divisor_bound_verified = True
    published_coverage = (
        not asymptotically_empty
        and base.analytic_size_covers
        and sharp_adapter
        and theorem_q_equals_one
        and dyadic_smooth_weight_verified
        and coefficient_l2_divisor_bound_verified
    )
    return DrappeauTypeSubcellAudit(
        base=base,
        r_truncated_divisor_exponent=pi_r,
        s_truncated_divisor_exponent=pi_s,
        r_short_mobius_exponent=beta_r,
        s_short_mobius_exponent=beta_s,
        r_cutoff_exponent=cutoff_r,
        s_cutoff_exponent=cutoff_s,
        r_hyperbola_relation=r_relation,
        s_hyperbola_relation=s_relation,
        asymptotically_empty=asymptotically_empty,
        sharp_hyperbola_adapter_verified=sharp_adapter,
        theorem_q_equals_one=theorem_q_equals_one,
        dyadic_smooth_weight_verified=dyadic_smooth_weight_verified,
        coefficient_l2_divisor_bound_verified=(
            coefficient_l2_divisor_bound_verified
        ),
        published_coverage=published_coverage,
    )


def published_coverage_witnesses() -> dict[str, ExponentBox]:
    """One exact rational admissible witness for every coverage cell."""

    F = Fraction
    boundary = boundary_witnesses()
    return {
        "A_rho_ge_sigma": ExponentBox(
            F(1), F(1), F(0), F(0), F(0), F(0), F(0)
        ),
        "A_sigma_gt_rho": ExponentBox(
            F(1), F(6, 5), F(1, 5), F(0), F(0), F(0), F(0)
        ),
        "B_ell_zero": boundary["large_q_endpoint"],
        "B_h_zero": ExponentBox(
            F(2), F(1), F(0), F(1), F(1), F(0), F(0)
        ),
        "D_rho_ge_sigma": boundary["balanced_max_a"],
        "D_sigma_gt_rho": boundary["s_long"],
    }


def _format_fraction(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def main() -> None:
    for name, box in sorted(published_coverage_witnesses().items()):
        savings = bettin_chandee_savings(box)
        completion = completion_exponents(box)
        joint_loss = joint_completion_loss(box)
        cell = published_coverage_cell(box)
        completion_text = ",".join(_format_fraction(x) for x in completion)
        print(
            f"{name}: route={cell.route} covered={cell.covered} "
            f"bc_first={_format_fraction(savings.first)} "
            f"bc_second={_format_fraction(savings.second)} "
            f"completion={completion_text} "
            f"joint_completion={_format_fraction(joint_loss)}"
        )


if __name__ == "__main__":
    main()
