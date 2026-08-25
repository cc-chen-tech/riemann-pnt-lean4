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


@dataclass(frozen=True)
class ShiftedPoissonScales:
    v: Fraction
    j: Fraction
    shift: Fraction
    target: Fraction
    gate_target: Fraction
    volume: Fraction
    required_saving: Fraction
    square_root_margin: Fraction


@dataclass(frozen=True)
class ShiftedPoissonSubboxScales:
    v: Fraction
    j: Fraction
    shift: Fraction
    target: Fraction
    gate_target: Fraction
    volume: Fraction
    required_saving: Fraction
    square_root_margin: Fraction


@dataclass(frozen=True)
class JointPhaseScales:
    stationary_h: Fraction
    t_phase_variation: Fraction
    fourier_phase_variation: Fraction
    same_sign_derivative_parameter: Fraction
    on_stationary_face: bool
    same_sign_power_saving: bool


@dataclass(frozen=True)
class DualCellIsolationScales:
    dual_v: Fraction
    fourier_window: Fraction
    normalized_h_spread: Fraction
    physical_h_support: Fraction
    seminorm_cost_per_derivative: Fraction
    uniform_in_original_kernel_class: bool


@dataclass(frozen=True)
class FareyCriticalScales:
    dual_v: Fraction
    j_interval: Fraction
    at_most_one_j: bool
    rational_approximation: Fraction
    farey_spacing: Fraction
    approximation_minus_spacing: Fraction


@dataclass(frozen=True)
class FareyCompletionScales:
    v: Fraction
    residue_frequency: Fraction
    product_frequency: Fraction
    residue_density_prefactor: Fraction
    two_dimensional_completion_prefactor: Fraction
    both_coordinate_axes_empty: bool
    farey_gate_target: Fraction
    normalized_gate_target: Fraction
    normalized_volume: Fraction
    required_saving: Fraction
    square_root_margin: Fraction
    generic_bcr_bound: Fraction
    generic_bcr_deficit: Fraction
    optimistic_distinct_large_sieve_bound: Fraction
    optimistic_distinct_large_sieve_deficit: Fraction
    fraction_multiplicity_exponent: Fraction
    separated_additive_large_sieve_bound: Fraction
    separated_additive_large_sieve_deficit: Fraction
    zero_residue_forces_centering: bool


@dataclass(frozen=True)
class MobiusTraceFunctionAudit:
    length_margin: Fraction
    length_hypothesis: bool
    modulus_is_prime: bool
    trace_is_nonexceptional: bool
    theorem_applicable: bool
    power_target_covered: bool
    reasons: tuple[str, ...]


@dataclass(frozen=True)
class AveragedChowlaShiftAudit:
    shift: Fraction
    product_frequency: Fraction
    correlation_volume: Fraction
    logarithmic_gate_target: Fraction
    power_deficit: Fraction
    unit_linear_slopes: bool
    zero_shift_excluded: bool
    theorem_applicable: bool
    source: str
    reasons: tuple[str, ...]


def _positive_part(value: Fraction) -> Fraction:
    return max(F(0), value)


def completion_dual_exponent(
    length_exponent: Fraction,
    modulus_exponent: Fraction,
) -> Fraction:
    """Length of the effective smooth-Poisson dual interval."""
    return _positive_part(modulus_exponent - length_exponent)


def h_poisson_shifted_scales(box: ExponentBox) -> ShiftedPoissonScales:
    """Exact zero-slack ledger after Poisson summation in ``h``.

    The transformed equation is ``delta = r*v - j*s``.  ``volume`` is
    the lattice-volume exponent before arithmetic cancellation; it records
    the codimension imposed by the shift window and is not an estimate.
    """
    v = completion_dual_exponent(box.h, box.sigma)
    j = max(F(0), box.rho - box.h, box.ell - box.sigma)
    product_scale = max(box.rho + v, box.sigma + j)
    volume = (
        box.rho
        + box.sigma
        + v
        + j
        - _positive_part(product_scale - box.ell)
    )
    target = box.rho + box.sigma - box.h
    gate_target = target - TARGET_SAVING
    return ShiftedPoissonScales(
        v=v,
        j=j,
        shift=box.ell,
        target=target,
        gate_target=gate_target,
        volume=volume,
        required_saving=volume - gate_target,
        square_root_margin=gate_target - volume / 2,
    )


def h_poisson_subbox_scales(
    box: ExponentBox,
    *,
    v: Fraction,
    j: Fraction,
) -> ShiftedPoissonSubboxScales:
    """Ledger for one dyadic ``(v,j)`` box after ``h``-Poisson.

    Exponent zero includes every fixed bounded interval, in particular the
    resonance box ``v=j=1``.  The returned saving is volume minus the
    coupled target and does not assert that such cancellation is known.
    """
    v_max = completion_dual_exponent(box.h, box.sigma)
    j_max = max(F(0), box.rho - box.h, box.ell - box.sigma)
    if v < 0 or j < 0 or v > v_max or j > j_max:
        raise ValueError("subbox exponents exceed the h-Poisson dual ranges")
    product_scale = max(box.rho + v, box.sigma + j)
    volume = (
        box.rho
        + box.sigma
        + v
        + j
        - _positive_part(product_scale - box.ell)
    )
    target = box.rho + box.sigma - box.h
    gate_target = target - TARGET_SAVING
    return ShiftedPoissonSubboxScales(
        v=v,
        j=j,
        shift=box.ell,
        target=target,
        gate_target=gate_target,
        volume=volume,
        required_saving=volume - gate_target,
        square_root_margin=gate_target - volume / 2,
    )


def joint_phase_scales(box: ExponentBox) -> JointPhaseScales:
    """Audit the joint ``(x,t)`` phase before ``h``-Poisson.

    On ``x \\asymp T^m`` the phase is

    ``t*log(1+delta/(x*r)) - 2*pi*h*x/s``.

    In the small-shift regime its two normalized variation exponents are
    ``1+ell-m-rho`` and ``h+m-sigma``.  For opposite signs of ``h`` and
    ``delta`` the stationary face is
    ``h=sigma+1+ell-2*m-rho``.  For equal signs the derivatives add, but
    integration by parts yields a power of ``T`` only when their largest
    normalized variation exponent is strictly positive.
    """
    t_variation = F(1) + box.ell - box.m - box.rho
    fourier_variation = box.h + box.m - box.sigma
    parameter = max(t_variation, fourier_variation)
    stationary_h = box.sigma + 1 + box.ell - 2 * box.m - box.rho
    return JointPhaseScales(
        stationary_h=stationary_h,
        t_phase_variation=t_variation,
        fourier_phase_variation=fourier_variation,
        same_sign_derivative_parameter=parameter,
        on_stationary_face=box.h == stationary_h,
        same_sign_power_saving=parameter > 0,
    )


def dual_cell_isolation_scales(
    box: ExponentBox,
    *,
    dual_v: Fraction,
) -> DualCellIsolationScales:
    """Ledger for isolating a dyadic ``v`` scale after ``h``-Poisson.

    The Fourier coordinate is ``xi=H*v/s``.  A scale
    ``v \\asymp T^nu`` therefore occupies a window of exponent
    ``h+nu-sigma``.  Multiplication by a cutoff on that window convolves
    the normalized ``h/H`` weight over the reciprocal scale.  A positive
    reciprocal exponent is a power loss in every derivative seminorm, so
    the isolated cell is not uniform in the original coupled-kernel class.
    """
    dual_max = completion_dual_exponent(box.h, box.sigma)
    if dual_v < 0 or dual_v > dual_max:
        raise ValueError("dual_v exceeds the h-Poisson range")
    fourier_window = box.h + dual_v - box.sigma
    spread = _positive_part(-fourier_window)
    return DualCellIsolationScales(
        dual_v=dual_v,
        fourier_window=fourier_window,
        normalized_h_spread=spread,
        physical_h_support=box.h + spread,
        seminorm_cost_per_derivative=spread,
        uniform_in_original_kernel_class=spread == 0,
    )


def farey_critical_scales(
    box: ExponentBox,
    *,
    dual_v: Fraction,
) -> FareyCriticalScales:
    """Ledger for ``r/s`` approximated by the dual rational ``j/v``.

    The determinant equation gives the exact identity
    ``r/s-j/v=delta/(s*v)``.  The natural spacing between fractions of
    denominator ``T^dual_v`` is ``T^(-2*dual_v)``.  For fixed ``r,s,v``,
    the allowed ``j`` interval has length exponent ``ell-sigma``.
    """
    dual_max = completion_dual_exponent(box.h, box.sigma)
    if dual_v < 0 or dual_v > dual_max:
        raise ValueError("dual_v exceeds the h-Poisson range")
    approximation = box.ell - box.sigma - dual_v
    spacing = -2 * dual_v
    j_interval = box.ell - box.sigma
    return FareyCriticalScales(
        dual_v=dual_v,
        j_interval=j_interval,
        at_most_one_j=j_interval < 0,
        rational_approximation=approximation,
        farey_spacing=spacing,
        approximation_minus_spacing=approximation - spacing,
    )


def farey_completion_scales(box: ExponentBox) -> FareyCompletionScales:
    """Ledger after exact finite Fourier inversion in the shift residue.

    The signed shift has scale ``L=T^ell`` inside residues modulo
    ``s=T^sigma``.  Its normalized Fourier coefficients contribute the
    exact density factor ``L/S`` and have effective frequency length
    ``K=S/L``.  The existing ``h``-Poisson frequency has length ``V=S/H``.
    Removing the density factor turns the Farey target into the target for
    a four-variable Kloosterman-fraction sum in ``(r,s,c,v)``.

    These are support and normalization exponents only; the function does
    not assert cancellation in that completed sum.
    """
    v = completion_dual_exponent(box.h, box.sigma)
    residue_frequency = completion_dual_exponent(box.ell, box.sigma)
    prefactor = box.ell - box.sigma
    farey_target = box.rho + box.sigma - box.h - TARGET_SAVING
    normalized_target = farey_target - prefactor
    volume = box.rho + box.sigma + v + residue_frequency
    product_frequency = v + residue_frequency
    total = product_frequency + box.rho + box.sigma
    longest = max(box.rho, box.sigma)
    large_a = F(1, 2) * _positive_part(
        product_frequency - box.rho - box.sigma
    )
    bcr_term_1 = F(17, 20) * total + F(1, 4) * longest + large_a
    bcr_term_2 = (
        F(7, 8) * (box.rho + box.sigma)
        + product_frequency
        + F(1, 8) * longest
        + large_a
    )
    generic_bcr_bound = max(bcr_term_1, bcr_term_2)
    optimistic_large_sieve_bound = (
        box.rho
        + box.sigma
        + product_frequency
        + max(box.rho, 2 * box.sigma)
    ) / 2
    # Fractions a/s need not be reduced.  A fixed reduced fraction can have
    # up to T^product_frequency representatives in the (a,s) box.  Combining
    # duplicate points by Cauchy costs half that exponent.
    fraction_multiplicity = product_frequency
    additive_large_sieve_bound = (
        optimistic_large_sieve_bound + fraction_multiplicity / 2
    )
    return FareyCompletionScales(
        v=v,
        residue_frequency=residue_frequency,
        product_frequency=product_frequency,
        residue_density_prefactor=prefactor,
        two_dimensional_completion_prefactor=(
            box.ell + box.h - box.sigma
        ),
        both_coordinate_axes_empty=(
            box.ell < box.sigma and box.h < box.sigma
        ),
        farey_gate_target=farey_target,
        normalized_gate_target=normalized_target,
        normalized_volume=volume,
        required_saving=volume - normalized_target,
        square_root_margin=normalized_target - volume / 2,
        generic_bcr_bound=generic_bcr_bound,
        generic_bcr_deficit=generic_bcr_bound - normalized_target,
        optimistic_distinct_large_sieve_bound=(
            optimistic_large_sieve_bound
        ),
        optimistic_distinct_large_sieve_deficit=(
            optimistic_large_sieve_bound - normalized_target
        ),
        fraction_multiplicity_exponent=fraction_multiplicity,
        separated_additive_large_sieve_bound=additive_large_sieve_bound,
        separated_additive_large_sieve_deficit=(
            additive_large_sieve_bound - normalized_target
        ),
        zero_residue_forces_centering=box.ell < box.sigma,
    )


def mobius_trace_function_audit(
    box: ExponentBox,
    *,
    modulus_is_prime: bool,
    trace_is_nonexceptional: bool,
) -> MobiusTraceFunctionAudit:
    """Audit Korolev--Shparlinski Theorem 2.1 against a CFK slice.

    The theorem treats a prime modulus, a nonexceptional bounded-
    conductor trace function, and a Möbius interval longer than
    ``p^(1/2+epsilon)``.  Its conclusion saves one logarithm (up to
    ``loglog``), not a fixed power.  The CFK phase in the ``r`` variable is
    linear additive, ``e(c*v*r/s)``, which belongs to the exceptional class
    explicitly excluded by the theorem; its modulus ``s`` also varies over
    general squarefree integers.
    """
    length_margin = box.rho - box.sigma / 2
    length_hypothesis = length_margin > 0
    reasons: list[str] = []
    if not modulus_is_prime:
        reasons.append("requires_prime_modulus")
    if not trace_is_nonexceptional:
        reasons.append("linear_additive_trace_is_exceptional")
    if not length_hypothesis:
        reasons.append("interval_not_beyond_square_root")
    reasons.append("only_logarithmic_saving")
    theorem_applicable = (
        modulus_is_prime
        and trace_is_nonexceptional
        and length_hypothesis
    )
    return MobiusTraceFunctionAudit(
        length_margin=length_margin,
        length_hypothesis=length_hypothesis,
        modulus_is_prime=modulus_is_prime,
        trace_is_nonexceptional=trace_is_nonexceptional,
        theorem_applicable=theorem_applicable,
        power_target_covered=False,
        reasons=tuple(reasons),
    )


def averaged_chowla_shift_audit(
    box: ExponentBox,
) -> AveragedChowlaShiftAudit:
    """Audit averaged Chowla after the exact substitution ``r=s+d``.

    The centered phase becomes ``e(a*d/s)-1`` because ``a`` is an
    integer.  Both Möbius arguments, ``s`` and ``s+d``, consequently have
    unit linear slope.  Matomäki--Radziwiłł--Tao's averaged Elliott theorem
    supplies logarithmic decay for fixed linear-form weights; it supplies
    no positive power and does not accept the actual coefficient
    ``Lambda_{s+d,s}(a)``, which depends jointly on the base and shift.
    """
    completion = farey_completion_scales(box)
    shift = max(box.rho, box.sigma)
    product_frequency = completion.product_frequency
    correlation_volume = box.sigma + shift + product_frequency
    logarithmic_gate_target = (
        completion.normalized_gate_target + TARGET_SAVING
    )
    power_deficit = correlation_volume - logarithmic_gate_target
    reasons = [
        "joint_s_shift_frequency_coefficient",
        "averaged_chowla_saves_only_logarithms",
    ]
    if power_deficit > 0:
        reasons.append("positive_power_deficit")
    return AveragedChowlaShiftAudit(
        shift=shift,
        product_frequency=product_frequency,
        correlation_volume=correlation_volume,
        logarithmic_gate_target=logarithmic_gate_target,
        power_deficit=power_deficit,
        unit_linear_slopes=True,
        zero_shift_excluded=min(box.rho, box.sigma) > 0,
        theorem_applicable=False,
        source=(
            "Matomaki-Radziwill-Tao, arXiv:1503.05121, Theorem 1.6"
        ),
        reasons=tuple(reasons),
    )


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
    dual = completion_dual_exponent(box.h, box.sigma)
    return RouteResult(
        route="h_completion",
        applicable=False,
        saving=None,
        source="finite Poisson completion modulo s",
        reason="no_cited_completed_kernel_bound",
        conditions=(
            f"dual exponent max(0,sigma-h)={dual}",
            "rv congruent to delta modulo s",
            "coupled Fourier kernel retained",
        ),
    )


def delta_completion_adapter(box: ExponentBox) -> RouteResult:
    dual = completion_dual_exponent(box.ell, box.sigma)
    return RouteResult(
        route="delta_completion",
        applicable=False,
        saving=None,
        source="finite Poisson completion modulo s",
        reason="no_cited_completed_kernel_bound",
        conditions=(
            f"dual exponent max(0,sigma-ell)={dual}",
            "rh congruent to transformed delta frequency modulo s",
            "coupled Fourier kernel retained",
        ),
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


def farey_trilinear_adapter(box: ExponentBox) -> RouteResult:
    """Reduce a short signed shift window to one ``j`` per ``(r,s,v)``.

    This is an exact reindexing adapter, not the missing analytic estimate.
    It applies kinematically when ``L/S`` is a negative power of ``T``.
    """
    short_window = box.ell < box.sigma
    return RouteResult(
        route="mobius_farey_trilinear",
        applicable=False,
        saving=None,
        source=(
            "exact signed-j reindexing; new Farey estimate required"
        ),
        reason=(
            "new_farey_trilinear_estimate_required"
            if short_window
            else "shift_window_not_shorter_than_s"
        ),
        conditions=(
            "split positive and negative delta",
            "j unique after splitting the sign of delta",
            "retain all v in the coupled Fourier kernel",
            "preserve both Mobius weights",
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
    farey = farey_trilinear_adapter(box)
    if farey.reason == "new_farey_trilinear_estimate_required":
        return farey
    return RouteResult(
        route="global_coupled_operator",
        applicable=False,
        saving=None,
        source="new estimate required",
        reason="new_global_operator_estimate_required",
        conditions=(
            "sum v,j before absolute values",
            "preserve both Mobius weights",
            "retain delta=r*v-j*s and the Fourier kernel",
        ),
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
