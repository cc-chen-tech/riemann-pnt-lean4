#!/usr/bin/env python3
"""Exact finite ledgers for the coefficient-first ``zeta * M_N`` route.

Every returned dictionary represents a formal linear combination of
``log(p)`` over primes ``p``.  This avoids floating-point comparisons:
for example ``{5: -1, 7: 1}`` is exactly ``log(7/5)``.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
if __package__:
    from scripts.mwkf_mobius_type_identity import divisors, mobius
else:
    from mwkf_mobius_type_identity import divisors, mobius


FormalLog = dict[int, int]


@dataclass(frozen=True)
class CoefficientFirstScales:
    complete_lambda_region: Fraction
    product_support: Fraction
    euler_maclaurin_pole: Fraction


@dataclass(frozen=True)
class PartialDiagonalCoefficientFirstAudit:
    mollifier_exponent: Fraction
    zeta_cutoff_exponent: Fraction
    product_exponent: Fraction
    complete_von_mangoldt_region: Fraction
    available_divisor_min_exponent: Fraction
    available_divisor_max_exponent: Fraction
    omitted_small_divisor_ceiling_exponent: Fraction
    product_below_mollifier_cutoff: bool
    finite_zeta_cofactor_boundary_active: bool
    mollifier_upper_boundary_active: bool
    pure_von_mangoldt_replacement_valid: bool
    large_mobius_divisor_tail_retained: bool
    boundary_correction_required: bool


@dataclass(frozen=True)
class ZeroRouteAudit:
    zero_residue_amplification: Fraction
    origin_interval_zero_free_boundary: Fraction
    dyadic_interval_zero_free_boundary: Fraction
    bettin_gonek_applicable: bool
    reason: str


def coefficient_first_scales(
    *,
    mollifier_exponent: Fraction,
    zeta_cutoff_exponent: Fraction,
) -> CoefficientFirstScales:
    """Return the exact power ledger for a finite zeta convolution.

    If ``N=T^n`` and ``X=T^x``, the coefficient of
    ``(sum_{m<=X}m^-s) M_N(s)`` has complete divisor convolution only up
    to ``T^min(n,x)`` and support up to ``T^(n+x)``.  The elementary
    Euler--Maclaurin pole correction ``X^(1-s)/(s-1)`` has size exponent
    ``x/2-1`` on ``s=1/2+it``, ``t \\asymp T``.
    """
    if mollifier_exponent < 0 or zeta_cutoff_exponent < 0:
        raise ValueError("length exponents must be nonnegative")
    return CoefficientFirstScales(
        complete_lambda_region=min(
            mollifier_exponent, zeta_cutoff_exponent
        ),
        product_support=mollifier_exponent + zeta_cutoff_exponent,
        euler_maclaurin_pole=zeta_cutoff_exponent / 2 - 1,
    )


def partial_diagonal_coefficient_first_audit(
    *,
    mollifier_exponent: Fraction,
    zeta_cutoff_exponent: Fraction,
    product_exponent: Fraction,
) -> PartialDiagonalCoefficientFirstAudit:
    """Audit one product exponent inside the finite zeta convolution.

    For ``u=T^p``, ``N=T^n`` and a finite zeta factor ``m<=T^x``, a
    factorization ``u=d*m`` is visible only when

    ``p-x <= log_T(d) <= min(p,n)``.

    Thus products above the complete range ``min(n,x)`` retain a truncated
    Möbius divisor tail rather than the pure ``Lambda(u)/log(N)``
    coefficient.  This is an exponent ledger only; endpoint constants stay
    in the exact finite divisor conditions.  In particular, it does not
    identify a synthetic BBLR product coefficient with this finite
    ``zeta * M_N`` coefficient.
    """

    n_exp = Fraction(mollifier_exponent)
    x_exp = Fraction(zeta_cutoff_exponent)
    p_exp = Fraction(product_exponent)
    if min(n_exp, x_exp, p_exp) < 0:
        raise ValueError("coefficient-first exponents must be nonnegative")
    if p_exp > n_exp + x_exp:
        raise ValueError("the product lies outside the finite convolution support")

    complete_region = min(n_exp, x_exp)
    available_min = max(Fraction(0), p_exp - x_exp)
    available_max = min(p_exp, n_exp)
    pure_lambda = p_exp <= complete_region
    finite_zeta_boundary = p_exp > x_exp
    mollifier_boundary = p_exp > n_exp
    return PartialDiagonalCoefficientFirstAudit(
        mollifier_exponent=n_exp,
        zeta_cutoff_exponent=x_exp,
        product_exponent=p_exp,
        complete_von_mangoldt_region=complete_region,
        available_divisor_min_exponent=available_min,
        available_divisor_max_exponent=available_max,
        omitted_small_divisor_ceiling_exponent=available_min,
        product_below_mollifier_cutoff=(p_exp <= n_exp),
        finite_zeta_cofactor_boundary_active=finite_zeta_boundary,
        mollifier_upper_boundary_active=mollifier_boundary,
        pure_von_mangoldt_replacement_valid=pure_lambda,
        large_mobius_divisor_tail_retained=(
            finite_zeta_boundary and available_min < available_max
        ),
        boundary_correction_required=(not pure_lambda),
    )


def zero_route_audit(
    *,
    mollifier_exponent: Fraction,
    zero_real_part: Fraction,
    all_lengths_up_to_cutoff: bool,
) -> ZeroRouteAudit:
    """Audit the Perron zero factor and Bettin--Gonek length scope.

    In the ratio integral for ``zeta(s) M_N(s)``, a zero ``rho`` produces
    ``N^(rho-s)``.  At ``Re(s)=1/2`` and ``N=T^theta`` its power exponent is
    ``theta*(Re(rho)-1/2)``.  Bettin--Gonek Theorems 1 and 2 instead assume
    the moment bound for every ``2 <= N <= T^theta``; a result only at the
    endpoint length does not meet that hypothesis.
    """
    if mollifier_exponent <= 0:
        raise ValueError("mollifier_exponent must be positive")
    if zero_real_part < 0 or zero_real_part > 1:
        raise ValueError("zero_real_part must lie in [0,1]")
    applicable = all_lengths_up_to_cutoff
    return ZeroRouteAudit(
        zero_residue_amplification=(
            mollifier_exponent * (zero_real_part - Fraction(1, 2))
        ),
        origin_interval_zero_free_boundary=(
            Fraction(1, 2) + Fraction(1, 2) / mollifier_exponent
        ),
        dyadic_interval_zero_free_boundary=(
            Fraction(1, 2) + Fraction(2) / mollifier_exponent
        ),
        bettin_gonek_applicable=applicable,
        reason=(
            "all_lengths_scope_satisfied"
            if applicable
            else "requires_all_lengths_up_to_T_theta"
        ),
    )


def _require_positive(name: str, value: int) -> None:
    if value < 1:
        raise ValueError(f"{name} must be positive")


def _prime_factorization(n: int) -> dict[int, int]:
    _require_positive("n", n)
    factors: dict[int, int] = {}
    value = n
    prime = 2
    while prime * prime <= value:
        while value % prime == 0:
            factors[prime] = factors.get(prime, 0) + 1
            value //= prime
        prime += 1
    if value > 1:
        factors[value] = factors.get(value, 0) + 1
    return factors


def _add_scaled(target: FormalLog, source: FormalLog, scale: int) -> None:
    for prime, exponent in source.items():
        new_exponent = target.get(prime, 0) + scale * exponent
        if new_exponent:
            target[prime] = new_exponent
        else:
            target.pop(prime, None)


def formal_log(n: int) -> FormalLog:
    """Return the exact prime-vector representing ``log(n)``."""
    return _prime_factorization(n)


def formal_von_mangoldt(n: int) -> FormalLog:
    """Return the prime-vector representing ``Lambda(n)``."""
    factors = _prime_factorization(n)
    if len(factors) != 1:
        return {}
    prime = next(iter(factors))
    return {prime: 1}


def missing_convolution_divisors(
    n: int,
    *,
    cutoff_n: int,
    cutoff_x: int | None = None,
) -> tuple[int, ...]:
    """Divisors omitted from the complete Dirichlet convolution.

    ``cutoff_n`` is the mollifier cutoff.  When ``cutoff_x`` is supplied,
    the zeta factor is the finite polynomial ``sum_{m<=X} m^{-s}``, so a
    factorization ``n=d*m`` is present exactly when ``d<=N`` and ``m<=X``.
    """
    _require_positive("n", n)
    _require_positive("cutoff_n", cutoff_n)
    if cutoff_x is not None:
        _require_positive("cutoff_x", cutoff_x)
    return tuple(
        d
        for d in divisors(n)
        if d > cutoff_n or (cutoff_x is not None and n // d > cutoff_x)
    )


def _scaled_available_coefficient(
    n: int,
    *,
    cutoff_n: int,
    cutoff_x: int | None,
) -> FormalLog:
    result: FormalLog = {}
    log_n_cutoff = formal_log(cutoff_n)
    for d in divisors(n):
        if d > cutoff_n:
            continue
        if cutoff_x is not None and n // d > cutoff_x:
            continue
        mu_d = mobius(d)
        _add_scaled(result, log_n_cutoff, mu_d)
        _add_scaled(result, formal_log(d), -mu_d)
    return result


def scaled_zeta_mollifier_coefficient(n: int, cutoff_n: int) -> FormalLog:
    """Return ``log(N) * b_N(n)`` for the formal product ``zeta M_N``."""
    return _scaled_available_coefficient(
        n, cutoff_n=cutoff_n, cutoff_x=None
    )


def scaled_truncated_product_coefficient(
    n: int,
    *,
    cutoff_n: int,
    cutoff_x: int,
) -> FormalLog:
    """Return the scaled coefficient of ``zeta_X(s) M_N(s)`` exactly."""
    return _scaled_available_coefficient(
        n, cutoff_n=cutoff_n, cutoff_x=cutoff_x
    )


def scaled_boundary_correction(
    n: int,
    *,
    cutoff_n: int,
    cutoff_x: int | None = None,
) -> FormalLog:
    """Return the exact correction to ``Lambda(n)`` from omitted divisors.

    For ``n>1`` this is

    ``sum_missing mu(d) * (log(d) - log(N))``.

    Hence the available scaled coefficient is ``Lambda(n)`` plus this
    correction.  The unit coefficient is handled separately.
    """
    result: FormalLog = {}
    log_n_cutoff = formal_log(cutoff_n)
    for d in missing_convolution_divisors(
        n, cutoff_n=cutoff_n, cutoff_x=cutoff_x
    ):
        mu_d = mobius(d)
        _add_scaled(result, formal_log(d), mu_d)
        _add_scaled(result, log_n_cutoff, -mu_d)
    return result


def coefficient_region(
    n: int,
    cutoff_n: int,
    cutoff_x: int | None = None,
) -> str:
    """Classify the unit, complete-von-Mangoldt, and boundary regions."""
    _require_positive("n", n)
    if n == 1:
        return "unit"
    missing = missing_convolution_divisors(
        n, cutoff_n=cutoff_n, cutoff_x=cutoff_x
    )
    return "von_mangoldt" if not missing else "boundary"
