#!/usr/bin/env python3
"""Exact finite ledgers for the coefficient-first ``zeta * M_N`` route.

Every returned dictionary represents a formal linear combination of
``log(p)`` over primes ``p``.  This avoids floating-point comparisons:
for example ``{5: -1, 7: 1}`` is exactly ``log(7/5)``.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import gcd
if __package__:
    from scripts.mwkf_mobius_type_identity import divisors, mobius
else:
    from mwkf_mobius_type_identity import divisors, mobius


FormalLog = dict[int, int]


@dataclass(frozen=True)
class RestrictedComplementaryDivisorPartition:
    """Exact four-piece partition on one critical complementary collar."""

    critical_collar: bool
    complete: FormalLog
    sparse_completion: FormalLog
    below_boundary_tail: FormalLog
    boundary_tail: FormalLog
    boundary_available: FormalLog
    above_boundary_available: FormalLog
    below_boundary_tail_divisors: tuple[int, ...]
    boundary_tail_divisors: tuple[int, ...]
    boundary_available_divisors: tuple[int, ...]
    above_boundary_available_divisors: tuple[int, ...]
    paired_boundary_plus_lower_tail: FormalLog
    unpaired_boundary_plus_upper: FormalLog
    complete_identity_holds: bool
    complete_matches_sparse_formula: bool
    pair_closes_completion: bool


@dataclass(frozen=True)
class CoefficientFirstScales:
    complete_lambda_region: Fraction
    product_support: Fraction
    euler_maclaurin_pole: Fraction


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


def _sum_formal_logs(*sources: FormalLog) -> FormalLog:
    result: FormalLog = {}
    for source in sources:
        _add_scaled(result, source, 1)
    return result


def _restricted_divisor_term(d: int, cutoff_x: int) -> FormalLog:
    result = formal_log(cutoff_x)
    _add_scaled(result, formal_log(d), -1)
    mu_d = mobius(d)
    if mu_d == 1:
        return result
    if mu_d == -1:
        return {prime: -exponent for prime, exponent in result.items()}
    return {}


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


def _q_free_part(n: int, modulus_q: int) -> int:
    result = 1
    for prime, exponent in _prime_factorization(n).items():
        if modulus_q % prime:
            result *= prime**exponent
    return result


def restricted_complementary_divisor_partition(
    n: int,
    *,
    cutoff_x: int,
    modulus_q: int,
    boundary_p: int,
) -> RestrictedComplementaryDivisorPartition:
    """Partition a restricted divisor completion on ``n/X in [P,2P]``.

    Write ``m=n/d`` and retain only ``(d,q)=1``.  The complete formal
    convolution is

    ``sum mu(d) * log(X/d)``.

    On the critical collar ``PX <= n <= 2PX``, every ``m<P`` term lies
    in the reflected tail ``d>X`` and every ``m>2P`` term is available
    in the truncated convolution ``d<=X``.  The remaining collar splits
    at ``d=X``.  This gives four disjoint pieces without an asymptotic or
    a floating-point logarithm.
    """
    _require_positive("n", n)
    _require_positive("cutoff_x", cutoff_x)
    _require_positive("modulus_q", modulus_q)
    _require_positive("boundary_p", boundary_p)
    critical_collar = (
        boundary_p * cutoff_x <= n
        and n <= 2 * boundary_p * cutoff_x
    )
    if not critical_collar:
        raise ValueError("n must lie in the critical collar [P*X,2*P*X]")

    complete: FormalLog = {}
    below_boundary_tail: FormalLog = {}
    boundary_tail: FormalLog = {}
    boundary_available: FormalLog = {}
    above_boundary_available: FormalLog = {}
    below_boundary_tail_divisors: list[int] = []
    boundary_tail_divisors: list[int] = []
    boundary_available_divisors: list[int] = []
    above_boundary_available_divisors: list[int] = []

    for d in divisors(n):
        if gcd(d, modulus_q) != 1:
            continue
        term = _restricted_divisor_term(d, cutoff_x)
        _add_scaled(complete, term, 1)
        complementary = n // d
        if complementary < boundary_p:
            if d <= cutoff_x:
                raise AssertionError("critical-collar lower term is available")
            _add_scaled(below_boundary_tail, term, 1)
            if mobius(d):
                below_boundary_tail_divisors.append(d)
        elif complementary <= 2 * boundary_p:
            available = d <= cutoff_x
            target = boundary_available if available else boundary_tail
            _add_scaled(target, term, 1)
            if mobius(d):
                divisors_target = (
                    boundary_available_divisors
                    if available
                    else boundary_tail_divisors
                )
                divisors_target.append(d)
        else:
            if d > cutoff_x:
                raise AssertionError("critical-collar upper term is in the tail")
            _add_scaled(above_boundary_available, term, 1)
            if mobius(d):
                above_boundary_available_divisors.append(d)

    paired = _sum_formal_logs(
        below_boundary_tail,
        boundary_available,
    )
    unpaired = _sum_formal_logs(
        boundary_tail,
        above_boundary_available,
    )
    reconstructed = _sum_formal_logs(paired, unpaired)
    q_free = _q_free_part(n, modulus_q)
    sparse_completion = (
        formal_log(cutoff_x)
        if q_free == 1
        else formal_von_mangoldt(q_free)
    )
    return RestrictedComplementaryDivisorPartition(
        critical_collar=critical_collar,
        complete=complete,
        sparse_completion=sparse_completion,
        below_boundary_tail=below_boundary_tail,
        boundary_tail=boundary_tail,
        boundary_available=boundary_available,
        above_boundary_available=above_boundary_available,
        below_boundary_tail_divisors=tuple(below_boundary_tail_divisors),
        boundary_tail_divisors=tuple(boundary_tail_divisors),
        boundary_available_divisors=tuple(boundary_available_divisors),
        above_boundary_available_divisors=tuple(
            above_boundary_available_divisors
        ),
        paired_boundary_plus_lower_tail=paired,
        unpaired_boundary_plus_upper=unpaired,
        complete_identity_holds=reconstructed == complete,
        complete_matches_sparse_formula=(complete == sparse_completion),
        pair_closes_completion=unpaired == {},
    )


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
