#!/usr/bin/env python3
"""Exact zero-slack exponent ledger for the MWKF(3) reduction.

This module checks linear implications only.  It does not prove an
oscillatory-sum estimate or certify that an analytic truncation is valid.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction


@dataclass(frozen=True)
class ExponentBox:
    rho: Fraction
    sigma: Fraction
    m: Fraction
    k: Fraction
    ell: Fraction
    h: Fraction
    kappa: Fraction

    @property
    def third_length(self) -> Fraction:
        return self.ell + self.h


def admissibility_violations(box: ExponentBox) -> tuple[str, ...]:
    v: list[str] = []
    values = (
        box.rho, box.sigma, box.m, box.k,
        box.ell, box.h, box.kappa,
    )
    if any(value < 0 for value in values):
        v.append("nonnegative")
    if box.kappa + box.rho > 3:
        v.append("mollifier_r")
    if box.kappa + box.sigma > 3:
        v.append("mollifier_s")
    if box.k + box.m > 1:
        v.append("km_length")
    if box.k + box.sigma != box.m + box.rho:
        v.append("ratio_balance")
    if box.ell > box.m + box.rho - 1:
        v.append("delta_length")
    if box.h > box.sigma - box.m:
        v.append("frequency_length")
    if box.third_length > box.rho + box.sigma - 1:
        v.append("third_length")
    return tuple(v)


def is_admissible(box: ExponentBox) -> bool:
    return not admissibility_violations(box)


def derived_bounds(box: ExponentBox) -> dict[str, Fraction]:
    """Return the exact zero-slack bounds derived from the range polytope.

    The ``m_cap`` and ``k_cap`` formulas combine ``k + m <= 1`` with
    the exact ratio balance ``k + sigma = m + rho``.
    """
    half = Fraction(1, 2)
    return {
        "a": box.third_length,
        "a_cap": box.rho + box.sigma - 1,
        "m_cap": half * (1 + box.sigma - box.rho),
        "k_cap": half * (1 + box.rho - box.sigma),
    }


def boundary_witnesses() -> dict[str, ExponentBox]:
    F = Fraction
    return {
        "balanced_max_a": ExponentBox(F(3), F(3), F(1, 2), F(1, 2),
                                       F(5, 2), F(5, 2), F(0)),
        "r_long": ExponentBox(F(3), F(2), F(0), F(1),
                               F(2), F(2), F(0)),
        "s_long": ExponentBox(F(2), F(3), F(1), F(0),
                               F(2), F(2), F(0)),
        "large_q_endpoint": ExponentBox(F(1), F(1), F(0), F(0),
                                         F(0), F(1), F(2)),
    }


def main() -> None:
    fields = ("rho", "sigma", "m", "k", "ell", "h", "kappa")
    for name, box in sorted(boundary_witnesses().items()):
        violations = admissibility_violations(box)
        if violations:
            raise ValueError(f"{name}: {','.join(violations)}")
        bounds = derived_bounds(box)
        gap = bounds["a"] - (box.rho + box.sigma) / 2
        values = [f"{field}={getattr(box, field)}" for field in fields]
        values.extend((f"a={bounds['a']}",
                       f"a_minus_half_rho_sigma={gap}"))
        print(f"{name}: {' '.join(values)}")


if __name__ == "__main__":
    main()
