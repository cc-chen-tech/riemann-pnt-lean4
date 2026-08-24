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
