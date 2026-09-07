#!/usr/bin/env python3
"""Exact zero-slack exponent ledger for the MWKF(3) reduction.

This module checks linear implications only.  It does not prove an
oscillatory-sum estimate or certify that an analytic truncation is valid.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations


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


def _reduced_polytope_inequalities(
) -> tuple[tuple[str, tuple[Fraction, ...], Fraction], ...]:
    """Return the exact six-dimensional H-representation.

    The coordinate order is ``(rho, sigma, m, ell, h, kappa)`` and the
    ratio equality has been eliminated by

    ``k = m + rho - sigma``.

    Every returned row means ``coefficient dot coordinate <= bound``.
    These are exactly the constraints checked by
    :func:`admissibility_violations`, with no numerical tolerance.
    """
    F = Fraction
    return (
        ("rho_nonnegative", (F(-1), F(0), F(0), F(0), F(0), F(0)), F(0)),
        ("sigma_nonnegative", (F(0), F(-1), F(0), F(0), F(0), F(0)), F(0)),
        ("m_nonnegative", (F(0), F(0), F(-1), F(0), F(0), F(0)), F(0)),
        ("ell_nonnegative", (F(0), F(0), F(0), F(-1), F(0), F(0)), F(0)),
        ("h_nonnegative", (F(0), F(0), F(0), F(0), F(-1), F(0)), F(0)),
        ("kappa_nonnegative", (F(0), F(0), F(0), F(0), F(0), F(-1)), F(0)),
        ("k_nonnegative", (F(-1), F(1), F(-1), F(0), F(0), F(0)), F(0)),
        ("mollifier_r", (F(1), F(0), F(0), F(0), F(0), F(1)), F(3)),
        ("mollifier_s", (F(0), F(1), F(0), F(0), F(0), F(1)), F(3)),
        ("km_length", (F(1), F(-1), F(2), F(0), F(0), F(0)), F(1)),
        ("delta_length", (F(-1), F(0), F(-1), F(1), F(0), F(0)), F(-1)),
        ("frequency_length", (F(0), F(-1), F(1), F(0), F(1), F(0)), F(0)),
        ("third_length", (F(-1), F(-1), F(0), F(1), F(1), F(0)), F(-1)),
    )


def _solve_fraction_square_system(
    coefficients: tuple[tuple[Fraction, ...], ...],
    right_hand_side: tuple[Fraction, ...],
) -> tuple[Fraction, ...] | None:
    """Solve a square rational system, returning ``None`` if singular."""
    dimension = len(coefficients)
    if dimension == 0 or len(right_hand_side) != dimension:
        raise ValueError("the system must be nonempty and square")
    if any(len(row) != dimension for row in coefficients):
        raise ValueError("the system must be square")

    matrix = [
        [Fraction(value) for value in row] + [Fraction(rhs)]
        for row, rhs in zip(coefficients, right_hand_side)
    ]
    for column in range(dimension):
        pivot = next(
            (row for row in range(column, dimension)
             if matrix[row][column] != 0),
            None,
        )
        if pivot is None:
            return None
        matrix[column], matrix[pivot] = matrix[pivot], matrix[column]
        pivot_value = matrix[column][column]
        matrix[column] = [value / pivot_value for value in matrix[column]]
        for row in range(dimension):
            if row == column:
                continue
            multiple = matrix[row][column]
            if multiple == 0:
                continue
            matrix[row] = [
                value - multiple * pivot_entry
                for value, pivot_entry in zip(matrix[row], matrix[column])
            ]
    return tuple(matrix[row][-1] for row in range(dimension))


def admissible_polytope_strict_interior_witness() -> ExponentBox:
    """Return a rational point strict in all thirteen half-spaces.

    This certifies that, after eliminating the ratio equality, the
    admissible polytope is genuinely six-dimensional rather than lying
    in a hidden affine hyperplane.
    """
    F = Fraction
    box = ExponentBox(
        rho=F(2),
        sigma=F(2),
        m=F(1, 4),
        k=F(1, 4),
        ell=F(1, 2),
        h=F(1, 2),
        kappa=F(1, 2),
    )
    coordinates = (
        box.rho, box.sigma, box.m, box.ell, box.h, box.kappa,
    )
    if not all(
        sum((coefficient * value for coefficient, value in zip(row, coordinates)),
            F(0)) < bound
        for _, row, bound in _reduced_polytope_inequalities()
    ):
        raise AssertionError("the advertised interior witness is not strict")
    return box


def admissible_polytope_vertices() -> tuple[ExponentBox, ...]:
    """Enumerate every vertex of the zero-slack exponent polytope.

    After eliminating the ratio equality the polytope has six
    coordinates and thirteen closed half-spaces.  A vertex is the
    unique intersection of six linearly independent active supporting
    hyperplanes.  We enumerate all ``13 choose 6`` candidates, solve
    them over :class:`fractions.Fraction`, reject candidates outside any
    half-space, and deduplicate intersections with more than six active
    constraints.  No floating-point grid or tolerance enters the result.
    """
    inequalities = _reduced_polytope_inequalities()
    # Fail loudly if a future constraint edit introduces a hidden affine
    # equality and invalidates the six-active-hyperplane enumeration.
    admissible_polytope_strict_interior_witness()
    dimension = 6
    vertices: set[ExponentBox] = set()
    for active in combinations(inequalities, dimension):
        solution = _solve_fraction_square_system(
            tuple(row for _, row, _ in active),
            tuple(bound for _, _, bound in active),
        )
        if solution is None:
            continue
        if any(
            sum((coefficient * value for coefficient, value in zip(row, solution)),
                Fraction(0)) > bound
            for _, row, bound in inequalities
        ):
            continue
        rho, sigma, m, ell, h, kappa = solution
        box = ExponentBox(
            rho=rho,
            sigma=sigma,
            m=m,
            k=m + rho - sigma,
            ell=ell,
            h=h,
            kappa=kappa,
        )
        if not is_admissible(box):
            raise AssertionError("H-representation and admissibility disagree")
        vertices.add(box)

    fields = ("rho", "sigma", "m", "k", "ell", "h", "kappa")
    return tuple(sorted(vertices, key=lambda box: tuple(
        getattr(box, field) for field in fields
    )))


def derived_bounds(box: ExponentBox) -> dict[str, Fraction]:
    """Return the linear bounds forced by the zero-slack polytope.

    The ``m_cap`` and ``k_cap`` identities combine ``k + m <= 1`` with
    ``k + sigma = m + rho``.  This is exact rational algebra only.
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


def _format_fraction(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def main() -> None:
    fields = ("rho", "sigma", "m", "k", "ell", "h", "kappa")
    for name, box in sorted(boundary_witnesses().items()):
        values = " ".join(
            f"{field}={_format_fraction(getattr(box, field))}"
            for field in fields
        )
        gap = box.third_length - (box.rho + box.sigma) / 2
        print(
            f"{name}: {values} a={_format_fraction(box.third_length)} "
            f"a_minus_half_rs={_format_fraction(gap)}"
        )


if __name__ == "__main__":
    main()
