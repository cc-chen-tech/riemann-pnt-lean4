"""Finite checks for the physical shifted-frequency adapter (SF1--SF19).

These helpers verify arithmetic phases and literal lattice axes only.
The finite periodic transform is not the continuous canonical zero mode:
each of its frequency classes includes all continuous Fourier aliases.
No continuous Poisson, Mellin contour, or analytic saving is certified here.
"""

from __future__ import annotations

import cmath
from fractions import Fraction
from math import gcd, pi
from typing import Mapping


def _coprime_slopes(r: int, s: int) -> None:
    if type(r) is not int or type(s) is not int or min(r, s) < 1 or gcd(r, s) != 1:
        raise ValueError("r,s must be positive coprime integers")


def _integer_pair(pair, *, positive: bool = False) -> None:
    if (not isinstance(pair, tuple) or len(pair) != 2
            or any(type(n) is not int for n in pair)
            or (positive and min(pair) < 1)):
        raise ValueError("coordinates must be integer pairs, positive on the zeta lattice")


def _e(phase: Fraction) -> complex:
    return cmath.exp(2j*pi*float(phase % 1))


def completion_frequency_transport(r: int, s: int, nu: int, omega: int) -> dict:
    """Exact signed-modulus phase/Jacobian data; m=1 keeps arbitrary nu,omega."""
    _coprime_slopes(r, s)
    _integer_pair((nu, omega))
    if r == s:
        raise ValueError("the short-modulus completion requires r != s")
    b, m = r-s, abs(r-s)
    sign = 1 if b > 0 else -1
    beta = pow(s, -1, m) if m > 1 else 0
    gauss_phase = Fraction(-s*nu*omega, b)
    # Fourier inversion samples x=-delta/b-s*xi; its Jacobian is s*abs(b).
    inversion_constant = Fraction(omega*b*s*nu, m*m)
    return {
        "signed_modulus": b,
        "modulus": m,
        "beta": beta,
        "bezout_cofactor": (1-s*beta)//b,
        "gauss_phase": gauss_phase % 1,
        "combined_constant_phase": (gauss_phase+inversion_constant) % 1,
        "jacobian": s*m,
        "shift": -sign*nu,
        "lattice_frequency": sign*omega,
    }


def finite_completion_axis_sides(
    r: int, s: int, values: Mapping[tuple[int, int], complex]
) -> dict:
    """Finite periodization of SF3/SF7, retaining *literal* h=0,delta=0 axes.

    values supplies psi, after the rational chirp in SF2. All finite support
    points, including negative points and repeated residue classes, remain.
    Transform frequencies here are residue classes, not individual continuous
    Fourier frequencies from SF4. Their zero class is not the canonical Gram.
    """
    base = completion_frequency_transport(r, s, 0, 0)
    for pair in values:
        _integer_pair(pair)
    b, m, beta = base["signed_modulus"], base["modulus"], base["beta"]
    direct = sum(value*_e(Fraction(beta*h*delta, b))
                 for (h, delta), value in values.items())
    completed = 0j
    for nu in range(m):
        for omega in range(m):
            transform = sum(value*_e(Fraction(-nu*h-omega*delta, m))
                            for (h, delta), value in values.items())
            completed += _e(Fraction(-s*nu*omega, b))*transform/m
    h_axis = sum(value for (h, _delta), value in values.items() if h == 0)
    delta_axis = sum(value for (_h, delta), value in values.items() if delta == 0)
    origin = values.get((0, 0), 0)
    nonaxes_direct = sum(value*_e(Fraction(beta*h*delta, b))
                         for (h, delta), value in values.items() if h and delta)
    return {
        "direct": direct,
        "completed": completed,
        "h_axis": h_axis,
        "delta_axis": delta_axis,
        "origin": origin,
        "nonaxes_direct": nonaxes_direct,
        "nonaxes_completed": completed-h_axis-delta_axis+origin,
    }


def integer_shift_axis_partition(
    r: int, s: int, values: Mapping[tuple[int, int], complex]
) -> dict:
    """Partition a finite physical (n,m1) lattice by j=m1-n and delta=m1*s-n*r.

    This also accepts r=s=1: no short-modulus division is used. In that case
    the two axes coincide; for r!=s their positive-lattice intersection is empty.
    Values may be rational, and no floating-point conversion is performed.
    """
    _coprime_slopes(r, s)
    shift_sums = {}
    for pair, value in values.items():
        _integer_pair(pair, positive=True)
        n, m1 = pair
        shift_sums[m1-n] = shift_sums.get(m1-n, 0)+value
    afe = tuple(sorted(pair for pair in values if pair[1]*s == pair[0]*r))
    equal = tuple(sorted(pair for pair in values if pair[0] == pair[1]))
    return {
        "full": sum(values.values()),
        "shift_sums": shift_sums,
        "afe_points": afe,
        "equal_zeta_points": equal,
        "afe_diagonal": sum(values[pair] for pair in afe),
        "equal_zeta": sum(values[pair] for pair in equal),
        "axis_intersection": sum(values[pair] for pair in set(afe) & set(equal)),
        "off_both_axes": sum(value for (n, m1), value in values.items()
                             if m1 != n and m1*s != n*r),
    }
