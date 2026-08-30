"""Exact scale changes and finite complementary-divisor boundaries.

These routines do not certify smoothness of a physical packet or an
analytic estimate. See the RP note for the separate theorem hypotheses.
"""

from fractions import Fraction as F
from math import ceil, floor


def reciprocal_scales(R, S, A, e, r, j, kl):
    """The quotient Poisson factor is Uhat(m*R/(A*s)), with R <= S.

    R, S and A are positive dyadic scales (no squarefreeness is inferred).
    e and r are positive cofactor parameters. Phase sign is included in
    phase_numerator, so the exponential is e(phase_numerator/n).
    """
    R, S, A, e, r, j, kl = map(F, (R, S, A, e, r, j, kl))
    if min(R, S, A, e, r) <= 0 or R > S:
        raise ValueError("positive scales with entry scale R <= modulus scale S required")
    M = A * S / R
    D, X = S / e, S / (e * r)
    prefactor = M / (r*r*e*e)
    return {
        "ratio": S / R,
        "M": M,
        "D": D,
        "X": X,
        "mode_scale": D / M,
        "lambda": j * M / D,
        "phase_numerator": -j * A * kl / r,
        "poisson_prefactor": prefactor,
        "outer_per_mode": prefactor / (X * A),
    }


def complementary_interval_ledger(D, r, M, Z):
    """Count D <= r*n <= 2D, |r*n*c-Z| <= M, n>0, c!=0.

    All endpoints are inclusive. No Mobius sign or coprimality is added;
    the resulting positive bound also majorizes any bounded masked sum.
    This is a finite verification helper; its runtime grows with D/r.
    """
    D, r, M, Z = map(F, (D, r, M, Z))
    if D <= 0 or r <= 0 or M < 0:
        raise ValueError("D and r must be positive; M must be nonnegative")
    pairs, weighted = 0, F(0)
    for n in range(max(1, ceil(D / r)), floor(2*D / r) + 1):
        lo, hi = ceil((Z-M) / (r*n)), floor((Z+M) / (r*n))
        count = max(0, hi-lo+1) - int(lo <= 0 <= hi)
        pairs += count
        weighted += F(count) / (r*n)
    C = floor((abs(Z) + M) / D)
    harmonic = sum((F(1, c) for c in range(1, C+1)), F(0))
    return {
        "pair_count": pairs,
        "weighted_count": weighted,
        "c_cutoff": C,
        "continuous_part": 4*M*harmonic / (r*D),
        "boundary_part": 2*F(C) / D,
    }


def cubic_window_margin(u, a):
    """Taylor margin only, on 1/2 <= u <= 3, 0 <= a <= 2u-1.

    The external MRSTT theorem and the physical transfer are not tested
    by positivity of this rational number.
    """
    u, a = F(u), F(a)
    if not F(1, 2) <= u <= 3 or not 0 <= a <= 2*u-1:
        raise ValueError("outside the declared necessary polytope inequalities")
    eta, rho, nu = F(1, 1000), F(1, 1000), F(17, 50)
    x = (u-eta) * (1-rho)
    return 4*(1-nu)*x - (2*u-a) - eta
