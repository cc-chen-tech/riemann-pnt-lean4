# Third-order zero-pole L-series bridge

## Result

The negative-left-edge contour identity is now attached to the genuine
second-smoothed Chebyshev function. For

    a < 0,    1 < c,    W > 0,

the corrected finite residue sum satisfies

    norm(
      residue sum
        - thirdOrderContourRemainder
        - secondSmoothedChebyshevPsi
    )
      <= explicit quadratic-height Perron error.

The residue set contains zero. Every nonzero zeta zero has coefficient

    -multiplicity(p) * x^p / p^3,

and the cubic zero-pole coefficient is

    -zeta'(0) / zeta(0).

## Significance

The earlier L-series bridge required a positive left boundary only because it
used the old rectangle formula. The right vertical Perron estimate itself
depends only on c > 1 and W > 0. Replacing the rectangle input by the
zero-pole-corrected contour identity removes that artificial obstruction.

This is the first theorem in this chain where the genuine second-smoothed PNT
object, the actual zeta residues, the negative-left-edge contour remainder,
and the explicit finite-height Perron error occur in one statement.

## Remaining zero correction

The simple residue at zero is retained as residue(0). The next local task is
to identify it as the quadratic Taylor coefficient of

    (-zeta'(s) / zeta(s)) * x^s

at s = 0, or at least prove the explicit polylogarithmic bound needed for
normalization. No Carlson tail, Omega theorem, or RH conclusion is claimed.
