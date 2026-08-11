# Third-order zero-pole contour identity

## Result

The zero-pole-corrected rectangle formula is converted to the scaled
right-edge identity used by the Perron bridge. For

    a < 0 < c,    W > 0,

the genuine third-order right-edge integral satisfies

    right integral
      = sum(corrected residues)
      - thirdOrderContourRemainder(x, a, c, W).

The finite residue set contains zero. Every nonzero zeta zero retains the
coefficient

    -multiplicity(p) * x^p / p^3,

and the cubic zero-pole coefficient remains

    -zeta'(0) / zeta(0).

## Role in the unified route

The dynamic contour theorem already proves decay for the genuine remainder
with the fixed left edge a = -1 and dynamic selected heights. This identity
puts that exact remainder into the same equation as the corrected residue
sum and the right vertical L-series integral.

No new contour estimate is introduced here; the proof is the scaled vertical
change of variables and algebraic rearrangement of the zero-pole rectangle
formula.

## Scope

This slice does not yet identify the simple zero residue explicitly or turn
the corrected residue sum into a closed formula for the second-smoothed
Chebyshev function. It also does not bound Carlson tails, prove an Omega
theorem, or imply RH.
