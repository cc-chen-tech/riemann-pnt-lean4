# Variable-Boundary Visible Carlson Tail

## Problem

The fixed-boundary dominated-tail theorem sums over every Carlson zero. Its
summable weight majorant therefore needs a global inequality `Re rho <= beta`.
For a finite-height right edge `beta(x)`, invisible higher zeros need not obey
the current boundary and destroy that domination.

## Design

Define a visible term that is zero unless `|Im rho| <= H(m)`. If visible, delete
the zero when it belongs to the complete package on `Re rho = beta(m)`;
otherwise normalize it by `m^(beta(m)-1)`.

Two conditions suffice:

- pointwise visible right edge: every visible indexed zero has
  `Re rho <= beta(m)`;
- absorption-or-gap: every fixed indexed zero is eventually in the boundary
  package or satisfies `Re rho <= beta(m) - delta` for one fixed `delta > 0`.

The first condition bounds every visible normalized term by its summable
Carlson reciprocal-norm weight. The second bounds each fixed term by
`weight * m^(-delta)`, giving pointwise decay. Tannery dominated convergence
then proves that the complete visible weighted tail tends to zero.

Finally, the exact Pintz kernel identity identifies this weighted model with
the sum of norms of the currently visible actual zeta kernels normalized by
the variable target amplitude.

## Claim boundary

This proves the variable-beta high-tail estimate under absorption-or-gap. It
does not yet derive absorption-or-gap from a concrete monotone finite-height
maximum schedule, control low Carlson strips or contour remainder, construct
the moving-package witness, prove simultaneous signs, or imply RH.
