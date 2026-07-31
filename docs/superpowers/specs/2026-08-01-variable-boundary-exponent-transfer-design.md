# Variable-Boundary Exponent Transfer

## Problem

The existing dynamic-boundary chain varies the truncation height `H(x)` but
keeps the boundary real part `beta` fixed. Consequently it cannot model a
finite-height right edge that approaches a supremum without attaining it.

## Design

Introduce a genuine boundary schedule `beta : R -> R` and define the actual
package

`equalRealPartZeroPackage (H x) (beta x)`.

The pointwise right-edge predicate requires every visible positive-ordinate
zero to satisfy `Re rho <= beta x`; zeros outside the complete boundary package
then lie strictly left of `beta x`.

Use the variable target amplitude

`targetZeroPowerAmplitude (beta x) x = x^(beta x - 1)`.

The explicit formula decomposes around the moving package exactly. If the
remaining actual residual is negligible relative to this variable amplitude
and the package supplies an unsigned arbitrarily-far witness with coefficient
`c`, the generic sign alternative and one-sided transfer produce one
persistent sign with every fixed loss `0 < loss < c`.

Finally, multiplication by the positive sample point proves the exact identity

`x * x^(beta x - 1) = x^(beta x)`

and transfers the result to `chebyshevPsi0(x) - x`.

## Claim boundary

This PR removes the fixed-exponent restriction from the transfer machine. It
does not yet prove the variable-scale Carlson residual estimate or construct
the moving-package witness. Those are now the two precise analytic gaps. It
proves `Omega+ OR Omega-` only when both inputs are supplied, not simultaneous
signs and not RH.
