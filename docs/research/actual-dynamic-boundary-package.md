# Dynamic boundary packages for actual zeta zeros

## Purpose

A fixed equal-real-part zero package cannot satisfy the strict Carlson
threshold setup when another positive-ordinate zero with the same real part
appears above the package height.  The package must therefore move with the
selected height.

`dynamicEqualRealPartZeroPackage H beta x` contains the positive nontrivial
zeta zeros visible up to height `H x` whose real part equals `beta`.

## Verified declarations

The module proves:

- every currently visible positive zero with real part `beta` belongs to the
  dynamic package;
- every currently visible positive zero outside the package has real part
  different from `beta`;
- under the pointwise right-edge assumption `z.re <= beta`, every such outside
  zero has `z.re < beta`;
- a finite family lying strictly below `beta` admits a positive uniform gap;
- consequently, at each fixed scale there is a positive `delta` for which all
  visible outside zeros satisfy `z.re <= beta - delta`;
- the relative Chebyshev error has the exact pointwise decomposition into the
  dynamic boundary package main term and the actual explicit-formula
  residuals.

## Mathematical boundary

The resulting gap is pointwise and height-dependent.  The theorem does not
yet control how quickly the gap may shrink as the selected height grows.
Therefore it does not by itself prove that the complementary zero sum is
negligible after normalization by `x^(beta - 1)`.

The next required statement is an exponent budget relating the dynamic gap,
the selected height, and the Carlson density exponent.  No unconditional
Omega theorem or Riemann-hypothesis consequence is claimed here.
