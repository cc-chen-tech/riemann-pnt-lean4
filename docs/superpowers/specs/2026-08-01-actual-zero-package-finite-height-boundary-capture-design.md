# Actual Zero-Package Finite-Height Boundary Capture

## Objective

Turn the existing finite target-line Carlson capture into a genuine
`equalRealPartZeroPackage T beta` with arbitrarily small outside boundary mass.

## Construction

For a finite target-line seed `S`, choose

`T = sum (rho in S) |Im rho|`.

Every member ordinate is at most this nonnegative sum, so `S` is contained in
the actual height package. For a requested `epsilon > 0`, first invoke the
target-line selector with `c = 2 * epsilon` and `q = 0`; it returns a finite
target-line extension `S` with `2 * outsideMass(S) < 2 * epsilon`.

Embed `S` into its height package. Boundary mass is antitone under cluster
enlargement, so the package outside mass remains below `epsilon`. The original
global real-part cap also transfers to the larger package.

## Claim boundary

The theorem assumes a finite target-line seed and its global outside
real-part cap. It does not assert existence of a rightmost zero, RH, energy
positivity, or signed oscillation.
