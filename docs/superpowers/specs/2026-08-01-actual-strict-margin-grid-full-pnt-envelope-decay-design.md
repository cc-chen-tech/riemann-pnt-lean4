# Actual Strict-Margin Grid Full-PNT Envelope Decay

## Objective

Close the analytic convergence gap left after Stack133. The actual strict-margin
grid already dominates the real relative Chebyshev error; this slice proves
that the displayed concrete majorant itself tends to zero.

## Theorem chain

1. Export `pntSqrtLog m / m -> 0` on natural points.
2. Combine it with the closed-log and real-axis limits to prove decay of
   `actualStrictMarginRateIndependentResidual`.
3. Split the full envelope into its degree-four contour term, degree-two finite
   zero term, and residual. Positive strict target rate makes both exponential
   terms tend to zero.
4. Reuse Stack133 to package, for every `q > 1`, the actual grid identities,
   the `1 / q` optimal-rate lower guarantee, majorant convergence, and eventual
   domination of the real PNT error.

## Claim boundary

This proves convergence of a concrete unconditional PNT upper majorant already
obtained from the classical zero-free input. It does not reach the non-strict
endpoint, improve Carlson constants, prove an Omega theorem, or imply RH.
