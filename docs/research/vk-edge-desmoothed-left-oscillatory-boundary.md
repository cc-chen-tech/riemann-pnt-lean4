# Dynamic-left oscillatory contour boundary

## Closed result

The actual Riemann-zeta logarithmic derivative and its derivative are now
controlled on one shared dynamic left boundary.  On every positive high-height
subinterval, the desmoothed cubic contour integral satisfies a total-variation
integration-by-parts bound with a full reciprocal `Real.log x` gain and only a
logarithmic endpoint-ratio loss.

The final endpoint is
`exists_dynamicCubicLeftBoundary_positive_interval_oscillatory_bound`.  It has
no abstract coefficient or model-polynomial assumption.  Its remaining inputs
are the interval geometry and the desmoothing condition `h * H <= 1 / 2`.

## What this removes

The previous pointwise estimate would have produced an unacceptable factor
proportional to the full contour height.  Integrating the reciprocal-height
derivative majorant instead gives a `Real.log (v / u)` total-variation cost.
This closes the positive high-height part of the dynamic left-edge contour
budget needed by the two-height explicit-formula route.

## What remains open

- The negative high-height interval must be instantiated with matching
  orientation and witnesses.
- Positive and negative pieces must be combined with the already formalized
  low segment and horizontal contour budgets.
- No theorem here proves residual energy after deleting an arbitrary finite
  recorded zero set `S`.
- No cofinal `S`-relative Sharp lower bound, Carlson contradiction, zero
  exclusion, or Riemann Hypothesis conclusion follows from this module alone.
