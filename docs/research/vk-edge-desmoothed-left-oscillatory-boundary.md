# Dynamic-left oscillatory contour boundary

## Closed result

The actual Riemann-zeta logarithmic derivative and its derivative are now
controlled on one shared dynamic left boundary. On every positive or negative
high-height subinterval, the desmoothed cubic contour integral satisfies a
total-variation integration-by-parts bound with a full reciprocal `Real.log x`
gain and only a logarithmic endpoint-ratio loss.

The endpoint
`exists_dynamicCubicLeftBoundary_negative_interval_oscillatory_bound` closes
the negative interval with exactly the same constant as the previously proved
positive endpoint. The theorem
`norm_add_intervalIntegral_desmoothedCubicLeftContourIntegrand_le` combines the
two actual-zeta pieces with only the triangle-inequality factor two. These
results have no abstract coefficient or model-polynomial assumption.

## What this removes

The previous pointwise estimate would have produced an unacceptable factor
proportional to the full contour height.  Integrating the reciprocal-height
derivative majorant instead gives a `Real.log (v / u)` total-variation cost.
This closes both high-height parts of the dynamic left-edge contour budget
needed by the two-height explicit-formula route. The negative estimate follows
by the exact change of variables `t -> -t`; no zeta conjugation assumption is
introduced.

## What remains open

- The two high-height pieces must still be combined with the already
  formalized low segment and horizontal contour budgets.
- The resulting full contour remainder must be compared against the actual
  low-height zero-cluster signal at distinct outer and detector heights.
- No theorem here proves residual energy after deleting an arbitrary finite
  recorded zero set `S`.
- No cofinal `S`-relative Sharp lower bound, Carlson contradiction, zero
  exclusion, or Riemann Hypothesis conclusion follows from this module alone.
