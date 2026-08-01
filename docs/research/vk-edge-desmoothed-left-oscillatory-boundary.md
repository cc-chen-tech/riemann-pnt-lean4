# Oscillatory integration boundary

This branch proves the reusable interval estimate

\[
  \left\|\int_u^v A(t)e^{i\omega t}\,dt\right\|
  \le
  \frac{2M_0+(v-u)M_1}{|\omega|},
\]

under explicit endpoint/amplitude and derivative bounds. Taking
`omega = log x` supplies exactly the reciprocal logarithm that absolute-value
estimates lose on the dynamic left edge.

The theorem is an analytic integration-by-parts mechanism. It does not yet
establish that the actual amplitude built from `logDeriv riemannZeta`, the
denominator, and `cubicKernelMultiplier` satisfies the required derivative and
endpoint bounds. Consequently it does not yet bound the actual desmoothed left
contour, prove an S-relative energy lower bound, produce a Carlson
contradiction, or prove RH.
