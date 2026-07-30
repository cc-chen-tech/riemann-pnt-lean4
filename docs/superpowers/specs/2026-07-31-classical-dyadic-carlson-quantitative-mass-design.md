# Classical dyadic Carlson quantitative-mass design

## Objective

Replace the qualitative `Tendsto` endpoint for the density-controlled moving
zero layers by a pointwise, explicit square-root-log majorant.

For positive constants `C` and `rate`, define

\[
M_{C,r}(m)=\exp\!\left(
  \log C-3\log r+11\log(1+\sqrt{\log m})
  -\frac r4\sqrt{\log m}
\right).
\]

The module proves that the classical dynamic Carlson layer mass is eventually
bounded by `M_{C,r}` and that `M_{C,r}(m) -> 0`.

## Derivation

The existing layered coarse ratio has logarithm

\[
\log C+2\log(\delta^{-1})+4\log\log m+
\log(L(m)+1)-\frac{\delta(m)}2\log m.
\]

Minimal dyadic layer count gives
`log (L(m)+1) <= log (delta(m)^(-1))`.  With

\[
\delta(m)=\frac r{1+\sqrt{\log m}},
\]

the three inverse-gap costs contribute `-3 log r` and at most six powers of
`1+sqrt(log m)`.  The log-power term contributes at most eight further
logarithmic units; the chosen exponent eleven is a convenient common envelope
once the negative exponential term is retained.  The decay follows from the
standard fact that every fixed power is dominated by
`exp(-(r/4) sqrt(log m))`.

## Public theorem chain

1. Convert the actual minimal dyadic Carlson fixed-anchor mass into the existing
   layered coarse ratio.
2. Bound that coarse ratio by `classicalDyadicCarlsonSqrtLogMajorant`.
3. expose the equivalent polynomial-times-exponential form.
4. Prove the explicit majorant tends to zero.
5. Transfer the bound to every selected classical admissible height, including
   the middle mass and the right-strip mass.

## Honest boundary

This closes an explicit majorant only for the density-controlled right-hand
zero layers.  The fixed low-real-part strip remains a separate decaying term.
The critical-half contribution, real-ordinate term, contour remainder, and all
other explicit-formula pieces are not yet compressed into this same majorant.
Consequently this module does not claim an optimal quantitative PNT error, a
new zero-density theorem, an unconditional Omega theorem, or RH.
