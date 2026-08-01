# VK-edge desmoothed left derivative plan

## Scope

Build the actual-zeta analytic input needed to estimate the desmoothed cubic
left edge by oscillatory integration by parts.  This branch does not modify
Gate B, Carlson counting, witness extraction, or finite-set growth.

## Milestones

1. Prove that a closed disk around the dynamic positive left boundary is
   zero-free for the actual Riemann zeta function at high height.
2. Upgrade the center-line square-logarithmic bound for `logDeriv riemannZeta`
   to a uniform closed-disk bound.
3. Apply Cauchy's estimate to obtain a cubic-logarithmic derivative bound for
   `deriv (logDeriv riemannZeta)` at the dynamic left center.
4. Prove a complex oscillatory integration-by-parts estimate with the required
   `1 / log x` gain.
5. Assemble the high, compact, and end-cap pieces of the desmoothed left edge
   and record the remaining input to the S-relative Sharp lower bound.

## Claim boundary

The first three milestones are local analytic estimates.  They do not prove a
repeated S-relative energy lower bound, a Carlson contradiction, or RH.  The
final contour estimate will still need to be combined with the actual finite
zero package and the two-height Sharp construction.
