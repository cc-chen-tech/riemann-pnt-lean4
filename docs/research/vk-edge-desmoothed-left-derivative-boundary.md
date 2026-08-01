# Dynamic-left derivative boundary

## Closed actual-zeta input

This branch proves three estimates for the actual Riemann zeta function on the
dynamic positive left boundary

\[
  a(H)=\frac{b}{(\log(H+6))^3}.
\]

For all sufficiently large `H`, and for center heights away from the compact
and endpoint ranges, it provides:

1. a zero-free closed disk of radius `a(H) / 2` around `a(H) + i t`;
2. a uniform `O((1 + log (H + 6))^2)` bound for `zeta'/zeta` on that disk;
3. a center bound
   `O((1 + log (H + 6))^3)` for the derivative of `zeta'/zeta`.

The disk result is not an abstract coefficient model. It is derived from the
proved finite-height reflected zero barrier for `riemannZeta`, and the
logarithmic-derivative estimates use the functional equation plus Cauchy's
estimate.

## What this enables

The derivative estimate supplies the amplitude-variation term needed when the
desmoothed left-edge integral is integrated by parts against
`exp (i * t * log x)`. The next theorem must retain the oscillation and obtain
the missing `1 / log x` gain; estimating the integrand by absolute values would
lose the target `x^beta` scale.

## What is not proved here

This branch does not yet prove:

- the oscillatory left-edge remainder bound;
- the full actual-zeta desmoothed contour formula at the two heights;
- a positive complement-energy lower bound after deleting an arbitrary finite
  recorded zero set `S`;
- cofinal repeatability, a Carlson contradiction, or RH.

The eventual Sharp theorem must still distinguish the outer contour height
`H = x^alpha` from the lower detector height `Y = x^gammaLow` and control the
compact center and endpoint caps separately.
