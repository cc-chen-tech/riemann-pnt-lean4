# Classical dyadic Carlson quantitative full-zero-tail design

## Objective

Extend the explicit positive-ordinate zero-tail majorant to the complete finite
nontrivial-zero sum by treating negative ordinates through conjugation and
real ordinates through their fixed finite set.

## Real-ordinate majorant

For every nonnegative truncation height, the real-ordinate nontrivial-zero set
is exactly the height-zero finite set.  Define

\[
R(m)=\sum_{\substack{\rho:\,\zeta(\rho)=0\\ \Im\rho=0}}
  \left\|m(\rho)\frac{m^{\rho-1}}{\rho}\right\|.
\]

This deliberately preserves each zero's actual exponent `Re rho - 1` rather
than replacing the finite set by an unproved uniform numerical gap.  Every
nontrivial zero satisfies `Re rho < 1`, so each summand tends to zero and hence
`R(m) -> 0` by finite summation.  The norm of the dynamic real-ordinate sum is
eventually bounded by `R`.

## Full finite zero tail

Complex conjugation identifies the negative-ordinate sum with the conjugate of
the positive-ordinate sum.  If `P(m)` is the stack-23 positive-zero-tail
majorant, define

\[
F(m)=2P(m)+R(m).
\]

The existing conjugation inequality gives the eventual pointwise bound

\[
\left\|\sum_{|\Im\rho|\le H(m)}
  m(\rho)\frac{m^{\rho-1}}{\rho}\right\|\le F(m),
\]

and `F(m) -> 0`.

## Mathematical significance

This is the first explicit pointwise majorant in the stack controlling the
complete finite nontrivial-zero sum, not only one ordinate half or one real
strip.  It combines true zeta kernels, analytic multiplicity, dynamic Carlson
layers, selected truncation heights, and conjugation on one PNT zero-tail
object.

## Honest boundary

The theorem controls the finite nontrivial-zero part of the explicit formula.
The real-axis elementary term, trivial-zero term, and contour/truncation
remainder still require compatible pointwise bounds before a complete
quantitative natural PNT remainder can be claimed.  No new zero-density
estimate, optimal PNT rate, unconditional Omega theorem, or RH is claimed.
