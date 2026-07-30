# Classical dyadic Carlson quantitative full-PNT design

## Objective

Assemble the quantified complete finite zero tail with the remaining actual
terms of the multiplicity-aware truncated explicit formula, producing one
pointwise upper bound for the natural relative Chebyshev error.

## Exact explicit-formula decomposition

For the selected height `H`, the repository proves the exact identity

\[
\frac{\psi_0(m)-m}{m}
 = \Re Z_H(m)+A(m)+R_H(m),
\]

where `Z_H` is the complete finite nontrivial-zero sum, `A` is the closed
real-axis term, and `R_H` is the signed approximation remainder.

The classical good-height certificate supplies the eventual pointwise bound

\[
|R_H(m)|\le B_{\mathrm{contour}}(m)+B_{\mathrm{closed-log}}(m).
\]

The trivial-zero contribution is exactly zero for the selected truncation
parameter `N=0`.

## Full error majorant

Let `F_zero(m)` be the stack-24 complete finite-zero majorant and let
`B_classical(m)` be
`selectedClassicalAdmissibleNaturalRemainderUpperBound`.  Define

\[
Q(m)=F_{\mathrm{zero}}(m)+|A(m)|+B_{\mathrm{classical}}(m).
\]

The module proves

\[
\left|\frac{\psi_0(m)-m}{m}\right|\le Q(m)
\]

eventually, and `Q(m) -> 0`.

## What is now unified

The pointwise majorant reaches the actual natural PNT error through one chain:

1. true zeta kernels and analytic multiplicities;
2. dynamic dyadic real-part layers;
3. Carlson density counts;
4. classical subpolynomial selected truncation height;
5. conjugation and the fixed real-ordinate set;
6. the exact multiplicity-aware explicit formula;
7. the certified contour and closed real-axis remainder bound.

This is stronger than the earlier endpoint that only asserted convergence of
the relative error.

## Honest boundary

The contour contribution remains expressed by the repository's explicit
certificate function `cofinalPNTFormulaRemainderBound`; this stack does not
compress that function to an optimized elementary closed form.  Consequently
it proves a complete pointwise majorant tending to zero, but not yet a claimed
optimal numerical PNT rate in the Johnston/Bellotti sense.  It also does not
prove an unconditional Omega theorem or RH.
