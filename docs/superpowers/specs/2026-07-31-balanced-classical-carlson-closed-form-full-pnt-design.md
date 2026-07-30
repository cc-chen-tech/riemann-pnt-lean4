# Balanced classical Carlson closed-form full-PNT design

## Objective

Carry the exact optimized truncation and zero-free gap rates through every
quantitative layer to the actual natural relative Chebyshev error.  Earlier
full-PNT endpoints selected valid existential constants but did not retain the
relation between the height rate and Carlson gap rate.

## Global rate data

The endpoint returns global constants `b`, `gapRate`, and `D` satisfying

\[
\text{gapRate}=\frac{\min(1,\sqrt b)}2,
\]

and

\[
\text{verifiedRate}(b)=\frac{\text{gapRate}}4
 =\frac{\min(1,\sqrt b)}8.
\]

It also returns the Carlson moving dyadic gap certificate and the selected
height zero-free certificate using exactly this `gapRate`.

## Quantitative theorem chain

For each uniform good-height selector, the proof constructs:

1. a critical-half majorant
   \(E\eta^{-1}(2+1/64)m^{-31/64}(\log m)^4\);
2. a fixed low-strip majorant
   \(C\kappa^{-1}(2+1/64)m^{-7/64}(\log m)^4\);
3. two Carlson square-root-log terms using the retained `gapRate`;
4. the finite real-ordinate zero sum with each true exponent `Re rho - 1`;
5. the exact closed real-axis term;
6. the closed-form contour majorant
   \(26C_0u^4e^{-\alpha_*u}+2K u/m\);
7. the exact closed-log term.

These are assembled into
`classicalDyadicCarlsonClosedFormFullPNTErrorMajorant`.

## Final statement

For every selector there are only the selector-dependent norm-separation
constants `E`, `eta`, `C`, and `kappa` such that

\[
\left|\frac{\psi_0(m)-m}{m}\right|
 \le Q_{b,\mathrm{gapRate}}(m)
\]

eventually and

\[
Q_{b,\mathrm{gapRate}}(m)\to0.
\]

The optimized height/gap relation remains visible in the same existential
statement as this actual PNT error bound.

## Mathematical significance

This closes the upper-transfer target proposed for the project at the current
coarse Carlson precision:

\[
\text{zero-free region} + \text{Carlson density}
 + \text{explicit kernel} + \text{optimized height}
 \Longrightarrow \text{pointwise PNT error majorant}.
\]

The theorem is fully machine-auditable and does not hide the selected
truncation rate behind unrelated existential constants.

## Honest boundary

The verified square-root-log bottleneck is `alpha*/8`, not asserted to be the
best analytic constant.  The reverse/lower transfer still requires local-L2
control of the explicit-formula residual and the uncontrolled complementary
zero contribution.  This module does not prove an unconditional Omega theorem
or RH.
