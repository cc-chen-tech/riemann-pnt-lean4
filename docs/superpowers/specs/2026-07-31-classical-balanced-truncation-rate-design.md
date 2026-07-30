# Classical balanced truncation-rate design

## Objective

Expose the exact truncation-height optimization data used by the closed-form
Pintz-Carlson-explicit-formula transfer.  Earlier endpoints existentially
returned positive constants but hid the relation between the selected height
rate and the zero-free gap constant.

## Rates

For a classical zero-free constant `b > 0`, define the admissibly optimized
height rate

\[
\alpha_*(b)=\min(1,\sqrt b).
\]

The concrete selected-height zero-free proof uses

\[
r_{\mathrm{gap}}(b)=\frac{\alpha_*(b)}2.
\]

The stack-21 coarse Carlson layer majorant has square-root-log exponential
rate `r_gap / 4`.  Define the currently verified full-transfer bottleneck

\[
r_{\mathrm{verified}}(b)=\frac{\alpha_*(b)}8.
\]

The module proves the exact identity

\[
r_{\mathrm{verified}}=rac{r_{\mathrm{gap}}}{4},
\]

its positivity, and

\[
r_{\mathrm{verified}}\le \alpha_*.
\]

Thus the contour term is strictly faster than the current coarse Carlson
layer contribution.

## Optimality in the verified framework

The existing balanced-rate optimizer states that for every admissible height
rate `alpha`,

\[
\min\!\left(\alpha,\frac b\alpha\right)\le\alpha_*(b).
\]

Dividing by the fixed coarse Carlson loss factor eight proves

\[
\frac18\min\!\left(\alpha,\frac b\alpha\right)
 \le r_{\mathrm{verified}}(b).
\]

This is an optimizer theorem for the current verified transfer architecture,
not a claim that the factor eight is analytically optimal.

## Exact zero-free endpoint

The module reconstructs the selected classical dyadic Carlson zero-free
certificate while retaining the formerly hidden equality

\[
r_{\mathrm{gap}}=\alpha_*/2.
\]

This makes the truncation tradeoff available to downstream quantitative PNT
and optimizer theorems instead of losing it behind existential constants.

## Honest boundary

The factor eight comes from the current coarse layer aggregation (`1/2` in the
gap exponent, another `1/2` in the chosen gap constant, and the stack-21
majorant's `/4` rate).  Improving it requires sharpening that aggregation.
This module does not prove the globally optimal analytic PNT rate, an
unconditional Omega theorem, or RH.
