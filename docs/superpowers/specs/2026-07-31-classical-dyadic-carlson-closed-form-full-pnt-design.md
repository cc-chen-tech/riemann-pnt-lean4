# Classical dyadic Carlson closed-form full-PNT design

## Objective

Remove the last opaque certificate-valued term from the stack-25 pointwise PNT
majorant by substituting the proved two-scale contour estimate at the actual
classical selected height.

## Closed-form contour bound

Write

\[
u=\sqrt{\log m},\qquad
\alpha=\min(1,\sqrt b).
\]

For the selected height in the unit interval immediately below
`exp(alpha * u)`, the depth-zero relative contour remainder satisfies

\[
B_{\mathrm{contour}}(m)
 \le 26C u^4e^{-\alpha u}
   +2K\frac{u}{m},
\]

where `C` is the uniform good-height certificate constant and `K` is the fixed
left-contour constant already defined in the repository.  The remaining
closed-log part is retained exactly as

\[
B_{\mathrm{closed-log}}(m)=
 \frac{\left\|\frac12\log(1-m^{-2})\right\|}{m}.
\]

Both terms tend to zero.

## Final closed-form PNT majorant

The stack-26 majorant is

\[
Q_{\mathrm{closed}}(m)=F_{\mathrm{zero}}(m)
 +|A(m)|
 +26C u^4e^{-\alpha u}
 +2K\frac{u}{m}
 +B_{\mathrm{closed-log}}(m).
\]

The module proves eventually

\[
\left|\frac{\psi_0(m)-m}{m}\right|
 \le Q_{\mathrm{closed}}(m),
\qquad Q_{\mathrm{closed}}(m)\to0.
\]

## Truncation-rate comparison

The existing optimizer proves

\[
\alpha=\min(1,\sqrt b)
\]

maximizes the common contour/zero-free rate among admissible height exponents.
The concrete dyadic Carlson zero-free construction chooses gap constant

\[
r=\frac{\alpha}{2}.
\]

The stack-21 coarse Carlson majorant decays with exponent `r/4`, hence with
square-root-log rate `alpha/8`, while the contour term decays with rate
`alpha`.  Therefore the current verified upper-transfer bottleneck is the
Carlson layer aggregation, not the contour remainder.  Improving the final
rate now requires sharpening the layer-count/log-power absorption constants,
not increasing the truncation height.

## Honest boundary

The endpoint is closed-form up to genuine mathematical constants and the
finite real-ordinate zero sum.  It does not claim the exponent `alpha/8` is
analytically optimal; it is the rate delivered by the current verified coarse
Carlson aggregation.  No unconditional Omega theorem or RH is claimed.
