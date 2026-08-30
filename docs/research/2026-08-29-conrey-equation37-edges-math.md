# Conrey equation (37): selected edges and the left-boundary convention

## Scope

This checkpoint combines the two selected horizontal estimates with the
already proved moving-right-edge logarithmic and argument bounds.  It does
not assume the mollified product is zero-free on the Littlewood left edge,
and it does not claim equation (37), equations (38)--(41), the long
mollified mean square, or the final two-fifths result.

Put

\[
 \sigma_0={1\over2}-{R\over L},\qquad A=2\log L,
 \qquad F(s)=V_1(s)B(s).
\]

For `L >= 40000`, the elementary estimate `log L <= L/100` gives

\[
 A+3<e^L.
\]

Consequently the horizontal-height selector can be applied independently to
the bottom window `[A+1,A+2]` and the top window `[e^L-1,e^L]`.  It produces
`t_0<t_1`, zero-free complete horizontal segments, and

\[
 |H(t_j)|\le 1.1\cdot10^{12}L^7\quad(j=0,1),
\]

where

\[
 H(t)=\int_{\sigma_0}^{A}(\sigma-\sigma_0)
       \operatorname{Im}{F'\over F}(\sigma+it)\,d\sigma.
\]

On `[t_0,t_1]`, restriction of the proved global absolute-log estimate and
the right-edge argument theorem give

\[
 \left|\int_{t_0}^{t_1}\log|F(A+it)|\,dt\right|
 \le {507e^L\over L},\qquad
 \left|\int_{t_0}^{t_1}\operatorname{Re}{F'\over F}(A+it)\,dt\right|
 \le \pi.
\]

Thus the complete non-left boundary remainder in Littlewood's identity is
bounded by

\[
 {507e^L\over L}+2.2\cdot10^{12}L^7+(A-\sigma_0)\pi.
\]

## Newly exposed mathematical boundary

The repository's exact theorem
`littlewoodRectangle_zeroMultiplicityWeightedRealSum_eq_logNormEdges`
currently requires every zero of `F` in the closed rectangle to be strictly
interior.  The selected heights and the positive-real-part right-edge theorem
exclude zeros on the bottom, top, and right sides, but there is no theorem
excluding zeros on `Re s = sigma_0`, nor should equation (37) depend on such
an exclusion.

The classical Littlewood lemma permits this situation by a limiting
convention.  Move the left side to `sigma_0-epsilon` through zero-free
vertical lines and let `epsilon` decrease to zero.  Zeros lying on the target
left edge acquire weight `epsilon` and disappear in the limit, while the
left logarithmic integral converges in `L^1`; locally this is the elementary
integrability of `m log|t-gamma|` after analytic zero factorization.  Zeros
with real part at least `1/2` retain the fixed gap `R/L`.

The next contour-core task is therefore an analytic boundary-limit extension
of the exact Littlewood theorem, not an extra zero-free hypothesis.  Only
after that extension may the left logarithmic integral be bounded by Jensen
and the long mollified second moment.

## Source audit

Conrey 1989 states equation (37) after applying Littlewood's lemma exactly as
in Levinson and Conrey 1983.  Conrey 1983 applies the lemma to a rectangle
whose left side is `sigma_0=1/2-R/L` and counts the relevant product zeros
inside the rectangle; the printed argument does not supply a theorem that
the whole left side is zero-free.  The limiting boundary convention above is
therefore required for a literal formalization.
