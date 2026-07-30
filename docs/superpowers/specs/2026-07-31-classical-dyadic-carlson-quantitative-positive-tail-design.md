# Classical dyadic Carlson quantitative positive-tail design

## Objective

Upgrade the classical selected-height positive-ordinate zero tail from a
qualitative limit to an explicit pointwise majorant.  This stack combines the
critical-half low layer with the already quantified moving-middle and moving
right-strip contributions.

## Generic selected-height extraction

The existing selected-height hybrid theorem proved convergence by constructing
an eventual pointwise bound internally.  This stack exposes that bound as a
reusable theorem:

\[
\frac{|Z_i(x)|}{x^{\beta-1}}
 \le C\kappa^{-1}(\alpha+2)
      x^{\tau-\beta+\alpha}(\log x)^4.
\]

The hypotheses are the same selected-height polynomial ceiling, cofinality,
uniform norm separation, and real-part ceiling used by the qualitative
transfer.

## Critical-half term

For `beta=1`, `tau=1/2`, and `alpha=1/64`, the exposed majorant is

\[
K_{E,\eta}(m)
 = E\eta^{-1}\left(2+\frac1{64}\right)
   m^{-31/64}(\log m)^4.
\]

The module proves both the exact identity and convergence to zero, then applies
it to the canonical critical-half low layer at every classical admissible
selected height.

## Complete positive-zero tail

The high critical-half layer is already covered by the moving-middle and
moving right strip.  Let

\[
L_{C,\kappa}(m)
 = C\kappa^{-1}\left(2+\frac1{64}\right)
   m^{-7/64}(\log m)^4
\]

and let `M(D,r,m)` be the stack-21 Carlson square-root-log majorant.  The full
positive-ordinate zero tail is eventually bounded by

\[
P(m)=K_{E,\eta}(m)+L_{C,\kappa}(m)+2M(D,r,m).
\]

Thus all positive-ordinate nontrivial zeros visible below the selected height
are controlled by one explicit function tending to zero.

## Quantifier boundary

The Carlson constants `rate` and `D` are global across selectors.  The norm
separation constants for the critical-half and fixed low strip remain inside
each selector because the current certificates are produced from the selected
height schedule.  No selector-uniform lower norm bound is assumed.

## Honest boundary

This is a quantitative positive-zero-tail theorem, not yet a complete
quantitative PNT remainder theorem.  The real-ordinate zero contribution,
explicit-formula real-axis and trivial-zero terms, and contour remainder still
need compatible pointwise majorants.  No new Carlson density estimate,
unconditional Omega theorem, optimal PNT rate, or RH is claimed.
