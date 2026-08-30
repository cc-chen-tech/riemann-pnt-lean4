# Continuity of the non-left Littlewood remainder

## Scope

This checkpoint proves that the three non-left boundary terms retained by
`LittlewoodLeftBoundaryLimit` converge when the shifted left endpoint tends
to the limiting endpoint.  It closes the first remaining contour lemma from
that checkpoint.  It does **not** yet perform the tail-sequence assembly that
simultaneously controls this remainder, the coefficient `critical - x`, and
the reverse-Fatou selected index.

## Moving weighted horizontal integrals

The only nonlinear-looking dependence on the moving endpoint is

\[
 J_g(x)=\int_x^{x_1}(u-x)g(u)\,du.
\]

For `g` continuous on the ambient compact interval,

\[
 J_g(x)=\int_x^{x_1}u g(u)\,du
       -x\int_x^{x_1}g(u)\,du.
\]

Both integrals on the right are continuous primitives with a moving left
endpoint, and multiplication by `x` preserves continuity.  This avoids a
separate parametric dominated-convergence argument.

The generic statement is formalized as
`continuousOn_intervalIntegral_sub_mul_left`.

## Application to the Littlewood remainder

On either selected horizontal side, analyticity and nonvanishing imply
continuity of

\[
 u\longmapsto \operatorname{Im}\frac{f'}{f}(u+i y_j).
\]

Applying the generic lemma to the bottom and top integrals proves continuity
of `littlewoodRectangleNonleftRemainder` in the left endpoint.  The fixed
right logarithmic integral is constant, and the fixed right logarithmic-
derivative integral is multiplied only by the linear factor `x_1-x`.

Thus, for any sequence `x_n` in the ambient interval with `x_n -> x_0`,

\[
 R_{\mathrm{nonleft}}(x_n)
   \longrightarrow R_{\mathrm{nonleft}}(x_0).
\]

No zero-free hypothesis is imposed on the limiting left vertical edge.  Only
the two fixed horizontal sides must be zero-free, exactly as required by the
selected-height construction.

## Remaining ledger

1. Apply the reverse-Fatou theorem to every tail `n = N+k`, so its selected
   index is forced beyond a prescribed `N`.
2. On that common tail, control both
   `R_nonleft(x_n)-R_nonleft(x_0)` and
   `(x_n-x_0) * zeroMultiplicityMassAtOrRight`.
3. Deduce the limiting coefficient inequality with `critical-x_0`.
4. Instantiate the divisor and right-shifted zero-free sequence for the
   actual product at the selected heights.

Only after those steps is the left-boundary part of equation (37) fully
assembled.  Equations (38)--(41), the long mollified second moment, and the
two-fifths optimization remain downstream.
