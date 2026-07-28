# Cosine-Model Annihilator Step-Average Audit

## Proved finite-spectral result

For a finite exponential polynomial

\[
F(y)=\sum_{j\in S} c_j e^{i\omega_j y},
\]

assume the frequencies are distinct and positive, none equals the selected
target frequency \(\gamma>0\), and at least one coefficient is nonzero.
The module proves that there are real numbers \(h\) and \(L>0\) such that

\[
\int_0^L
\left|
\sum_{j\in S}
2\bigl(\cos(\omega_j h)-\cos(\gamma h)\bigr)c_j
e^{i\omega_j y}
\right|^2\,dy>0.
\]

The proof first averages the exact detector multiplier over the step:

\[
\frac1H\int_0^H
4\bigl(\cos(\lambda h)-\cos(\gamma h)\bigr)^2\,dh
\longrightarrow 4
\qquad(\lambda\ne\gamma).
\]

It then selects a step which preserves one nonzero residual coefficient and
uses the repository's finite-frequency mean-square theorem. The interval
length is chosen so that the diagonal energy exceeds the explicit
off-diagonal budget by at least one.

## What this closes

This removes a genuine finite-dimensional obstruction: a fixed detector step
can accidentally annihilate another frequency, but step averaging guarantees
that a nonzero finite residual spectrum cannot be killed for every step.
The conclusion is an actual positive finite-window second moment, not only a
positive formal diagonal term.

The module also instantiates this theorem with the repository's actual
multiplicity-aware zeta coefficients

\[
c_\rho=\frac{m(\rho)}{\rho}.
\]

After filtering the finite equal-real-part zero package to positive heights and
removing the selected target frequency, Lean verifies that a nonempty residual
package has positive coefficient energy and distinct frequencies. Hence some
annihilator step leaves that actual finite zeta package with positive
finite-window second moment.

## What remains open

The zeta specialization assumes that the filtered finite residual package is
nonempty. It does not prove that an arbitrary selected off-critical-line zeta
zero has another zero on the same real-part edge. It also does not control:

1. lower-real-part zero contributions after normalization;
2. the infinite or moving-height zero tail;
3. the explicit-formula contour and truncation remainder;
4. cancellation between the finite package and those analytic remainder
   terms.

Consequently this module proves neither a Carlson contradiction nor RH. The
next analytic gate is a quantitative comparison between the positive finite
package energy and the full normalized explicit-formula residual.
