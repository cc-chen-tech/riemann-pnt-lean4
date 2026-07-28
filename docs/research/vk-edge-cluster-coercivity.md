# VK-edge finite-cluster coercivity checkpoint

## Scope

This checkpoint proves a reusable local `L²` lower bound for a finite
exponential package whose real exponents vary in a narrow band. It is designed
for the top-band zero cluster in the explicit formula. It does not prove that
the required coercivity inequality holds for zeta zeros, and it does not prove
RH or a zero-density contradiction.

## Abstract estimate

For

\[
F(t)=\sum_{j\in S}c_j
  e^{\alpha_j(t-a)}e^{i\lambda_jt},
\qquad -\delta\leq\alpha_j\leq0,
\]

let equal frequencies first be merged:

\[
d_\lambda=\sum_{\lambda_j=\lambda}c_j.
\]

Write

\[
E=\sum_\lambda |d_\lambda|^2,\qquad
B=\sum_{\lambda\ne\mu}
  \frac{2|d_\lambda||d_\mu|}{|\mu-\lambda|},\qquad
M=\sum_j|c_j|.
\]

The Lean theorem
`integral_normSq_driftingExponentialPolynomial_ge_merged` proves

\[
\int_a^{a+L}|F(t)|^2\,dt
\ge
\frac12(LE-B)
-
L(1-e^{-\delta L})^2M^2.
\]

Consequently the integral is strictly positive whenever

\[
B+
2L(1-e^{-\delta L})^2M^2
<
LE.
\]

The collision-safe statement is important: two zeta zeros can in principle
have the same ordinate. Their coefficients are merged before the diagonal
energy is measured, so cancellation is visible in `E` rather than excluded by
an unjustified distinct-ordinate hypothesis.

## Zeta specialization

For a top-band zero cluster normalized by a reference exponent `beta`, take

\[
c_\rho=
\frac{m(\rho)}{\rho}
e^{(\operatorname{Re}\rho-\beta)a},
\quad
\alpha_\rho=\operatorname{Re}\rho-\beta,
\quad
\lambda_\rho=\operatorname{Im}\rho.
\]

Then the normalized finite zero contribution on `[a,a+L]` is exactly the
drifting exponential polynomial above. The band condition

\[
\beta-\delta\leq\operatorname{Re}\rho\leq\beta
\]

supplies `-\delta <= alpha_rho <= 0`.

## Remaining mathematical gate

Carlson zero density controls the number of zeros in the top band, but it does
not by itself prove the coercivity inequality. The missing input is a lower
bound for the merged energy relative to:

1. the reciprocal-spacing off-diagonal budget `B`;
2. the drift loss governed by `delta * L`;
3. possible cancellation among zeros sharing one ordinate.

Thus the next honest alternatives are:

- prove a zeta-specific lower bound for merged coefficients;
- split the cluster into near-frequency blocks and control each block before
  applying the off-diagonal estimate between blocks;
- replace reciprocal-spacing control with a Turan or Remez inequality whose
  loss depends only on the Carlson cardinality bound.

Until one of these is proved, local `L²` lower bounds remain compatible with a
finite off-line cluster and cannot yield a Carlson contradiction.
