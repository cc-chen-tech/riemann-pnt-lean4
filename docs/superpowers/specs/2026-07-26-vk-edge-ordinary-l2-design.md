# VK-edge ordinary local L2 design

## Objective

Upgrade the existing Gaussian-weighted second-moment lower bound to an
ordinary logarithmic-window lower bound with a named, inspectable constant.
For a fixed off-line zero and a fixed missing odd harmonic, the target scale
is

\[
  \int_{(q-d)m}^{(q+d)m}
    |\rho|^2 e^{-2\beta y}
    \bigl(\psi(e^y)-e^y\bigr)^2\,dy
  \;>\; c_{\rho,k,q}\sqrt m
\]

for all sufficiently large \(m\).

## Mathematical mechanism

The current contour theorem gives a constant-order lower bound for

\[
  \int_I F_\rho(y)^2 |K_m(y)|\,dy.
\]

The polynomial-Gaussian construction gives the pointwise envelope

\[
  |K_m(y)| \le
  K_{\rho,k,q}
  \exp\!\left(\frac{|qm-y|}{\sqrt m}\right)G_m(qm-y).
\]

Completing the square yields

\[
  \exp(|t|/\sqrt m)G_m(t)
  \le \frac{e}{\sqrt m}.
\]

Consequently,

\[
  \int_I F_\rho(y)^2 |K_m(y)|\,dy
  \le \frac{eK_{\rho,k,q}}{\sqrt m}
      \int_I F_\rho(y)^2\,dy.
\]

Combining both inequalities produces the ordinary second-moment lower
bound.

## Public API

1. Expose the finite coefficient sum controlling a polynomial-Gaussian
   kernel:

   `polynomialGaussianEnvelopeConstant`.

2. Define named constants for projected, relatively projected, and paired
   sharpened kernels.

3. Add:

   `centeredNormalizedWindowOrdinarySecondMoment`.

4. Prove a generic weighted-to-ordinary transfer lemma.

5. Specialize it to the true zeta contour, retaining analytic multiplicity
   and the strict `pi / 2` missing-harmonic constant.

6. Reparameterize by `epsilonGaussianScale` to obtain an endpoint on every
   interval

   `[log Y, (1 + epsilon) * log Y]`.

## Constant policy

The constants need not be numerically optimized. They must be finite
expressions in:

- polynomial coefficients;
- Gaussian derivative bounds;
- `rho`, the missing-harmonic center, and its contour coefficient;
- the fixed window parameter `q`;
- the selected missing harmonic `k`.

No `Classical.choose` witness is accepted as an "explicit constant".

## Boundary

This milestone does not claim a fixed-proportion positive-measure set.
An L2 lower bound and a threshold crossing only imply qualitative positive
measure without either:

- a local pointwise upper bound for `normalizedPsiError`, or
- a compatible fourth-moment upper bound.

It also does not produce an RH contradiction. That requires an unconditional
upper bound on the same local normalized second moment that is smaller than
the lower bound forced by every hypothetical zero with real part greater
than `1 / 2`.

## Verification

- focused contract build;
- focused axiom audit;
- `#print axioms` for every public endpoint;
- scan new source for `sorry`, `admit`, and project `axiom`;
- focused module build followed by the repository baseline verifier.
