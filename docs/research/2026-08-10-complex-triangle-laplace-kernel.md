# Complex triangle-Laplace kernel for off-critical zero energy

## Problem corrected by this note

A zeta-zero term normalized by a target real part `beta_0` has logarithmic
form

\[
  e^{(\rho-\beta_0)u}
  =e^{(\beta-\beta_0)u}e^{i\gamma u}.
\]

When two terms are multiplied in an `L2` energy, the real exponential depends
on the pair of zeros.  Therefore the long observation triangle cannot be
treated as a pure Fourier kernel unless the two real parts sum to exactly
`2 beta_0`.

The correct object is a bilateral Laplace transform at a complex argument.
It retains the same quadratic frequency decay, multiplied by exactly the
endpoint growth forced by the varying real parts.

## 1. Centered triangle

For `L > 0`, define

\[
  W_L(v)=\frac1L\left(1-\frac{|v|}{L}\right)_+.
\]

It is nonnegative, supported on `[-L,L]`, and has integral one.  For
`z in C`, put

\[
  K_L(z)=\int_{-L}^{L}W_L(v)e^{zv}\,dv.
\]

If `z != 0`, direct integration gives

\[
  K_L(z)
  =\frac{e^{Lz}-2+e^{-Lz}}{L^2z^2}
  =\left(\frac{2\sinh(Lz/2)}{Lz}\right)^2.
\]

At `z = 0`, the integral is one.  Thus `K_L` is the continuous extension of
the centered second-difference quotient.

For `z = i delta`, this reduces to the Fejer kernel

\[
  K_L(i\delta)
  =\left(\frac{\sin(L\delta/2)}{L\delta/2}\right)^2.
\]

## 2. Uniform complex bound

Write

\[
  z=a+i\delta,
  \qquad a,\delta\in\mathbb R.
\]

The integral representation gives the trivial bound

\[
  |K_L(z)|
  \le \int W_L(v)e^{av}\,dv
  \le e^{|a|L}.
\]

For `z != 0`, the second-difference formula gives

\[
\begin{aligned}
  |e^{Lz}-2+e^{-Lz}|
  &\le e^{aL}+2+e^{-aL}\\
  &\le 4e^{|a|L}.
\end{aligned}
\]

Consequently

\[
  |K_L(a+i\delta)|
  \le
  e^{|a|L}
  \min\left(1,\frac4{L^2(a^2+\delta^2)}\right).
\]

In particular, for `delta != 0`,

\[
  |K_L(a+i\delta)|
  \le
  e^{|a|L}
  \min\left(1,\frac4{L^2\delta^2}\right).
\]

For equal ordinates, the first bound is used.  No frequency injectivity is
required.

## 3. Translation to the target interval

Let

\[
  p=\log X,
  \qquad q=\lambda\log X,
  \qquad u_0=\frac{p+q}{2},
  \qquad L=\frac{q-p}{2}.
\]

The translated triangle

\[
  W_{u_0,L}(u)=W_L(u-u_0)
\]

is supported on `[p,q]`.  A change of variables gives

\[
  \int W_{u_0,L}(u)e^{zu}\,du=e^{zu_0}K_L(z).
\]

Therefore

\[
  \left|\int W_{u_0,L}(u)e^{(a+i\delta)u}\,du\right|
  \le
  e^{au_0+|a|L}
  \min\left(1,\frac4{L^2\delta^2}\right),
\]

with the second factor interpreted as one when `delta = 0`.

The exponential factor is not an artificial loss:

\[
  au_0+|a|L=\max(ap,aq).
\]

It is exactly the maximum real-exponential growth on the support.

## 4. Pair kernel for a real-part strip

For two zeros in the same strip, set

\[
  z_{ij}
  =(\beta_i+\beta_j-2\beta_0)
   +i(\gamma_i-\gamma_j).
\]

If `beta_i,beta_j < sigma_R`, then

\[
  a_{ij}=\beta_i+\beta_j-2\beta_0
  \le2(\sigma_R-\beta_0).
\]

The function `a -> max(ap,aq)` is increasing because `0 < p <= q`.
Hence

\[
  e^{a_{ij}u_0+|a_{ij}|L}
  \le
  X^{2\kappa_\lambda(\sigma_R-\beta_0)},
\]

where

\[
  \kappa_\lambda(r)=
  \begin{cases}
    r,&r\le0,\\
    \lambda r,&r\ge0.
  \end{cases}
\]

Thus

\[
  \left|\int W_{u_0,L}(u)e^{z_{ij}u}\,du\right|
  \le
  X^{2\kappa_\lambda(\sigma_R-\beta_0)}
  A_{ij},
\]

with

\[
  A_{ij}=
  \begin{cases}
    1,&\gamma_i=\gamma_j,\\
    \min\left(1,
      \dfrac4{L^2(\gamma_i-\gamma_j)^2}
    \right),&\gamma_i\ne\gamma_j.
  \end{cases}
\]

This is precisely the symmetric nonnegative kernel required by the
multiplicity-weighted Schur lemma.

## 5. Energy consequence

Let

\[
  F(u)=\sum_i m_i d_i e^{(\rho_i-\beta_0)u},
\]

where `d_i` contains the reciprocal zero and any fixed explicit-formula
multiplier.  Expanding the triangular energy and applying the pair-kernel
bound yields

\[
\begin{aligned}
  \int W_{u_0,L}(u)|F(u)|^2\,du
  &\le
  X^{2\kappa_\lambda(\sigma_R-\beta_0)}\\
  &\quad\cdot
  \sum_{i,j}m_i m_j|d_i||d_j|A_{ij}.
\end{aligned}
\]

If

\[
  \sup_i\sum_jm_jA_{ij}\le O,
\]

weighted Schur gives

\[
  \int W_{u_0,L}(u)|F(u)|^2\,du
  \le
  X^{2\kappa_\lambda(\sigma_R-\beta_0)}
  O\sum_i m_i|d_i|^2.
\]

For actual zeta zeros, the local analytic-multiplicity bound supplies
`O = O(log T)`.  Carlson supplies the linear coefficient mass with exponent
`q(sigma_L)-2` and log loss four.  Therefore the corrected off-critical block
energy still has log loss five.

## 6. Separation from cubic desmoothing

There are two triangle kernels in the full proof and they serve different
purposes.

- The long triangle above has `L` comparable to `epsilon * log X`.  It detects
  energy somewhere in `[X,X^(1+epsilon)]` and supplies frequency decay.
- The short triangle in the cubic explicit formula has width `h = x^(-d)`.
  It removes the endpoint desmoothing loss and modifies each zero coefficient.

They may share a generic centered second-difference identity, but their scale
assumptions and theorem statements must remain distinct.

## 7. Minimal formalization boundary

The required production lemmas are:

1. the exact centered triangle-Laplace identity;
2. the complex norm bound with `exp (abs a * L)`;
3. the translated support-endpoint bound;
4. the stripwise pair-kernel bound;
5. the weighted-Schur energy consequence.

These lemmas belong in a `ZeroDensityLayerBudget*` module.  They do not modify
or reprove the separately owned sharp lower-bound or Gram-separation modules.
