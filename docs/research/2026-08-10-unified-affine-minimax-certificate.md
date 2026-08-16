# Unified affine minimax certificate

## Objective

After choosing a finite real-part partition, every polynomial exponent in the
Pintz--Carlson--explicit-formula transfer is affine in the remaining height
and smoothing parameters.  Examples include:

- `L1` upper-transfer strip exponents;
- multiplicity-weighted direct-`L2` complement exponents;
- cubic contour exponents;
- real-axis and trivial-zero exponents;
- inequalities separating the low probe, direct-`L2` cutoff, and outer
  contour height.

The mathematically correct optimization problem is

\[
  \min_{p\in P}\max_{j\in J} f_j(p),
\]

where `P` is a finite polyhedron and each `f_j` is affine.  Lean does not need
to run a linear-programming algorithm.  It only needs to verify a proposed
primal/dual certificate.

## 1. Data model

Let the parameter vector be

\[
  p=(\gamma,\alpha,d,\ldots)\in\mathbb R^n.
\]

For each error contribution `j`, write

\[
  f_j(p)=a_j+b_j\mathbin{\cdot}p
\]

and record separately a nonnegative logarithmic loss `ell_j`.

The closed feasible polyhedron is

\[
  P=\{p:g_k(p)=c_k+d_k\mathbin{\cdot}p\le0
         \text{ for every }k\in K\}.
\]

Each exponent should also carry a tag such as

```text
upperL1 | lowerL2 | contour | realAxis | trivialZero | compatibility
```

for audit output.  Tags do not enter the minimax proof.

## 2. Primal/dual optimality certificate

Fix a candidate `p_star` and value `t_star`.  A certificate consists of:

1. primal feasibility:

   \[
     g_k(p_*)\le0;
   \]

2. candidate upper bound:

   \[
     f_j(p_*)\le t_*;
   \]

3. objective weights `w_j >= 0` with

   \[
     \sum_jw_j=1,
     \qquad
     \sum_jw_jf_j(p_*)=t_*;
   \]

4. feasible-constraint multipliers `mu_k >= 0`;

5. stationarity:

   \[
     \sum_jw_jb_j+\sum_k\mu_kd_k=0;
   \]

6. complementarity:

   \[
     \mu_kg_k(p_*)=0
     \quad\text{for every }k.
   \]

Then `p_star` is globally minimax-optimal on `P`.

## 3. Proof of optimality

For any `p in P`,

\[
\begin{aligned}
  \max_j f_j(p)
  &\ge\sum_jw_jf_j(p)\\
  &=\sum_jw_jf_j(p_*)
    +\left(\sum_jw_jb_j\right)\mathbin{\cdot}(p-p_*)\\
  &=t_*-sum_k\mu_kd_k\mathbin{\cdot}(p-p_*).
\end{aligned}
\]

If `mu_k > 0`, complementarity gives `g_k(p_star)=0`.  Feasibility of `p`
then gives

\[
  d_k\mathbin{\cdot}(p-p_*)le0.
\]

Every term in the last sum therefore has nonnegative contribution after the
minus sign.  Hence

\[
  \max_j f_j(p)\ge t_*.
\]

The candidate upper bound gives

\[
  \max_jf_j(p_*)\le t_*.
\]

The weighted equality implies the reverse inequality at `p_star`, so

\[
  \max_jf_j(p_*)=t_*
  =\min_{p\in P}\max_jf_j(p).
\]

This is a finite-sum algebra theorem.  No compactness, differentiability, or
external optimizer is needed once the certificate is supplied.

## 4. One-dimensional height certificate

For a single height `gamma in [l,u]`, let

\[
  f_j(\gamma)=a_j+b_j\gamma.
\]

The multidimensional certificate reduces to a weighted active slope

\[
  B=\sum_jw_jb_j.
\]

Optimality follows in each of three cases:

- `l < gamma_star < u` and `B = 0`;
- `gamma_star = l` and `B >= 0`;
- `gamma_star = u` and `B <= 0`.

Indeed,

\[
  \max_jf_j(\gamma)
  \ge t_*+(\gamma-\gamma_*)B.
\]

When two active lines have slopes

\[
  b_-<0<b_+,
\]

the explicit weights

\[
  w_- =\frac{b_+}{b_+-b_-},
  \qquad
  w_+ =\frac{-b_-}{b_+-b_-}
\]

are nonnegative, sum to one, and give weighted slope zero.  This provides a
small exact certificate for the usual balanced intersection.

## 5. Strict inequalities and unattained infima

Analytic feasibility frequently requires strict inequalities such as

\[
  \lambda(1-\beta)<\gamma<\frac\lambda2.
\]

An open feasible set need not contain its minimizer.  Therefore the formal
machine must distinguish:

- an optimum on a closed polyhedron;
- an infimum attained only on the boundary of the closure;
- an explicit interior point with certified safety margin.

For production transfer the recommended input is a closed safety polyhedron,
for example

\[
  \gamma\ge\lambda(1-\beta)+\eta_{\rm low},
  \qquad
  \gamma\le\frac\lambda2-\eta_{\rm high},
\]

with positive supplied margins.  The minimax theorem then proves an attained
optimum without pretending that a forbidden boundary point is admissible.

## 6. Decay certificate

Suppose the verified minimax value satisfies

\[
  t_*\le-\eta
\]

for some `eta > 0`.  If contribution `j` is bounded by

\[
  C_jX^{f_j(p_*)}(1+\log X)^{\ell_j},
\]

then every contribution is

\[
  O\left(X^{-\eta}(1+\log X)^{\ell_j}\right)=o(1).
\]

Because `J` is finite, their sum is also `o(1)`.  A quantitative version may
replace `eta` by `eta/2` after choosing an explicit threshold at which every
polylogarithm is at most `X^(eta/2)`.

The sign of `t_star` has an exact interpretation:

- `t_star < 0`: polynomial decay; finite log losses are harmless;
- `t_star = 0`: critical equality; a nonnegative log loss does not decay;
- `t_star > 0`: the supplied parameter region cannot close this transfer.

## 7. Unified upper/lower use

The same exponent family can contain both directions.

### Upper transfer

The `upperL1` entries bound the actual explicit-formula zero layers and
contour terms relative to the PNT main term.  A negative certificate yields a
PNT error upper bound.

### Lower transfer

The `lowerL2` entries bound the complement after deleting the finite target
cluster, relative to `x^beta / |rho_0|`.  A negative certificate yields
`o(1)` normalized complement energy.  The independent sharp lower-bound
component then compares its main-cluster constant with the resulting tail
constant.

The minimax certificate does not create a `pi/2` surplus or choose a sign.  It
only proves that all upper and lower error channels can be made simultaneously
small by the same explicit parameter vector.

## 8. Recommended theorem chain

The abstract module should expose:

1. `AffineExponent.eval`;
2. `AffineConstraint.IsFeasible`;
3. `AffineMinimaxCertificate`;
4. `AffineMinimaxCertificate.isGlobalMinimizer`;
5. the one-dimensional weighted-slope specialization;
6. `AffineDecayCertificate`, adding `t_star <= -eta` and log-loss metadata;
7. a tagged report listing active constraints and strict/critical exponents;
8. a unified transfer theorem consuming one decay certificate for both the
   upper `L1` and lower direct-`L2` channels.

The actual optimizer may be external, hand-derived, or generated by a small
script.  Mathematical trust resides only in the Lean-checked certificate.

## 9. Immediate application to the direct-`L2` height

For the direct-`L2` right edge,

\[
  f_{\rm right}(\gamma)
  =2\lambda(1-\beta)-2\gamma.
\]

Its slope is negative.  In a tail-only optimization it is minimized at the
largest permitted height, confirming that the midpoint height is not the
tail optimum.  An interior midpoint becomes optimal only after another active
constraint with positive slope, or an explicit max-margin objective, is
included.

This simple case is the first contract example for the generic certificate.
