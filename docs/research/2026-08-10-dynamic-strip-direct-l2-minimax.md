# Dynamic-strip direct-`L2` minimax

## Scope

This note solves the polynomial exponent optimization for the corrected
multiplicity-weighted direct-`L2` block bound.  It does not include contour,
real-axis, trivial-zero, or sharp lower-bound constants.

Let

\[
  \frac12<\beta<1,
  \qquad \lambda=1+\varepsilon\ge1,
  \qquad q(\sigma)=4\sigma(1-\sigma).
\]

The observation interval is `[X,X^lambda]`.  A dyadic height begins at
`T = X^gamma`.

## 1. Correct strip exponent

For a real-part strip

\[
  \sigma_L\le\Re\rho<\sigma_R,
\]

the complex triangle-Laplace kernel and linear Carlson capacity give the
normalized block exponent

\[
  E(\sigma_L,\sigma_R;\gamma)
  =2\kappa_\lambda(\sigma_R-\beta)
   +\gamma(q(\sigma_L)-2),
\]

where

\[
  \kappa_\lambda(a)=
  \begin{cases}
    a,&a\le0,\\
    \lambda a,&a\ge0.
  \end{cases}
\]

The logarithmic loss is `(log T)^5`.  It does not affect a strictly negative
polynomial exponent, but it makes exponent zero a genuine non-decaying
critical case.

## 2. Infinitesimal-strip envelope

For a zero-width strip at `sigma`, define

\[
  \Phi_\gamma(\sigma)
  =2\kappa_\lambda(\sigma-\beta)
   +\gamma(q(\sigma)-2).
\]

Put

\[
  g=\lambda(1-\beta).
\]

Assume

\[
  g<\gamma<\frac\lambda2.
\]

For `sigma <= beta`, both

\[
  2(\sigma-\beta)\le0
  \quad\text{and}\quad
  q(\sigma)-2\le-1,
\]

so

\[
  \Phi_\gamma(\sigma)\le-\gamma.
\]

For `sigma >= beta`,

\[
  \Phi_\gamma'(\sigma)
  =2\lambda+4\gamma(1-2\sigma)
  \ge2\lambda-4\gamma>0.
\]

Hence the upper-side envelope is strictly increasing and has maximum at
`sigma = 1`:

\[
  \Phi_\gamma(1)
  =2\lambda(1-\beta)-2\gamma
  =-2(\gamma-g).
\]

Therefore

\[
  \sup_{1/2\le\sigma\le1}\Phi_\gamma(\sigma)
  \le-r,
  \qquad
  r=\min\{\gamma,2(\gamma-g)\}>0.
\]

This proof does not need monotonicity on the lower side.

## 3. Finite strip mesh

The support function `kappa_lambda` is `lambda`-Lipschitz.  Thus for a strip
of width at most `delta`,

\[
\begin{aligned}
  E(\sigma_L,\sigma_R;\gamma)
  &\le \Phi_\gamma(\sigma_L)
       +2\lambda(\sigma_R-\sigma_L)\\
  &\le-r+2\lambda\delta.
\end{aligned}
\]

Choose

\[
  \delta=\frac{r}{4\lambda}.
\]

Every strip in any finite partition of `[1/2,1]` with mesh at most `delta`
then satisfies

\[
  E(\sigma_L,\sigma_R;\gamma)
  \le-\frac r2<0.
\]

This replaces fixed decimal or hundredth grids by a parameter-driven finite
partition with an explicit common decay margin.

At the actual-zeta level, Carlson may require `sigma_L > 1/2`.  The first
strip touching `1/2` should be discharged by the ordinary total zero count;
all remaining strips use Carlson.  This hybrid endpoint does not change the
exponent calculation because `q(1/2)=1`.

## 4. Exact critical height

The right-edge limit gives

\[
  \lim_{\sigma_L,\sigma_R\to1}
  E(\sigma_L,\sigma_R;\gamma)
  =2g-2\gamma.
\]

Therefore:

- if `gamma > g`, a sufficiently fine finite mesh has uniform polynomial
  decay;
- if `gamma = g`, the right-edge exponent tends to zero and the fifth
  logarithmic power prevents decay;
- if `gamma < g`, strips sufficiently close to the 1-line have positive
  exponent.

Thus

\[
  \boxed{\gamma_{\mathrm{crit}}=\lambda(1-\beta)}
\]

is the exact threshold for this direct-`L2` Carlson mechanism.  It is not
merely a sufficient value obtained from a convenient parameter choice.

## 5. Feasibility under an upper height cap

Suppose the direct-`L2` cutoff must also satisfy

\[
  \gamma<c\le\frac\lambda2.
\]

There exists an admissible `gamma` exactly when

\[
  g<c.
\]

For the intrinsic cap `c = lambda/2`, this condition is simply

\[
  \beta>\frac12.
\]

If an outer cubic height `alpha` is also imposed, take

\[
  c=\min\left(\alpha,\frac\lambda2\right).
\]

For the standard cubic choice

\[
  \alpha=\frac{1+g}{2},
\]

the additional condition `g < alpha` is equivalent to `g < 1`.  Hence the
combined intrinsic feasibility conditions are

\[
  \beta>\frac12,
  \qquad
  \lambda(1-\beta)<1.
\]

The older shared-cutoff restriction `gamma < 2 beta - 1` is not part of this
intrinsic calculation.  Imposing it reintroduces the familiar `beta > 2/3`
barrier and must be labeled as a compatibility constraint, not as a Carlson
direct-`L2` impossibility.

## 6. Three different notions of chosen height

These values must not be conflated.

### Critical height

\[
  \gamma_{\mathrm{crit}}=g.
\]

It is an unattained strict-decay boundary.

### Tail-only optimum

The worst upper-strip exponent

\[
  2g-2\gamma
\]

strictly decreases with `gamma`.  If no other error increases with height,
the tail-only optimum is the upper cap `gamma -> c`; there is no interior
minimizer.

### Balanced robust choice

To maximize the smaller of the distance from criticality and the distance
from the upper cap, choose

\[
  \gamma_{\mathrm{bal}}=\frac{g+c}{2}.
\]

For this choice,

\[
  \gamma_{\mathrm{bal}}-g
  =c-\gamma_{\mathrm{bal}}
  =\frac{c-g}{2}.
\]

It is a max-margin choice, not the tail-only optimum.  Its continuum decay
margin is

\[
  r_{\mathrm{bal}}
  =\min\left\{
    \frac{g+c}{2},c-g
  \right\}.
\]

A finite mesh of width

\[
  \delta_{\mathrm{bal}}
  =\frac{r_{\mathrm{bal}}}{4\lambda}
\]

retains the common exponent margin `-r_bal / 2`.

## 7. General finite affine minimax interface

After discretizing the real-part range, every contribution to a unified
transfer has an affine exponent in the height parameters:

\[
  A_j+B_j\gamma+C_j\alpha+D_jd.
\]

The full "optimal truncation" problem should therefore be stated as a finite
convex piecewise-affine minimax problem:

\[
  \min_{(\gamma,\alpha,d)\in\mathcal P}
  \max_j
  (A_j+B_j\gamma+C_j\alpha+D_jd),
\]

where `P` records the strict feasibility inequalities.  Candidate optima are
boundary points and intersections of active affine exponents.  The theorem
should return:

- the selected parameters;
- the active constraints;
- the common exponent margin;
- the unchanged logarithmic ledger.

The direct-`L2` calculation above supplies one family of affine constraints.
It does not by itself decide the full explicit-formula optimum.

## 8. Formal theorem chain

The parameter layer should expose:

1. `directL2Envelope_le` with margin
   `min gamma (2 * (gamma - lambda * (1 - beta)))`;
2. `directL2FiniteStrip_le` using the Lipschitz mesh penalty;
3. `exists_directL2FinitePartition` with mesh
   `r / (4 * lambda)`;
4. `directL2CriticalHeight_iff` recording the strict threshold;
5. `directL2BalancedHeight` under a supplied cap `c`;
6. a generic finite affine minimax certificate used jointly by the upper and
   lower transfer machines.

No statement here excludes zeros with real part greater than `2/3`, proves
RH, or supplies the sharp oscillation constant.
