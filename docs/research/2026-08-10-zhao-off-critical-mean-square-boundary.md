# Zhao 2025: off-critical mean-square and short-interval boundary

## Source and purpose

This note audits Tianyu Zhao,
"On the mean values of the error terms in Mertens' theorems",
Research in Number Theory 11, article 62 (2025),
[DOI 10.1007/s40993-025-00640-y](https://link.springer.com/article/10.1007/s40993-025-00640-y).

The audit asks which parts of the proposed Pintz--Carlson--explicit-formula
route are already present when zeros occur off the critical line.

Write

\[
  \Theta=\sup\{\Re\rho:\zeta(\rho)=0\}.
\]

## Existing off-critical `L2` result

Zhao's Lemma 8 records

\[
  X^{2\Theta+1-\varepsilon}
  \ll \int_X^{2X}(\psi(x)-x)^2\,dx
  \ll X^{2\Theta+1}
\]

when `Theta > 1/2`.  The upper bound is effective and uniform in `Theta`; the
lower bound is ineffective.  Thus neither of the following may be presented
as new:

- an off-critical-line mean-square upper bound for the PNT error;
- an `L2` lower bound whose polynomial scale is determined by the supremal
  real part of a zeta zero.

The proof relevant to this project expands a truncated explicit formula into
a double zero sum.  With fixed `0 < delta < Theta - 1/2`, it uses a kernel of
the form

\[
  \frac{1}
  {|\gamma_i\gamma_j|
   (\delta+|\gamma_i-\gamma_j|)}.
\]

The corresponding global double series converges.  This is genuine
off-critical pair-kernel precedent.

## Why it is not the proposed direct-`L2` tail

The argument is organized by the single global exponent `Theta`, not by
real-part strips and dynamic height blocks.  It does not expose:

- a Carlson input `N(sigma,T)`;
- a dyadic capacity with explicit polynomial and logarithmic exponents;
- analytic square-multiplicity mass;
- finite deletion of a selected rightmost cluster;
- a distinct-frequency Occupancy or Gram/Schur interface;
- a target-zero-normalized complement bound.

The distinction becomes especially sharp in Zhao's Lemma 11.  Its pair sum is
bounded by

\[
  \frac{1}{x(\log x)^2}
  \left(
    \sum_{|\gamma|\le x^2}\frac{x^\beta}{|\gamma|}
  \right)^2.
\]

The parenthesized quantity is then bounded by a zero-free-region PNT estimate.
Consequently this step returns to the square of a global `L1` zero mass.  It
does not retain the reciprocal-height square gain as a Carlson-weighted
coefficient mass, and it does not use local frequency orthogonality.

This provides a precise comparison:

- Zhao: pair kernel `->` global `L1` zero sum squared;
- proposed route: pair kernel `->` Gram/Schur Occupancy times dyadic
  `sum m(rho)^2 / |rho|^2` capacity.

## Existing short-interval oscillation

Zhao's Lemma 10 assumes a zero
`rho_0 = beta_0 + i gamma_0` with `beta_0 > 1/2 + epsilon`.  For every
sufficiently large `X`, it produces both signs at points

\[
  x_1,x_2\in[X,X^{1+\varepsilon}].
\]

For the integrated Mertens error used there, the scale is

\[
  \frac{x_j^{\beta_0}}
       {\gamma_0^{2+\varepsilon}\log x_j}.
\]

The paper also recalls Pintz's corresponding result for
`pi(x)-li(x)` at scale

\[
  \frac{x_j^{\beta_0}}
       {\gamma_0^{1+\varepsilon}\log x_j}.
\]

The proof is a power-sum argument with a Gaussian Mellin kernel and a second
zero chosen near the target zero.  It is therefore already precedent for all
of the following:

- the interval `[X,X^(1+epsilon)]`;
- both signs;
- an effective threshold depending on `epsilon` and the target ordinate;
- using a nearby zero in a finite oscillating package.

The proposed project must not claim any one of those features alone as new.

## Remaining sharp target

Zhao's result loses `gamma_0^epsilon` beyond the natural reciprocal-ordinate
scale and does not state a sharp `pi/2` oscillation constant.  Its arithmetic
object is also an integrated Mertens error, or `pi-li` in the cited Pintz
theorem, rather than the exact smoothed `psi-x` transfer currently being
assembled.

After this audit, the defensible target is the conjunction

\[
  [X,X^{1+\varepsilon}]
  \quad+\quad
  \frac{x^{\beta_0}}{|\rho_0|}
  \quad+\quad
  \text{sharp `pi/2`-level constant}
\]

for the actual zeta PNT error, with the complement controlled through a
real-part-stratified Carlson direct-`L2` theorem.  Each ingredient separately
has precedent; the candidate contribution is their quantitative and
machine-checked assembly without a `|rho_0|^epsilon` loss.

This remains a candidate novelty statement, not a literature-wide novelty
claim.

## Required theorem chain

The lower-transfer route should expose the following independent interfaces.

1. `actualDyadicLinearCapacity`:

   \[
     \sum_{\rho\in Z(\sigma,T)}m(\rho)
     \ll T^{q(\sigma)}(1+\log T)^4.
   \]

2. `actualDyadicSquareCapacity`:

   \[
     \sum_{\rho\in Z(\sigma,T)\setminus S}
       \frac{m(\rho)^2}{|\rho|^2}
     \ll T^{q(\sigma)-2}(1+\log T)^5.
   \]

   The extra logarithm is the explicit local maximum-multiplicity loss;
   finite `S` is removed by nonnegative monotonicity.

3. `distinctFrequencyOccupancy` supplied by the half-isolated component:

   \[
     \operatorname{Occ}(\sigma,T,H)
     \ll T^\theta(1+\log T)^r.
   \]

4. `dyadicBlockEnergy`:

   \[
     \|R_{\sigma,T}\|_2^2
     \ll
     H\,x^{2(\sigma-\beta_0)}
     T^{q(\sigma)-2+\theta}
     (1+\log T)^{5+r}.
   \]

5. `dynamicTailEnergy` obtained by summing the square roots of dyadic block
   energies and then squaring.  Strict negativity of every active exponent is
   required; equality is a genuine critical case, not decay.

6. `targetClusterTransfer`, combining the direct-`L2` complement with the
   exact triangle average and the finite-cluster lower bound.  The output
   constant remains parametric until an actual-zeta surplus over `pi/2` is
   proved.

This chain improves on the audited precedent only if it retains the stripwise
Carlson exponent and square-height gain all the way to step 6.  Collapsing step
4 to a squared global `L1` sum would reproduce the existing route rather than
advance it.
