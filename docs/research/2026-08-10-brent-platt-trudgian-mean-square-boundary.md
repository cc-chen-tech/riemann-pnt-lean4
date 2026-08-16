# Brent--Platt--Trudgian mean-square boundary

## Scope

This note audits Richard Brent, David Platt, and Timothy Trudgian,
"The mean square of the error term in the prime number theorem",
Journal of Number Theory 238 (2022), 740--762
([arXiv:2008.06140](https://arxiv.org/abs/2008.06140),
[author final PDF](https://maths-people.anu.edu.au/~brent/pd/rpb274-final.pdf)).

The purpose is narrow: determine whether their result already supplies the
off-critical-line dyadic direct-`L2` zero-tail interface needed by the
Pintz--Carlson--explicit-formula project.

## What the paper proves

Put

\[
  I(X)=\int_X^{2X}(\psi(x)-x)^2\,dx.
\]

Under RH, the paper proves an explicit upper bound

\[
  \limsup_{X\to\infty}\frac{I(X)}{X^2}\le 0.8603.
\]

Its relevant zero-side constant is the global double series

\[
  B=\sum_{\rho_1,\rho_2}
  \left|
    \frac{2^{2+i(\gamma_1-\gamma_2)}-1}
         {\rho_1\overline{\rho_2}
          (2+i(\gamma_1-\gamma_2))}
  \right|,
\]

with `rho_j = 1/2 + i gamma_j`.  Theorem 3 bounds the complement of the
finite square `|gamma_1|, |gamma_2| <= T` by

\[
  \frac{10(\log T)^3+11(\log T)^2}{\pi^2T}.
\]

The proof fixes the larger ordinate, bounds the inner sum by the ordinary
zero-counting function `N(T)`, and then sums the outer tail.  Its kernel

\[
  \frac{1}{|\gamma_1\gamma_2|
    |2+i(\gamma_1-\gamma_2)|}
\]

does encode frequency interaction, but the proof discards cancellation and
estimates the pairwise absolute sum directly.

## Exact overlap with this project

The paper confirms three structural points used by the direct-`L2` route.

1. Squaring an explicit zero sum naturally produces a pair kernel depending
   on `gamma_1 - gamma_2`.
2. The reciprocal factors `1 / |rho|` become a summable high-zero tail after
   the pair kernel is used; pointwise `L1` summation is not the only route.
3. A tail of order `T^(-1) (log T)^3` is available on RH without invoking a
   spacing conjecture.

This is useful precedent for direct `L2`, but it is not the interface required
for a zero with `Re rho = beta > 1/2`.

## Non-overlap and remaining candidate contribution

The paper does not supply any of the following components.

- A decomposition into real-part strips `sigma <= Re rho < sigma + Delta`.
- A Carlson density input `N(sigma,T)` for zeros off the critical line.
- A dyadic absolute-height block certificate that can be evaluated at
  `T = x^gamma`.
- A finite-set deletion theorem for removing a designated rightmost cluster.
- A local Gram/Schur Occupancy parameter for a short logarithmic observation
  window.
- A transfer from such a tail to an actual-zeta short-interval oscillation at
  scale `x^beta / |rho_0|`.

Accordingly, the defensible novelty target is not "the first mean-square
explicit-formula tail".  It is the following conditional interface and its
machine-checked assembly:

> an off-critical-line, real-part-stratified, analytic-multiplicity-aware
> dyadic `L2` tail obtained from Carlson capacity plus a separate
> distinct-frequency Occupancy bound, with finite-cluster deletion, and then
> transferred through a smoothed actual-zeta explicit formula.

This statement remains a candidate contribution until a broader literature
search and the full theorem chain are complete.

## Multiplicity audit

The paper explicitly says that a one-zero sum gives a zero `rho` weight
`m_rho`, while a double sum gives `(rho_1,rho_2)` weight
`m_{rho_1} m_{rho_2}`.  It then defines

\[
  c_1=\sum_\rho \frac{m_\rho}{|\rho|^2}
\]

and says that, on RH, the diagonal terms of its double constant `c_2` sum to
`c_1`.  With a distinct-zero index and the stated product weighting, the
literal diagonal instead carries `m_rho^2`.  The equality is automatic only
under simplicity, or under a copy-indexing convention in which the meaning of
"diagonal" is changed.  A later footnote says that a subsequent argument is
written assuming simple zeros and can be modified for multiple zeros.

The formal route must not leave this convention implicit.  It will use:

- one index per distinct zero;
- coefficient `m_rho / rho`;
- square coefficient mass `m_rho^2 / |rho|^2`;
- Carlson linear mass `sum m_rho`;
- a local maximum-multiplicity bound to pass from linear to square mass;
- Occupancy only for distinct-frequency geometry.

This is exactly why the linear-to-square multiplicity theorem is a required
prerequisite rather than cosmetic bookkeeping.

## Consequence for the theorem chain

For a dyadic real-part strip `Z(sigma,T)` and nonnegative weight `w`, the
capacity layer should expose

\[
  \sum_{\rho\in Z(sigma,T)\setminus S}
    \frac{m(\rho)^2 w(\rho)}{|\rho|^2}
  \le
  M_{\max}(sigma,T)
  \sum_{\rho\in Z(sigma,T)}
    \frac{m(\rho) w(\rho)}{|\rho|^2}.
\]

Carlson controls the linear sum, nonnegative monotonicity removes the finite
set `S`, and the half-isolated component contributes only the Gram/Schur
Occupancy bound.  Unlike the RH double-series estimate above, this separation
keeps analytic multiplicity and frequency crowding as two different losses.

The comparison therefore sharpens, rather than invalidates, the current
direct-`L2` design.
