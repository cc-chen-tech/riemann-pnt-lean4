# Multiplicity-weighted Schur transfer from linear Carlson capacity

## Objective

The existing safe route to a dyadic zero-block energy bound is

\[
  \text{linear multiplicity capacity}
  \longrightarrow
  \text{square multiplicity capacity}
  \longrightarrow
  \text{distinct-frequency Occupancy}.
\]

If the Carlson count costs `(log T)^4`, local maximum multiplicity costs one
logarithm, and distinct-frequency Occupancy costs one logarithm, this produces
`(log T)^6`.

There is a sharper route.  A multiplicity-weighted Schur row bound can consume
the linear Carlson mass directly.  For the triangular observation window, the
row bound follows from the ordinary local zero count with multiplicity and
costs only one logarithm.  The resulting block energy has log loss five.

This is an application of the weighted Schur test, not a claim that the
underlying functional-analytic inequality is new.  The contribution sought
here is its explicit, multiplicity-correct integration into the
Carlson--Pintz transfer.

## 1. Finite weighted-Schur lemma

Let `I` be finite.  Suppose

- `m_i >= 0`;
- `a_i` is complex;
- `K_ij` is complex;
- `A_ij >= 0` is symmetric;
- `|K_ij| <= A_ij`;
- `sum_j m_j A_ij <= O` for every `i`.

Then

\[
  \left|
    \sum_{i,j}m_i m_j a_i\overline{a_j}K_{ij}
  \right|
  \le
  O\sum_i m_i|a_i|^2.
\]

Indeed,

\[
\begin{aligned}
  \left|\sum_{i,j}m_i m_j a_i\overline{a_j}K_{ij}\right|
  &\le \sum_{i,j}m_i m_j|a_i||a_j|A_{ij}\\
  &\le \frac12\sum_{i,j}m_i m_j
       (|a_i|^2+|a_j|^2)A_{ij}\\
  &=\sum_i m_i|a_i|^2\sum_jm_jA_{ij}\\
  &\le O\sum_i m_i|a_i|^2.
\end{aligned}
\]

The equality in the third line is exactly where symmetry of `A` is used.

The diagonal term has coefficient `m_i^2`, but no multiplicity is lost: the
row sum `O` itself contains the diagonal contribution `m_i A_ii`.  Extracting
`max m_i` before applying Schur would pay for the same multiplicity twice.

## 2. Finite-set deletion

For `J = I \ S`, with `S` arbitrary and finite,

\[
  \sum_{j\in J}m_jA_{ij}
  \le \sum_{j\in I}m_jA_{ij}
\]

by nonnegativity.  Likewise,

\[
  \sum_{i\in J}m_i|a_i|^2
  \le \sum_{i\in I}m_i|a_i|^2.
\]

Thus the same constant `O` controls every deleted block.  No new density
theorem and no new local-zero theorem is required for a selected finite
cluster `S`.

## 3. Triangular observation window

For `L > 0`, define the normalized triangle

\[
  W_L(u)=\frac1L\left(1-\frac{|u|}{L}\right)_+.
\]

It has integral one, support `[-L,L]`, and Fourier transform

\[
  \widehat W_L(v)
  =\left(\frac{\sin(Lv/2)}{Lv/2}\right)^2.
\]

Consequently

\[
  |\widehat W_L(v)|
  \le \min\left(1,\frac{4}{L^2v^2}\right).
\]

For

\[
  F(u)=\sum_i m_i a_i e^{i\gamma_i u},
\]

the normalized triangular energy is

\[
  \int_{-L}^{L}W_L(u)|F(u)|^2\,du
  =\sum_{i,j}m_i m_j a_i\overline{a_j}
    \widehat W_L(\gamma_i-\gamma_j).
\]

Hence the finite weighted-Schur lemma applies with

\[
  A_{ij}=\min\left(
    1,\frac{4}{L^2(\gamma_i-\gamma_j)^2}
  \right),
\]

where the value at equal ordinates is one.

The square decay is essential for the sharp log ledger.  A box window gives
only `1 / (L |gamma_i-gamma_j|)` decay and an additional harmonic logarithm.

## 4. Weighted row occupancy from local zero counting

Assume the ordinates lie in an absolute-height block comparable to `T`, and
suppose every interval of length at most one in that block contains analytic
zero multiplicity at most

\[
  U(T)\le C(1+\log T).
\]

Take `L >= 1`.  For fixed `i`, split the other ordinates into

\[
  B_0=\{j:|\gamma_j-\gamma_i|<1/L\}
\]

and, for `k >= 1`,

\[
  B_k=\{j:k/L\le|\gamma_j-\gamma_i|<(k+1)/L\}.
\]

The near block has weighted cardinality at most `U(T)`.  Each `B_k` is
contained in two intervals of length `1/L <= 1`, so its weighted cardinality
is at most `2 U(T)`.  Therefore

\[
\begin{aligned}
  \sum_jm_jA_{ij}
  &\le U(T)+8U(T)\sum_{k\ge1}\frac1{k^2}\\
  &=\left(1+\frac{4\pi^2}{3}\right)U(T).
\end{aligned}
\]

This count includes multiplicity.  It simultaneously handles repeated zeros,
distinct zeros with the same ordinate, and very close ordinates.  No zero
separation conjecture is used.

The Riemann--von Mangoldt formula and its standard explicit error bound give
`U(T) = O(1 + log T)` for actual zeta zeros counted with analytic
multiplicity.  Restricting to a real-part strip can only decrease the row
mass.

## 5. Carlson block capacity

Let the dyadic real-part strip be

\[
  Z(\sigma_L,\sigma_R,T)
  =\{\rho:\sigma_L\le\Re\rho<\sigma_R,
              T\le|\Im\rho|<2T\}.
\]

Suppose Carlson supplies the linear analytic-multiplicity count

\[
  \sum_{\rho\in Z}m(\rho)
  \ll T^{q(\sigma_L)}(1+\log T)^4,
  \qquad q(\sigma)=4\sigma(1-\sigma).
\]

Since `|rho| >= T` on the block,

\[
  \sum_{\rho\in Z}\frac{m(\rho)}{|\rho|^2}
  \ll T^{q(\sigma_L)-2}(1+\log T)^4.
\]

Combining this with the multiplicity-weighted row bound gives

\[
  \text{block energy}
  \ll
  T^{q(\sigma_L)-2}(1+\log T)^5
\]

before the real-part and target-normalization factors are inserted.

There is no separate maximum-multiplicity loss.

## 6. Real-part exponent on a short multiplicative interval

Let the target real part be `beta`, and let

\[
  x\in[X,X^\lambda],\qquad \lambda=1+\varepsilon.
\]

For a strip with upper edge `sigma_R`, define the support function

\[
  \kappa_\lambda(a)=
  \begin{cases}
    a,&a\le0,\\
    \lambda a,&a\ge0.
  \end{cases}
\]

Then

\[
  \sup_{X\le x\le X^\lambda}x^{2(\sigma_R-\beta)}
  =X^{2\kappa_\lambda(\sigma_R-\beta)}.
\]

This piecewise exponent is necessary.  Multiplying a negative exponent by
`lambda` would underestimate the left-of-target strips.

For `T = X^gamma`, the normalized block-energy exponent is therefore

\[
  E_{L2}(\sigma_L,\sigma_R,\gamma)
  =2\kappa_\lambda(\sigma_R-\beta)
   +\gamma(q(\sigma_L)-2).
\]

The block decays exactly when this exponent is strictly negative.  Equality is
a critical case and does not give a summable infinite dyadic tail.

## 7. Dyadic summation

If every block exponent is at most `-delta < 0`, its normalized squared norm
has the form

\[
  E_k\ll 2^{-k\delta}(1+\log(2^kT))^5.
\]

Minkowski must be applied to `sqrt(E_k)`, not directly to `E_k`.  The geometric
sum of square roots converges, and squaring back preserves both the
polynomial exponent and the fifth logarithmic power.

At `delta = 0`, the dyadic norms are not summable.  A finite outer cutoff only
replaces divergence by an explicit number-of-blocks loss; it does not create
decay.

## 8. Comparison with the square-multiplicity route

The already available fallback has the ledger

\[
  \underbrace{(\log T)^4}_{\text{Carlson linear count}}
  \cdot
  \underbrace{(\log T)}_{\max m}
  \cdot
  \underbrace{(\log T)}_{\text{distinct Occupancy}}
  =(\log T)^6.
\]

The weighted-Schur route has

\[
  \underbrace{(\log T)^4}_{\text{Carlson linear count}}
  \cdot
  \underbrace{(\log T)}_{\text{multiplicity-weighted row count}}
  =(\log T)^5.
\]

If only an unweighted Occupancy estimate is available, converting it by
`max m` recovers the old log loss.  The improvement is real only when the row
count is proved directly with analytic multiplicity, as the local zeta
zero-counting bound permits.

## 9. Proposed formal interfaces

The abstract arithmetic layer should eventually expose the following small
theorem chain.

1. `weightedSchurEnergy_le`:
   the finite symmetric-kernel inequality of Section 1.
2. `weightedSchurEnergy_mono`:
   restriction to an arbitrary subset preserves the bound.
3. `triangleKernel_abs_le`:
   the `min(1, 4 / (L^2 delta^2))` Fourier estimate.
4. `weightedTriangleRow_le_of_localMass`:
   local multiplicity count implies the explicit row constant
   `(1 + 4*pi^2/3) U`.
5. `linearCarlson_triangleEnergy`:
   the actual dyadic strip energy with exponent `q(sigma_L)-2` and log loss
   five.
6. `linearCarlson_triangleEnergy_delete`:
   the same theorem after deleting a finite target cluster.

The first two are elementary finite-sum algebra.  The third and fourth are
the only new analytic adapters.  The fifth and sixth should reuse the actual
Carlson shell-mass theorem already merged into `main`.

No theorem in this chain proves the sharp oscillation lower bound.  It only
provides the complement estimate consumed by that independently owned
component.
