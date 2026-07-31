# Distinct complementary-zero witness

## Closed implication

Let \(S\) be any finite set of already selected complex numbers and let
\(Z(T)\) be the finite multiset support of nontrivial zeta zeros up to height
\(T\).  The canonical moving complement uses exactly

\[
Z(T)\setminus S.
\]

If \(Z(T)\subseteq S\), its contribution is identically zero and hence its
Gaussian energy is zero.  Taking the contrapositive gives

\[
E_{\mathrm{full}}(S,T)>0
\quad\Longrightarrow\quad
\exists\rho\in Z(T),\ \rho\notin S.
\]

Lean endpoint:
`exists_nontrivialZero_not_mem_of_fullMovingGaussianSecondMoment_pos`.

Combining this with the exact residual decomposition proves the stronger
usable criterion

\[
R_{S,T}>
3\left(
  \eta^2+
  (e^{-\beta a}B_{\mathrm{closed}})^2
\right)
\quad\Longrightarrow\quad
\exists\rho\in Z(T)\setminus S,
\]

provided the finite-height approximation is uniformly bounded by \(\eta\)
on the window.  This is
`exists_nontrivialZero_not_mem_of_remainder_energy_gt_three_errors`.

## Value for duplicate-free iteration

The witness is automatically outside the entire previously selected set
\(S\).  Thus no additional combinatorial de-duplication is needed at one
iteration step.  If a positive surplus can be re-established after adjoining
the witness to \(S\), the next application must produce a different zero.

## Exact blocker

The current off-line-zero theorem supplies the required residual lower bound
only for \(S=\varnothing\).  In that case the witness may simply be the
original target zero, so it gives no growing count.

The missing mathematical input is therefore:

> after absorbing a finite set of previously found zeros, prove that the
> selected-cluster residual still exceeds three times the approximation and
> closed-term budgets on a later window.

Neither Carlson's zero-density upper bound nor the current local oscillation
theorem provides this persistence.  A fixed finite cluster is compatible
with every presently available growing zero-density upper majorant.

No growing family, zero-density contradiction, zero exclusion, or RH is
claimed.
