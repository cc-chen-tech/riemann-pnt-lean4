import PrimeNumberTheorem.ZeroDensityLayerBudgetMultiplicityWeightedAggregation

/-!
# Relative PNT zero-kernel bounds from real-part gaps

The relative simple zero kernel has exact norm
`x ^ (rho.re - 1) / ‖rho‖`.  A lower bound on `‖rho‖` and a layerwise
real-part gap therefore discharge the abstract kernel hypothesis used by the
Carlson aggregation theorem.

The denominator hypothesis is kept explicit: low-height zeros must be split
off and controlled separately rather than silently absorbed into the density
budget.
-/

open Complex
open scoped BigOperators

namespace PrimeNumberTheorem

/-- Exact norm of the relative simple PNT zero kernel. -/
theorem norm_pntRelativeSimpleZeroKernel_eq
    {x : ℝ} (hx : 0 < x) (rho : ℂ) :
    ‖pntRelativeSimpleZeroKernel x rho‖ =
      x ^ (rho.re - 1) / ‖rho‖ := by
  rw [pntRelativeSimpleZeroKernel, norm_mul, norm_inv, norm_neg, norm_div,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hx, Real.rpow_sub_one hx.ne']
  ring

/-- A pointwise envelope inequality and `‖rho‖ ≥ 1` imply the desired
exponential kernel majorant. -/
theorem norm_pntRelativeSimpleZeroKernel_le_exp_neg_envelope
    {x : ℝ} (hx : 0 < x) {rho : ℂ}
    (hnorm : 1 ≤ ‖rho‖)
    (henvelope :
      Pintz.pintzZeroEnvelope x ≤
        (1 - rho.re) * Real.log x) :
    ‖pntRelativeSimpleZeroKernel x rho‖ ≤
      Real.exp (-Pintz.pintzZeroEnvelope x) := by
  have hnormpos : 0 < ‖rho‖ :=
    lt_of_lt_of_le zero_lt_one hnorm
  have hpow : 0 ≤ x ^ (rho.re - 1) :=
    Real.rpow_nonneg (le_of_lt hx) _
  have hdiv :
      x ^ (rho.re - 1) / ‖rho‖ ≤
        x ^ (rho.re - 1) := by
    rw [div_le_iff₀ hnormpos]
    have hmul :
        0 ≤ x ^ (rho.re - 1) * (‖rho‖ - 1) :=
      mul_nonneg hpow (sub_nonneg.mpr hnorm)
    nlinarith
  have hexponent :
      Real.log x * (rho.re - 1) ≤
        -Pintz.pintzZeroEnvelope x := by
    calc
      Real.log x * (rho.re - 1) =
          -((1 - rho.re) * Real.log x) := by ring
      _ ≤ -Pintz.pintzZeroEnvelope x :=
        neg_le_neg henvelope
  calc
    ‖pntRelativeSimpleZeroKernel x rho‖ =
        x ^ (rho.re - 1) / ‖rho‖ :=
      norm_pntRelativeSimpleZeroKernel_eq hx rho
    _ ≤ x ^ (rho.re - 1) := hdiv
    _ = Real.exp (Real.log x * (rho.re - 1)) :=
      Real.rpow_def_of_pos hx _
    _ ≤ Real.exp (-Pintz.pintzZeroEnvelope x) :=
      Real.exp_le_exp.mpr hexponent

/-- A conventional real-part strip `rho.re ≤ 1 - delta` implies the pointwise
envelope condition whenever `delta * log x` dominates the Pintz envelope. -/
theorem norm_pntRelativeSimpleZeroKernel_le_exp_neg_envelope_of_realPartGap
    {x delta : ℝ} (hx : 1 ≤ x) {rho : ℂ}
    (hnorm : 1 ≤ ‖rho‖)
    (hre : rho.re ≤ 1 - delta)
    (henvelope :
      Pintz.pintzZeroEnvelope x ≤ delta * Real.log x) :
    ‖pntRelativeSimpleZeroKernel x rho‖ ≤
      Real.exp (-Pintz.pintzZeroEnvelope x) := by
  have hdelta : delta ≤ 1 - rho.re := by
    linarith
  have hgap :
      Pintz.pintzZeroEnvelope x ≤
        (1 - rho.re) * Real.log x := by
    calc
      Pintz.pintzZeroEnvelope x ≤ delta * Real.log x :=
        henvelope
      _ ≤ (1 - rho.re) * Real.log x :=
        mul_le_mul_of_nonneg_right hdelta (Real.log_nonneg hx)
  exact norm_pntRelativeSimpleZeroKernel_le_exp_neg_envelope
    (lt_of_lt_of_le zero_lt_one hx) hnorm hgap

/-- Layerwise real-part gaps discharge the positive-ordinate aggregation
kernel hypothesis. -/
theorem PositiveZeroBucketInput.norm_positive_pntRelativeZeroContribution_sum_le_of_realPartGaps
    {T x : ℝ} {n : ℕ} (input : PositiveZeroBucketInput T n)
    (delta : Fin n → ℝ)
    (hx : 1 ≤ x)
    (hnorm : ∀ i, ∀ rho ∈ input.layer i, 1 ≤ ‖rho‖)
    (hre : ∀ i, ∀ rho ∈ input.layer i, rho.re ≤ 1 - delta i)
    (henvelope :
      ∀ i, Pintz.pintzZeroEnvelope x ≤ delta i * Real.log x) :
    ‖∑ rho ∈ positiveNontrivialZerosFinset T,
        pntRelativeZeroContribution x rho‖ ≤
      pintzCarlsonClassicalAggregatedDensityLayerTerm
        (Finset.univ : Finset (Fin n)) input.sigma () x T := by
  apply input.norm_positive_pntRelativeZeroContribution_sum_le
  intro i rho hrho
  exact
    norm_pntRelativeSimpleZeroKernel_le_exp_neg_envelope_of_realPartGap
      hx (hnorm i rho hrho) (hre i rho hrho) (henvelope i)

/-- Layerwise real-part gaps and the denominator guard give the full
multiplicity-weighted relative PNT zero-sum bound, with the real-ordinate
residual still explicit. -/
theorem PositiveZeroBucketInput.norm_full_pntRelativeZeroContribution_sum_le_of_realPartGaps
    {T x : ℝ} {n : ℕ} (input : PositiveZeroBucketInput T n)
    (delta : Fin n → ℝ)
    (hx : 1 ≤ x)
    (hnorm : ∀ i, ∀ rho ∈ input.layer i, 1 ≤ ‖rho‖)
    (hre : ∀ i, ∀ rho ∈ input.layer i, rho.re ≤ 1 - delta i)
    (henvelope :
      ∀ i, Pintz.pintzZeroEnvelope x ≤ delta i * Real.log x) :
    ‖∑ rho ∈ nontrivialZerosFinset T,
        pntRelativeZeroContribution x rho‖ ≤
      2 * pintzCarlsonClassicalAggregatedDensityLayerTerm
        (Finset.univ : Finset (Fin n)) input.sigma () x T +
      ‖∑ rho ∈ realOrdinateNontrivialZerosFinset T,
        pntRelativeZeroContribution x rho‖ := by
  apply input.norm_full_pntRelativeZeroContribution_sum_le_weighted
    (lt_of_lt_of_le zero_lt_one hx)
  intro i rho hrho
  exact
    norm_pntRelativeSimpleZeroKernel_le_exp_neg_envelope_of_realPartGap
      hx (hnorm i rho hrho) (hre i rho hrho) (henvelope i)

end PrimeNumberTheorem
