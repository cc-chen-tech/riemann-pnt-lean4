import PrimeNumberTheorem.ZeroDensityLayerBudgetRelativeKernelBound

/-!
# Automatic Pintz bounds for positive-ordinate PNT zero kernels

Pintz's zero cost contains the denominator contribution `log rho.im`.
Since `rho.im ≤ ‖rho‖` for a positive-ordinate zero, the exact relative PNT
kernel norm is automatically bounded by the exponential of the negative Pintz
envelope.  No auxiliary lower bound `‖rho‖ ≥ 1` is needed on this half-plane.
-/

open Complex
open scoped BigOperators

namespace PrimeNumberTheorem

/-- Exponential form of the exact relative simple-kernel norm. -/
theorem norm_pntRelativeSimpleZeroKernel_eq_exp_neg_zeroCost
    {x : ℝ} (hx : 0 < x) {rho : ℂ} (hrho : rho ≠ 0) :
    ‖pntRelativeSimpleZeroKernel x rho‖ =
      Real.exp
        (-((1 - rho.re) * Real.log x + Real.log ‖rho‖)) := by
  have hnorm : 0 < ‖rho‖ :=
    norm_pos_iff.mpr hrho
  calc
    ‖pntRelativeSimpleZeroKernel x rho‖ =
        x ^ (rho.re - 1) / ‖rho‖ :=
      norm_pntRelativeSimpleZeroKernel_eq hx rho
    _ = Real.exp (Real.log x * (rho.re - 1)) / ‖rho‖ := by
      rw [Real.rpow_def_of_pos hx]
    _ = Real.exp (Real.log x * (rho.re - 1)) /
        Real.exp (Real.log ‖rho‖) := by
      rw [Real.exp_log hnorm]
    _ = Real.exp
        (Real.log x * (rho.re - 1) - Real.log ‖rho‖) := by
      rw [Real.exp_sub]
    _ = Real.exp
        (-((1 - rho.re) * Real.log x + Real.log ‖rho‖)) := by
      congr 1
      ring

/-- Every positive-ordinate nontrivial zero satisfies the relative Pintz
kernel majorant directly from the definition of the global envelope. -/
theorem norm_pntRelativeSimpleZeroKernel_le_exp_neg_pintzEnvelope
    {x : ℝ} (hx : 1 ≤ x) {rho : ℂ}
    (hrho : RiemannHypothesis.IsNontrivialZero rho)
    (him : 0 < rho.im) :
    ‖pntRelativeSimpleZeroKernel x rho‖ ≤
      Real.exp (-Pintz.pintzZeroEnvelope x) := by
  have himnorm : rho.im ≤ ‖rho‖ := by
    calc
      rho.im ≤ |rho.im| := le_abs_self _
      _ ≤ ‖rho‖ := Complex.abs_im_le_norm rho
  have hnorm : 0 < ‖rho‖ :=
    him.trans_le himnorm
  have hlog :
      Real.log rho.im ≤ Real.log ‖rho‖ :=
    Real.log_le_log him himnorm
  have henvelope :
      Pintz.pintzZeroEnvelope x ≤
        (1 - rho.re) * Real.log x + Real.log ‖rho‖ := by
    calc
      Pintz.pintzZeroEnvelope x ≤ Pintz.pintzZeroTerm x rho :=
        Pintz.pintzZeroEnvelope_le_zeroTerm hx hrho him
      _ ≤ (1 - rho.re) * Real.log x + Real.log ‖rho‖ := by
        simpa [Pintz.pintzZeroTerm] using
          add_le_add_left hlog ((1 - rho.re) * Real.log x)
  rw [norm_pntRelativeSimpleZeroKernel_eq_exp_neg_zeroCost
    (lt_of_lt_of_le zero_lt_one hx) (norm_pos_iff.mp hnorm)]
  exact Real.exp_le_exp.mpr (neg_le_neg henvelope)

/-- The positive-ordinate multiplicity-weighted PNT zero sum satisfies the
Carlson aggregate with no additional pointwise kernel hypotheses. -/
theorem PositiveZeroBucketInput.norm_positive_pntRelativeZeroContribution_sum_le_pintz
    {T x : ℝ} {n : ℕ} (input : PositiveZeroBucketInput T n)
    (hx : 1 ≤ x) :
    ‖∑ rho ∈ positiveNontrivialZerosFinset T,
        pntRelativeZeroContribution x rho‖ ≤
      pintzCarlsonClassicalAggregatedDensityLayerTerm
        (Finset.univ : Finset (Fin n)) input.sigma () x T := by
  apply input.norm_positive_pntRelativeZeroContribution_sum_le
  intro i rho hrho
  have hpositive : rho ∈ positiveNontrivialZerosFinset T :=
    (Finset.mem_filter.mp hrho).1
  have hzero := mem_positiveNontrivialZerosFinset.mp hpositive
  exact norm_pntRelativeSimpleZeroKernel_le_exp_neg_pintzEnvelope
    hx hzero.1 hzero.2.1

/-- The full multiplicity-weighted relative PNT zero sum is bounded
automatically by twice the positive Carlson aggregate plus the explicit
real-ordinate residual. -/
theorem PositiveZeroBucketInput.norm_full_pntRelativeZeroContribution_sum_le_pintz
    {T x : ℝ} {n : ℕ} (input : PositiveZeroBucketInput T n)
    (hx : 1 ≤ x) :
    ‖∑ rho ∈ nontrivialZerosFinset T,
        pntRelativeZeroContribution x rho‖ ≤
      2 * pintzCarlsonClassicalAggregatedDensityLayerTerm
        (Finset.univ : Finset (Fin n)) input.sigma () x T +
      ‖∑ rho ∈ realOrdinateNontrivialZerosFinset T,
        pntRelativeZeroContribution x rho‖ := by
  apply input.norm_full_pntRelativeZeroContribution_sum_le_weighted
    (lt_of_lt_of_le zero_lt_one hx)
  intro i rho hrho
  have hpositive : rho ∈ positiveNontrivialZerosFinset T :=
    (Finset.mem_filter.mp hrho).1
  have hzero := mem_positiveNontrivialZerosFinset.mp hpositive
  exact norm_pntRelativeSimpleZeroKernel_le_exp_neg_pintzEnvelope
    hx hzero.1 hzero.2.1

end PrimeNumberTheorem
