import PrimeNumberTheorem.ZeroDensityLayerBudgetActualClosedRealAxisTargetDecay
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualOscillationBoundary

/-!
# Polynomial-height criterion for the actual explicit-formula remainder

This module isolates the uniform estimate needed to normalize the actual
explicit-formula approximation error. The existing fixed-`x` all-heights
estimate does not by itself construct this certificate: its constant may
depend on `x`. A uniform good-height or moving-height argument must supply the
eventual bound below.

Once that bound is available, the exact threshold is
`1 - beta < alpha`.
-/

open Filter Topology

namespace PrimeNumberTheorem

/-- Target-normalized polynomial logarithmic majorant. -/
noncomputable def actualPolynomialRemainderTargetMajorant
    (C beta alpha x : ℝ) : ℝ :=
  C * x ^ (1 - beta - alpha) * (1 + Real.log x) ^ 2

/-- A power margin absorbs the square logarithm in the polynomial-height
explicit-formula remainder. -/
theorem tendsto_actualPolynomialRemainderTargetMajorant
    {C beta alpha : ℝ} (hC : 0 ≤ C) (hmargin : 1 - beta < alpha) :
    Tendsto
      (actualPolynomialRemainderTargetMajorant C beta alpha)
      atTop (nhds 0) := by
  let exponent : ℝ := 1 - beta - alpha
  have hexponent : exponent < 0 := by
    dsimp [exponent]
    linarith
  let epsilon : ℝ := -exponent / 2
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    linarith
  have hstrict : exponent + epsilon < 0 := by
    dsimp [epsilon]
    linarith
  have hlogFour :
      Tendsto
        (fun x : ℝ => x ^ exponent * Real.log x ^ 4)
        atTop (nhds 0) :=
    tendsto_rpow_mul_log_four_atTop_nhds_zero hepsilon hstrict
  have hupper :
      Tendsto
        (fun x : ℝ =>
          4 * C * (x ^ exponent * Real.log x ^ 4))
        atTop (nhds 0) := by
    simpa using hlogFour.const_mul (4 * C)
  unfold actualPolynomialRemainderTargetMajorant
  change
    Tendsto
      (fun x : ℝ => C * x ^ exponent * (1 + Real.log x) ^ 2)
      atTop (nhds 0)
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    positivity
  · filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
    have hxpos : 0 < x := (Real.exp_pos 1).trans_le hx
    have hlog : 1 ≤ Real.log x :=
      (Real.le_log_iff_exp_le hxpos).2 hx
    have hpower : 0 ≤ x ^ exponent := Real.rpow_nonneg hxpos.le exponent
    have hlogBound :
        (1 + Real.log x) ^ 2 ≤ 4 * Real.log x ^ 4 := by
      nlinarith [sq_nonneg (Real.log x - 1),
        sq_nonneg (Real.log x ^ 2 - 1)]
    calc
      C * x ^ exponent * (1 + Real.log x) ^ 2 ≤
          C * x ^ exponent * (4 * Real.log x ^ 4) := by
        gcongr
      _ = 4 * C * (x ^ exponent * Real.log x ^ 4) := by ring

/-- A uniform polynomial-height bound for the signed actual explicit-formula
remainder. Constructing this certificate from the analytic contour machinery
is deliberately kept separate from the exponent arithmetic. -/
structure ActualPolynomialExplicitFormulaRemainderCertificate
    (alpha : ℝ) : Type where
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  eventually_bound :
    ∀ᶠ x : ℝ in atTop,
      |actualPNTExplicitFormulaRelativeRemainder
          (carlsonPolynomialHeight alpha) x| ≤
        constant * x ^ (-alpha) * (1 + Real.log x) ^ 2

/-- The uniform polynomial remainder certificate becomes target-negligible
exactly under the strict exponent margin `1 - beta < alpha`. -/
theorem ActualPolynomialExplicitFormulaRemainderCertificate.targetAmplitudeNegligible
    {beta alpha : ℝ}
    (certificate : ActualPolynomialExplicitFormulaRemainderCertificate alpha)
    (hmargin : 1 - beta < alpha) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (actualPNTExplicitFormulaRelativeRemainder
        (carlsonPolynomialHeight alpha)) := by
  let bound : ℝ → ℝ := fun x =>
    certificate.constant * x ^ (-alpha) * (1 + Real.log x) ^ 2
  have hboundNegligible :
      TargetAmplitudeNegligible
        (targetZeroPowerAmplitude beta) bound := by
    unfold TargetAmplitudeNegligible
    have htarget :=
      tendsto_actualPolynomialRemainderTargetMajorant
        certificate.constant_nonneg hmargin
    apply htarget.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hboundNonneg : 0 ≤ bound x := by
      dsimp [bound]
      exact mul_nonneg
        (mul_nonneg certificate.constant_nonneg
          (Real.rpow_nonneg hx.le (-alpha)))
        (sq_nonneg (1 + Real.log x))
    rw [abs_of_nonneg hboundNonneg]
    dsimp [bound, actualPolynomialRemainderTargetMajorant,
      targetZeroPowerAmplitude]
    rw [div_eq_mul_inv, ← Real.rpow_neg hx.le]
    have hpower :
        x ^ (-alpha) * x ^ (-(beta - 1)) =
          x ^ (1 - beta - alpha) := by
      rw [← Real.rpow_add hx]
      congr 1
      ring
    rw [← hpower]
    ring
  exact
    TargetAmplitudeNegligible.of_eventually_abs_le
      (targetZeroPowerAmplitude_eventually_pos beta)
      hboundNegligible certificate.eventually_bound

end PrimeNumberTheorem
