import PrimeNumberTheorem.ZeroDensityLayerBudgetActualExplicitFormulaClusterDecomposition
import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonLogAbsorption

/-!
# Target-normalized decay of the actual closed real-axis term

The fixed logarithmic term and the trivial-zero logarithm in the truncated
explicit formula are negligible relative to `x^(beta - 1)` whenever
`0 < beta`. This closes the closed-term hypothesis in the concrete cluster
transfer without making any assertion about the contour remainder.
-/

open Filter Topology

namespace PrimeNumberTheorem

/-- Real numerator of the closed real-axis contribution. -/
noncomputable def actualPNTClosedRealAxisNumerator (x : ℝ) : ℝ :=
  -Real.log (2 * Real.pi) -
    (1 / 2 : ℝ) * Real.log (1 - x ^ (-2 : ℝ))

/-- The complex presentation used by the exact explicit formula is the real
closed numerator divided by the evaluation point. -/
theorem actualPNTClosedRealAxisRelativeTerm_eq (x : ℝ) :
    actualPNTClosedRealAxisRelativeTerm x =
      actualPNTClosedRealAxisNumerator x / x := by
  simp [actualPNTClosedRealAxisRelativeTerm,
    actualPNTClosedRealAxisNumerator]

/-- The trivial-zero logarithm in the closed numerator tends to zero. -/
theorem tendsto_log_one_sub_rpow_neg_two_atTop :
    Tendsto
      (fun x : ℝ => Real.log (1 - x ^ (-2 : ℝ)))
      atTop (nhds 0) := by
  have hpower :
      Tendsto (fun x : ℝ => x ^ (-2 : ℝ)) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have hone :
      Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hargument :
      Tendsto (fun x : ℝ => 1 - x ^ (-2 : ℝ)) atTop (nhds 1) :=
    by simpa using hone.sub hpower
  have hlog :=
    (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
      hargument
  simpa using hlog

/-- The closed numerator has a finite limit. -/
theorem tendsto_actualPNTClosedRealAxisNumerator :
    Tendsto actualPNTClosedRealAxisNumerator atTop
      (nhds (-Real.log (2 * Real.pi))) := by
  have hconstant :
      Tendsto
        (fun _ : ℝ => -Real.log (2 * Real.pi))
        atTop (nhds (-Real.log (2 * Real.pi))) :=
    tendsto_const_nhds
  unfold actualPNTClosedRealAxisNumerator
  simpa using
    hconstant.sub
      (tendsto_log_one_sub_rpow_neg_two_atTop.const_mul (1 / 2 : ℝ))

/-- The actual closed real-axis term is negligible on every positive target
zero-power scale. -/
theorem actualPNTClosedRealAxisRelativeTerm_targetAmplitudeNegligible
    {beta : ℝ} (hbeta : 0 < beta) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      actualPNTClosedRealAxisRelativeTerm := by
  have hproduct :
      Tendsto
        (fun x : ℝ =>
          |actualPNTClosedRealAxisNumerator x| * x ^ (-beta))
        atTop (nhds 0) := by
    simpa using
      tendsto_actualPNTClosedRealAxisNumerator.abs.mul
        (tendsto_rpow_neg_atTop hbeta)
  unfold TargetAmplitudeNegligible
  apply hproduct.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [actualPNTClosedRealAxisRelativeTerm_eq,
    targetZeroPowerAmplitude, abs_div, abs_of_pos hx, div_div]
  have hpower : x * x ^ (beta - 1) = x ^ beta := by
    nth_rewrite 1 [← Real.rpow_one x]
    rw [← Real.rpow_add hx]
    congr 1
    ring
  rw [hpower, div_eq_mul_inv, ← Real.rpow_neg hx.le]

end PrimeNumberTheorem
