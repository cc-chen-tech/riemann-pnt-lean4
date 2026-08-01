import PrimeNumberTheorem.ZeroDensityLayerBudgetStrictMarginExponentialCoreRateGap
import PrimeNumberTheorem.ZeroDensityLayerBudgetTargetAmplitudeBarrier

/-!
# Power-to-square-root-log amplitude transfer

Every fixed decaying power scale is negligible relative to every
square-root-log exponential scale. Existing power-normalized closed-term
estimates therefore transfer automatically to the slower comparison scale.
-/

namespace PrimeNumberTheorem

open Filter Topology

/-- A fixed power amplitude is negligible relative to every square-root-log
exponential amplitude. -/
theorem tendsto_targetZeroPowerAmplitude_div_pntSqrtLogExponentialAmplitude_zero
    {beta : ℝ} (hbeta : beta < 1) (rate : ℝ) :
    Tendsto
      (fun m : ℕ =>
        targetZeroPowerAmplitude beta (m : ℝ) /
          pntSqrtLogExponentialAmplitude rate m)
      atTop (nhds 0) := by
  have hinverse := tendsto_inv_atTop_zero.comp
    (pntContourKernelToTargetAmplitudeRatio_tendsto_atTop hbeta rate)
  apply hinverse.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  have hmpos : 0 < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hm)
  unfold pntContourKernelToTargetAmplitudeRatio
    pntSqrtLogExponentialAmplitude targetZeroPowerAmplitude
  rw [Real.rpow_def_of_pos hmpos]
  simp only [Function.comp_apply]
  rw [inv_div]
  congr 2
  ring

/-- Natural-point negligibility transfers from a fixed power amplitude to any
square-root-log exponential amplitude. -/
theorem NaturalPointTargetAmplitudeNegligible.toSqrtLogExponentialAmplitude
    {beta rate : ℝ} (hbeta : beta < 1) {remainder : ℕ → ℝ}
    (hnegligible :
      NaturalPointTargetAmplitudeNegligible
        (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))
        remainder) :
    NaturalPointTargetAmplitudeNegligible
      (pntSqrtLogExponentialAmplitude rate) remainder := by
  have hratio :=
    tendsto_targetZeroPowerAmplitude_div_pntSqrtLogExponentialAmplitude_zero
      hbeta rate
  unfold NaturalPointTargetAmplitudeNegligible at hnegligible ⊢
  have hproduct := hnegligible.mul hratio
  have hpower := eventually_naturalPoint_pos_of_eventually_pos
    (targetZeroPowerAmplitude_eventually_pos beta)
  have heq :
      (fun m : ℕ =>
        (|remainder m| / targetZeroPowerAmplitude beta (m : ℝ)) *
          (targetZeroPowerAmplitude beta (m : ℝ) /
            pntSqrtLogExponentialAmplitude rate m)) =ᶠ[atTop]
        (fun m : ℕ =>
          |remainder m| / pntSqrtLogExponentialAmplitude rate m) := by
    filter_upwards [hpower] with m hm
    field_simp [ne_of_gt hm, Real.exp_ne_zero]
  simpa only [mul_zero] using hproduct.congr' heq

/-- The closed logarithmic explicit-formula term is negligible relative to
every square-root-log exponential amplitude. -/
theorem classicalClosedLogRelativeMajorant_sqrtLogAmplitudeNegligible
    (rate : ℝ) :
    NaturalPointTargetAmplitudeNegligible
      (pntSqrtLogExponentialAmplitude rate)
      classicalClosedLogRelativeMajorant := by
  exact NaturalPointTargetAmplitudeNegligible.toSqrtLogExponentialAmplitude
    (rate := rate) (show (1 / 2 : ℝ) < 1 by norm_num)
    (selectedNaturalClosedLogRelative_targetNegligible
      (show (0 : ℝ) < 1 / 2 by norm_num))

/-- The actual closed real-axis term is negligible relative to every
square-root-log exponential amplitude at natural points. -/
theorem actualPNTClosedRealAxisRelativeTerm_sqrtLogAmplitudeNegligible
    (rate : ℝ) :
    NaturalPointTargetAmplitudeNegligible
      (pntSqrtLogExponentialAmplitude rate)
      (fun m : ℕ => actualPNTClosedRealAxisRelativeTerm (m : ℝ)) := by
  exact NaturalPointTargetAmplitudeNegligible.toSqrtLogExponentialAmplitude
    (rate := rate) (show (1 / 2 : ℝ) < 1 by norm_num)
    ((actualPNTClosedRealAxisRelativeTerm_targetAmplitudeNegligible
      (show (0 : ℝ) < 1 / 2 by norm_num)).naturalPoint)

/-- Once the explicit `sqrt(log m) / m` tail is normalized, the entire
rate-independent residual is normalized on the same scale. -/
theorem tendsto_actualStrictMarginRateIndependentResidual_div_amplitude_zero_of_tail
    (rate : ℝ)
    (htail :
      Tendsto
        (fun m : ℕ =>
          (2 * cofinalPNTZeroDepthTailConstant * pntSqrtLog m / (m : ℝ)) /
            pntSqrtLogExponentialAmplitude rate m)
        atTop (nhds 0)) :
    Tendsto
      (fun m : ℕ =>
        actualStrictMarginRateIndependentResidual m /
          pntSqrtLogExponentialAmplitude rate m)
      atTop (nhds 0) := by
  have hlog :=
    classicalClosedLogRelativeMajorant_sqrtLogAmplitudeNegligible rate
  have hreal :=
    actualPNTClosedRealAxisRelativeTerm_sqrtLogAmplitudeNegligible rate
  unfold NaturalPointTargetAmplitudeNegligible at hlog hreal
  have hlog' : Tendsto
      (fun m : ℕ =>
        classicalClosedLogRelativeMajorant m /
          pntSqrtLogExponentialAmplitude rate m)
      atTop (nhds 0) := by
    apply hlog.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    rw [abs_of_nonneg]
    unfold classicalClosedLogRelativeMajorant
    positivity
  have hreal' : Tendsto
      (fun m : ℕ =>
        |actualPNTClosedRealAxisRelativeTerm (m : ℝ)| /
          pntSqrtLogExponentialAmplitude rate m)
      atTop (nhds 0) := by
    simpa only [abs_abs] using hreal
  convert (htail.add hlog').add hreal' using 1
  · funext m
    unfold actualStrictMarginRateIndependentResidual
    ring
  · simp

end PrimeNumberTheorem
