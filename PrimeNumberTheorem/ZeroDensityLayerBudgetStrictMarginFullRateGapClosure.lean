import PrimeNumberTheorem.ZeroDensityLayerBudgetPowerToSqrtLogAmplitudeTransfer

/-!
# Closure of the strict-margin full rate gap

The remaining `sqrt(log m) / m` tail is negligible relative to every
square-root-log exponential amplitude. Consequently the complete actual
strict-margin full-PNT majorant has normalized decay at every strict slower
rate.
-/

namespace PrimeNumberTheorem

open Filter Topology

/-- The auxiliary ratio `sqrt(log m) / sqrt(m)` tends to zero. -/
theorem tendsto_pntSqrtLog_div_sqrt_natCast_zero :
    Tendsto
      (fun m : ℕ => pntSqrtLog m / Real.sqrt (m : ℝ))
      atTop (nhds 0) := by
  have hsqrtTop : Tendsto (fun m : ℕ => Real.sqrt (m : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hbase :=
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hsqrtTop
  have hlogSqrt : Tendsto
      (fun m : ℕ => Real.log (m : ℝ) / Real.sqrt (m : ℝ))
      atTop (nhds 0) := by
    have htwo := hbase.const_mul 2
    convert htwo using 1
    · funext m
      by_cases hm : m = 0
      · subst m
        simp
      · have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
        simp only [Function.comp_apply, pow_one, one_mul, add_zero]
        rw [Real.log_sqrt hm0]
        ring
    · simp
  refine squeeze_zero' ?_ ?_ hlogSqrt
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · filter_upwards
      [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (1 : ℝ)),
        eventually_ge_atTop (1 : ℕ)] with m hlog hm
    have hlog' : 1 ≤ Real.log (m : ℝ) := by
      simpa only [Function.comp_apply] using hlog
    have hsqrtLog : pntSqrtLog m ≤ Real.log (m : ℝ) := by
      have hsquare := Real.sq_sqrt (le_trans zero_le_one hlog')
      have hsqrt0 : 0 ≤ pntSqrtLog m := Real.sqrt_nonneg _
      dsimp [pntSqrtLog] at hsquare ⊢
      nlinarith
    have hmpos : 0 < Real.sqrt (m : ℝ) := by
      exact Real.sqrt_pos.2 (by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hm))
    exact div_le_div_of_nonneg_right hsqrtLog hmpos.le

/-- The explicit depth-zero tail is negligible relative to every
square-root-log exponential amplitude. -/
theorem tendsto_cofinalPNTZeroDepthTail_div_sqrtLogAmplitude_zero
    (rate : ℝ) :
    Tendsto
      (fun m : ℕ =>
        (2 * cofinalPNTZeroDepthTailConstant * pntSqrtLog m / (m : ℝ)) /
          pntSqrtLogExponentialAmplitude rate m)
      atTop (nhds 0) := by
  have hpower :=
    tendsto_pntSqrtLog_div_sqrt_natCast_zero.const_mul
      (2 * cofinalPNTZeroDepthTailConstant)
  have hpowerToAmplitude :=
    tendsto_targetZeroPowerAmplitude_div_pntSqrtLogExponentialAmplitude_zero
      (show (1 / 2 : ℝ) < 1 by norm_num) rate
  have hproduct := hpower.mul hpowerToAmplitude
  have heq :
      (fun m : ℕ =>
        (2 * cofinalPNTZeroDepthTailConstant *
            (pntSqrtLog m / Real.sqrt (m : ℝ))) *
          (targetZeroPowerAmplitude (1 / 2) (m : ℝ) /
            pntSqrtLogExponentialAmplitude rate m)) =ᶠ[atTop]
        (fun m : ℕ =>
          (2 * cofinalPNTZeroDepthTailConstant * pntSqrtLog m / (m : ℝ)) /
            pntSqrtLogExponentialAmplitude rate m) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hmpos : 0 < (m : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hm)
    have hsqrtPos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hmpos
    have hsquare : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) :=
      Real.sq_sqrt hmpos.le
    unfold targetZeroPowerAmplitude
    rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by ring,
      Real.rpow_neg hmpos.le, ← Real.sqrt_eq_rpow]
    field_simp [hmpos.ne', hsqrtPos.ne', Real.exp_ne_zero]
    rw [hsquare]
  simpa only [mul_zero] using hproduct.congr' heq

/-- The complete rate-independent residual is negligible relative to every
square-root-log exponential amplitude. -/
theorem tendsto_actualStrictMarginRateIndependentResidual_div_amplitude_zero
    (rate : ℝ) :
    Tendsto
      (fun m : ℕ =>
        actualStrictMarginRateIndependentResidual m /
          pntSqrtLogExponentialAmplitude rate m)
      atTop (nhds 0) :=
  tendsto_actualStrictMarginRateIndependentResidual_div_amplitude_zero_of_tail
    rate (tendsto_cofinalPNTZeroDepthTail_div_sqrtLogAmplitude_zero rate)

/-- The full actual strict-margin grid majorant is negligible at every
strictly slower square-root-log exponential rate. -/
theorem tendsto_actualStrictMarginGridFullPNTErrorMajorant_strictRateGap
    (grid : ActualPintzCarlsonGoodHeightRateGrid)
    (C : ℝ) {theta b q slowerRate : ℝ}
    (htheta : 0 < theta) (hb : 0 < b) (hq : 0 < q)
    (hslower :
      slowerRate < classicalAdmissibleBalancedRate (theta * b) / q) :
    Tendsto
      (fun m : ℕ =>
        actualStrictMarginGridFullPNTErrorMajorant grid C theta b q m /
          pntSqrtLogExponentialAmplitude slowerRate m)
      atTop (nhds 0) :=
  tendsto_actualStrictMarginGridFullPNTErrorMajorant_div_amplitude_zero
    grid C htheta hb hq hslower
      (tendsto_actualStrictMarginRateIndependentResidual_div_amplitude_zero
        slowerRate)

/-- A normalized strict-rate upper bound excludes a cofinal lower witness at
the same square-root-log amplitude. -/
theorem no_cofinalPNTLowerWitness_at_sqrtLogAmplitude
    {upper : ℕ → ℝ} {rate : ℝ}
    (hupper : ∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ)| ≤ upper m)
    (hnormalized : Tendsto
      (fun m : ℕ => upper m / pntSqrtLogExponentialAmplitude rate m)
      atTop (nhds 0)) :
    ¬ ∃ witness : ℕ → ℕ,
      Tendsto witness atTop atTop ∧
      ∀ᶠ j : ℕ in atTop,
        pntSqrtLogExponentialAmplitude rate (witness j) ≤
          |relativeChebyshevPsi0Error (witness j : ℝ)| := by
  rintro ⟨witness, hwitness, hlower⟩
  apply
    (not_isNormalizedCofinalPNTLowerWitness_of_eventually_upper
      hupper witness
        (fun j : ℕ => pntSqrtLogExponentialAmplitude rate (witness j)))
  refine ⟨hwitness, Eventually.of_forall fun j =>
    pntSqrtLogExponentialAmplitude_pos rate (witness j), hlower, ?_⟩
  exact hnormalized.comp hwitness

end PrimeNumberTheorem
