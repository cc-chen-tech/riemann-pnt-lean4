import PrimeNumberTheorem.ZeroDensityLayerBudgetActualClassicalDyadicCarlsonThetaSharpRate

open Filter Real Complex
open scoped Topology BigOperators

namespace PrimeNumberTheorem

noncomputable def classicalDyadicCarlsonHalfSqrtLogMajorant
    (C rate : ℝ) (m : ℕ) : ℝ :=
  classicalDyadicCarlsonThetaSqrtLogMajorant
    (C * Real.exp (rate / 2)) rate (1 / 2) m

lemma eventually_carlsonDynamicGapLayeredCoarseLogPowerRatio_le_halfMajorant
    {C rate : ℝ} (hC : 0 < C) (hrate : 0 < rate) :
    ∀ᶠ m : ℕ in atTop,
      carlsonDynamicGapLayeredCoarseLogPowerRatio C
          (classicalAdmissibleDyadicCarlsonGapWidth rate)
          (dyadicCarlsonLayerSchedule
            (classicalAdmissibleDyadicCarlsonGapWidth rate)) m ≤
        classicalDyadicCarlsonHalfSqrtLogMajorant C rate m := by
  have hdeltaLe :=
    eventually_classicalAdmissibleDyadicCarlsonGapWidth_le_eighth hrate
  filter_upwards [eventually_ge_atTop (1 : ℕ), hdeltaLe,
      tendsto_pntSqrtLog_atTop.eventually
        (eventually_ge_atTop (1 : ℝ))] with
      m hm hdeltaUpper hsLarge
  let s : ℝ := pntSqrtLog m
  let delta : ℝ := classicalAdmissibleDyadicCarlsonGapWidth rate m
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hlogNonneg : 0 ≤ Real.log (m : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hm)
  have hsNonneg : 0 ≤ s := by
    dsimp [s, pntSqrtLog]
    positivity
  have hsOne : 1 ≤ s := hsLarge
  have hsSq : s ^ 2 = Real.log (m : ℝ) := by
    dsimp [s, pntSqrtLog]
    exact Real.sq_sqrt hlogNonneg
  have hdeltaPos : 0 < delta := by
    dsimp [delta]
    exact classicalAdmissibleDyadicCarlsonGapWidth_pos hrate m
  have hdeltaInv : delta⁻¹ = (1 + s) / rate := by
    dsimp [delta, classicalAdmissibleDyadicCarlsonGapWidth, s]
    field_simp
  have hlogDeltaInv :
      Real.log delta⁻¹ = Real.log (1 + s) - Real.log rate := by
    rw [hdeltaInv, Real.log_div (by linarith) (ne_of_gt hrate)]
  have hlogLog :
      Real.log (Real.log (m : ℝ)) ≤ 2 * Real.log (1 + s) := by
    have hlogPos : 0 < Real.log (m : ℝ) := by
      rw [← hsSq]
      nlinarith
    have hsqLe : Real.log (m : ℝ) ≤ (1 + s) ^ 2 := by
      rw [← hsSq]
      nlinarith
    calc
      Real.log (Real.log (m : ℝ)) ≤ Real.log ((1 + s) ^ 2) :=
        Real.log_le_log hlogPos hsqLe
      _ = 2 * Real.log (1 + s) := by
        rw [Real.log_pow]
        norm_num
  have hlayerCost :
      carlsonDynamicLayerCountLogCost
          (dyadicCarlsonLayerSchedule
            (classicalAdmissibleDyadicCarlsonGapWidth rate)) m ≤
        Real.log delta⁻¹ := by
    simpa [carlsonDynamicLayerCountLogCost,
      dyadicCarlsonLayerSchedule, delta] using
      carlsonDynamicMinimalLayerCountLogCost_le hdeltaPos hdeltaUpper
  have hden : 0 < 1 + s := by linarith
  have hidentity :
      (rate / (1 + s)) / 2 * s ^ 2 -
          (rate / 2 * s - rate / 2) =
        rate / (2 * (1 + s)) := by
    field_simp [ne_of_gt hden]
    ring
  have hcompensation :
      rate / 2 * s - rate / 2 ≤
        delta / 2 * Real.log (m : ℝ) := by
    rw [← hsSq]
    change rate / 2 * s - rate / 2 ≤
      (rate / (1 + s)) / 2 * s ^ 2
    have hnonneg : 0 ≤ rate / (2 * (1 + s)) := by positivity
    linarith
  unfold carlsonDynamicGapLayeredCoarseLogPowerRatio
    classicalDyadicCarlsonHalfSqrtLogMajorant
    classicalDyadicCarlsonThetaSqrtLogMajorant
  rw [Real.log_mul (ne_of_gt hC) (Real.exp_ne_zero _), Real.log_exp]
  apply Real.exp_le_exp.mpr
  dsimp [s] at hlogDeltaInv hlogLog hlayerCost hcompensation ⊢
  rw [hlogDeltaInv] at hlayerCost
  linarith

lemma classicalDyadicCarlsonHalfSqrtLogMajorant_eq
    {C rate : ℝ} (hC : 0 < C) (m : ℕ) :
    classicalDyadicCarlsonHalfSqrtLogMajorant C rate m =
      Real.exp (Real.log C - 3 * Real.log rate + rate / 2) *
        (1 + pntSqrtLog m) ^ 11 *
        Real.exp (-(rate / 2) * pntSqrtLog m) := by
  unfold classicalDyadicCarlsonHalfSqrtLogMajorant
  rw [classicalDyadicCarlsonThetaSqrtLogMajorant_eq]
  rw [Real.log_mul (ne_of_gt hC) (Real.exp_ne_zero _), Real.log_exp]
  congr 2 <;> ring

lemma tendsto_classicalDyadicCarlsonHalfSqrtLogMajorant_zero
    (C : ℝ) {rate : ℝ} (hrate : 0 < rate) :
    Tendsto (classicalDyadicCarlsonHalfSqrtLogMajorant C rate)
      atTop (nhds 0) := by
  unfold classicalDyadicCarlsonHalfSqrtLogMajorant
  exact tendsto_classicalDyadicCarlsonThetaSqrtLogMajorant_zero
    (C * Real.exp (rate / 2)) hrate (by norm_num)

lemma exists_classicalAdmissibleDyadicCarlsonHalfQuantitativeFixedAnchorMajorant
    {rate : ℝ} (hrate : 0 < rate) :
    ∃ C : ℝ, 0 < C ∧
      (∀ᶠ m : ℕ in atTop,
        actualDyadicCarlsonFixedAnchorMass (1 / 64)
            (classicalAdmissibleDyadicCarlsonGapWidth rate)
            (dyadicCarlsonLayerSchedule
              (classicalAdmissibleDyadicCarlsonGapWidth rate)) m ≤
          classicalDyadicCarlsonHalfSqrtLogMajorant C rate m) ∧
      Tendsto (classicalDyadicCarlsonHalfSqrtLogMajorant C rate)
        atTop (nhds 0) := by
  rcases
      exists_eventually_actualDyadicCarlsonMinimalFixedAnchorMass_le_layeredCoarse
        (alpha := 1 / 64)
        (show (0 : ℝ) < 1 / 64 by norm_num)
        (show (1 / 64 : ℝ) ≤ 1 / 16 by norm_num)
        (classicalAdmissibleDyadicCarlsonGapWidth_nonneg hrate)
        (Filter.Eventually.of_forall fun m =>
          classicalAdmissibleDyadicCarlsonGapWidth_pos hrate m)
        (eventually_classicalAdmissibleDyadicCarlsonGapWidth_le_eighth hrate)
        (isCarlsonMovingDyadicLogPowerGap_classicalAdmissible hrate) with
    ⟨C, hC, hcoarse⟩
  have hhalf :=
    eventually_carlsonDynamicGapLayeredCoarseLogPowerRatio_le_halfMajorant
      hC hrate
  refine ⟨C, hC, ?_, ?_⟩
  · filter_upwards [hcoarse, hhalf] with m hm hhalfM
    exact hm.trans hhalfM
  · exact tendsto_classicalDyadicCarlsonHalfSqrtLogMajorant_zero C hrate

lemma classicalAdmissibleHalfVerifiedPNTDecayRate_eq
    (b : ℝ) :
    classicalAdmissibleThetaVerifiedPNTDecayRate b (1 / 2) =
      classicalAdmissibleBalancedRate b / 4 := by
  unfold classicalAdmissibleThetaVerifiedPNTDecayRate
  ring

lemma classicalAdmissibleHalfVerifiedPNTDecayRate_pos
    {b : ℝ} (hb : 0 < b) :
    0 < classicalAdmissibleThetaVerifiedPNTDecayRate b (1 / 2) := by
  rw [classicalAdmissibleHalfVerifiedPNTDecayRate_eq]
  exact div_pos (classicalAdmissibleBalancedRate_pos hb) (by norm_num)

lemma classicalAdmissibleVerifiedPNTDecayRate_lt_halfRate
    {b : ℝ} (hb : 0 < b) :
    classicalAdmissibleVerifiedPNTDecayRate b <
      classicalAdmissibleThetaVerifiedPNTDecayRate b (1 / 2) := by
  unfold classicalAdmissibleVerifiedPNTDecayRate
  rw [classicalAdmissibleHalfVerifiedPNTDecayRate_eq]
  have hrate := classicalAdmissibleBalancedRate_pos hb
  nlinarith

end PrimeNumberTheorem
