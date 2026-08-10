import PrimeNumberTheorem.ZeroDensityLayerBudgetActualClassicalDyadicCarlsonBalancedClosedFormFullPNT

open Filter Real Complex
open scoped Topology BigOperators

namespace PrimeNumberTheorem

noncomputable def classicalDyadicCarlsonThetaSqrtLogMajorant
    (C rate theta : ℝ) (m : ℕ) : ℝ :=
  Real.exp
    (Real.log C - 3 * Real.log rate +
      11 * Real.log (1 + pntSqrtLog m) -
      theta * rate * pntSqrtLog m)

lemma eventually_carlsonDynamicGapLayeredCoarseLogPowerRatio_le_thetaMajorant
    {C rate theta : ℝ}
    (hrate : 0 < rate) (htheta : 0 < theta) (hthetaHalf : theta < 1 / 2) :
    ∀ᶠ m : ℕ in atTop,
      carlsonDynamicGapLayeredCoarseLogPowerRatio C
          (classicalAdmissibleDyadicCarlsonGapWidth rate)
          (dyadicCarlsonLayerSchedule
            (classicalAdmissibleDyadicCarlsonGapWidth rate)) m ≤
        classicalDyadicCarlsonThetaSqrtLogMajorant C rate theta m := by
  have hdenTheta : 0 < 1 - 2 * theta := by linarith
  have hdeltaLe :=
    eventually_classicalAdmissibleDyadicCarlsonGapWidth_le_eighth hrate
  filter_upwards [eventually_ge_atTop (1 : ℕ), hdeltaLe,
      tendsto_pntSqrtLog_atTop.eventually
        (eventually_ge_atTop
          (max 1 (2 * theta / (1 - 2 * theta))))] with
      m hm hdeltaUpper hsLarge
  let s : ℝ := pntSqrtLog m
  let delta : ℝ := classicalAdmissibleDyadicCarlsonGapWidth rate m
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hlogNonneg : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
  have hsNonneg : 0 ≤ s := by
    dsimp [s, pntSqrtLog]
    positivity
  have hsOne : 1 ≤ s := (le_max_left _ _).trans hsLarge
  have hsThreshold : 2 * theta / (1 - 2 * theta) ≤ s :=
    (le_max_right _ _).trans hsLarge
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
  have hcore : 2 * theta * (1 + s) ≤ s := by
    have hbase := (div_le_iff₀ hdenTheta).mp hsThreshold
    nlinarith
  have hscaled :
      theta * rate * s * (1 + s) ≤ rate / 2 * s ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hcore
      (mul_nonneg hrate.le hsNonneg)
    nlinarith
  have hnegative :
      theta * rate * s ≤ delta / 2 * Real.log (m : ℝ) := by
    rw [← hsSq]
    change theta * rate * s ≤ (rate / (1 + s)) / 2 * s ^ 2
    calc
      theta * rate * s ≤ (rate / 2 * s ^ 2) / (1 + s) :=
        (le_div_iff₀ (by linarith : 0 < 1 + s)).2 hscaled
      _ = (rate / (1 + s)) / 2 * s ^ 2 := by
        field_simp
  unfold carlsonDynamicGapLayeredCoarseLogPowerRatio
    classicalDyadicCarlsonThetaSqrtLogMajorant
  apply Real.exp_le_exp.mpr
  dsimp [s] at hlogDeltaInv hlogLog hlayerCost hnegative ⊢
  rw [hlogDeltaInv] at hlayerCost
  linarith

lemma classicalDyadicCarlsonThetaSqrtLogMajorant_eq
    (C rate theta : ℝ) (m : ℕ) :
    classicalDyadicCarlsonThetaSqrtLogMajorant C rate theta m =
      Real.exp (Real.log C - 3 * Real.log rate) *
        (1 + pntSqrtLog m) ^ 11 *
        Real.exp (-(theta * rate) * pntSqrtLog m) := by
  unfold classicalDyadicCarlsonThetaSqrtLogMajorant
  rw [show theta * rate * pntSqrtLog m =
      (theta * rate) * pntSqrtLog m by ring]
  rw [show Real.log C - 3 * Real.log rate +
      11 * Real.log (1 + pntSqrtLog m) -
      (theta * rate) * pntSqrtLog m =
    (Real.log C - 3 * Real.log rate) +
      11 * Real.log (1 + pntSqrtLog m) +
      (-(theta * rate) * pntSqrtLog m) by ring]
  rw [Real.exp_add, Real.exp_add]
  congr 1
  rw [← Real.rpow_natCast]
  rw [Real.rpow_def_of_pos (by
    have hs : 0 ≤ pntSqrtLog m := by
      unfold pntSqrtLog
      positivity
    linarith)]
  congr 1
  norm_num
  ring

lemma tendsto_classicalDyadicCarlsonThetaSqrtLogMajorant_zero
    (C : ℝ) {rate theta : ℝ}
    (hrate : 0 < rate) (htheta : 0 < theta) :
    Tendsto (classicalDyadicCarlsonThetaSqrtLogMajorant C rate theta)
      atTop (nhds 0) := by
  have hthetaRate : 0 < theta * rate := mul_pos htheta hrate
  have hbase :=
    tendsto_pntSqrtLog_pow_mul_exp_neg_mul_atTop_nhds_zero
      (theta * rate) hthetaRate 11
  have hratio : Tendsto
      (fun m : ℕ => ((1 + pntSqrtLog m) / pntSqrtLog m) ^ 11)
      atTop (nhds 1) := by
    have hsInv : Tendsto (fun m : ℕ => (pntSqrtLog m)⁻¹)
        atTop (nhds 0) := tendsto_inv_atTop_zero.comp tendsto_pntSqrtLog_atTop
    have hquot : Tendsto
        (fun m : ℕ => (1 + pntSqrtLog m) / pntSqrtLog m)
        atTop (nhds 1) := by
      have hsum : Tendsto
          (fun m : ℕ => 1 + (pntSqrtLog m)⁻¹)
          atTop (nhds 1) := by
        simpa using tendsto_const_nhds.add hsInv
      apply hsum.congr'
      filter_upwards
          [tendsto_pntSqrtLog_atTop.eventually
            (eventually_gt_atTop (0 : ℝ))] with m hs
      field_simp
      ring
    simpa using hquot.pow 11
  have hproduct := hratio.mul hbase
  have hproduct' : Tendsto
      (fun m : ℕ => (1 + pntSqrtLog m) ^ 11 *
        Real.exp (-(theta * rate) * pntSqrtLog m))
      atTop (nhds 0) := by
    have hproductZero : Tendsto
        (fun m : ℕ => ((1 + pntSqrtLog m) / pntSqrtLog m) ^ 11 *
          (pntSqrtLog m ^ 11 *
            Real.exp (-(theta * rate) * pntSqrtLog m)))
        atTop (nhds 0) := by
      simpa using hproduct
    apply hproductZero.congr'
    filter_upwards
        [tendsto_pntSqrtLog_atTop.eventually
          (eventually_gt_atTop (0 : ℝ))] with m hs
    field_simp
  have hscaled' : Tendsto
      (fun m : ℕ =>
        Real.exp (Real.log C - 3 * Real.log rate) *
          ((1 + pntSqrtLog m) ^ 11 *
            Real.exp (-(theta * rate) * pntSqrtLog m)))
      atTop (nhds 0) := by
    simpa using hproduct'.const_mul
      (Real.exp (Real.log C - 3 * Real.log rate))
  apply hscaled'.congr'
  filter_upwards with m
  simpa [mul_assoc] using
    (classicalDyadicCarlsonThetaSqrtLogMajorant_eq C rate theta m).symm

lemma exists_classicalAdmissibleDyadicCarlsonThetaQuantitativeFixedAnchorMajorant
    {rate theta : ℝ}
    (hrate : 0 < rate) (htheta : 0 < theta) (hthetaHalf : theta < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧
      (∀ᶠ m : ℕ in atTop,
        actualDyadicCarlsonFixedAnchorMass (1 / 64)
            (classicalAdmissibleDyadicCarlsonGapWidth rate)
            (dyadicCarlsonLayerSchedule
              (classicalAdmissibleDyadicCarlsonGapWidth rate)) m ≤
          classicalDyadicCarlsonThetaSqrtLogMajorant C rate theta m) ∧
      Tendsto
        (classicalDyadicCarlsonThetaSqrtLogMajorant C rate theta)
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
  have hthetaBound :=
    eventually_carlsonDynamicGapLayeredCoarseLogPowerRatio_le_thetaMajorant
      (C := C) hrate htheta hthetaHalf
  refine ⟨C, hC, ?_, ?_⟩
  · filter_upwards [hcoarse, hthetaBound] with m hm hthetaM
    exact hm.trans hthetaM
  · exact tendsto_classicalDyadicCarlsonThetaSqrtLogMajorant_zero
      C hrate htheta

noncomputable def classicalAdmissibleThetaVerifiedPNTDecayRate
    (b theta : ℝ) : ℝ :=
  theta * (classicalAdmissibleBalancedRate b / 2)

lemma classicalAdmissibleThetaVerifiedPNTDecayRate_pos
    {b theta : ℝ} (hb : 0 < b) (htheta : 0 < theta) :
    0 < classicalAdmissibleThetaVerifiedPNTDecayRate b theta := by
  unfold classicalAdmissibleThetaVerifiedPNTDecayRate
  exact mul_pos htheta
    (div_pos (classicalAdmissibleBalancedRate_pos hb) (by norm_num))

lemma classicalAdmissibleVerifiedPNTDecayRate_lt_thetaRate
    {b theta : ℝ} (hb : 0 < b) (hthetaQuarter : 1 / 4 < theta) :
    classicalAdmissibleVerifiedPNTDecayRate b <
      classicalAdmissibleThetaVerifiedPNTDecayRate b theta := by
  unfold classicalAdmissibleVerifiedPNTDecayRate
    classicalAdmissibleThetaVerifiedPNTDecayRate
  have hrate := classicalAdmissibleBalancedRate_pos hb
  nlinarith

lemma classicalAdmissibleThetaVerifiedPNTDecayRate_lt_quarterHeightRate
    {b theta : ℝ} (hb : 0 < b) (hthetaHalf : theta < 1 / 2) :
    classicalAdmissibleThetaVerifiedPNTDecayRate b theta <
      classicalAdmissibleBalancedRate b / 4 := by
  unfold classicalAdmissibleThetaVerifiedPNTDecayRate
  have hrate := classicalAdmissibleBalancedRate_pos hb
  nlinarith

end PrimeNumberTheorem
