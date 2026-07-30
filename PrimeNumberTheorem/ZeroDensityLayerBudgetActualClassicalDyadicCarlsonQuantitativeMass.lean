import PrimeNumberTheorem.ZeroDensityLayerBudgetActualClassicalDyadicCarlsonFullPNTTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonDynamicGapDomination
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDynamicCarlsonAutomaticCount

open Filter Real
open scoped Topology BigOperators

namespace PrimeNumberTheorem

lemma exists_eventually_actualDyadicCarlsonMinimalFixedAnchorMass_le_layeredCoarse
    {alpha : ℝ} {delta : ℕ → ℝ}
    (halpha : 0 < alpha) (halpha_le : alpha ≤ 1 / 16)
    (hdelta_nonneg : ∀ m, 0 ≤ delta m)
    (hdelta_pos : ∀ᶠ m : ℕ in atTop, 0 < delta m)
    (hdelta_le : ∀ᶠ m : ℕ in atTop, delta m ≤ 1 / 8)
    (hgap : IsCarlsonMovingDyadicLogPowerGap delta) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ m : ℕ in atTop,
        actualDyadicCarlsonFixedAnchorMass alpha delta
            (dyadicCarlsonLayerSchedule delta) m ≤
          carlsonDynamicGapLayeredCoarseLogPowerRatio C delta
            (dyadicCarlsonLayerSchedule delta) m := by
  have hscale := eventually_dyadicCarlsonLayerSchedule_scale hdelta_pos hdelta_le
  have hactive : ∀ᶠ m : ℕ in atTop,
      ∀ i : Fin (dyadicCarlsonLayerSchedule delta m),
        dyadicCarlsonGap delta m i ≤ 1 / 8 ∧
          128 * alpha * dyadicCarlsonGap delta m i ≤ 1 := by
    filter_upwards [hscale] with m hm
    exact dyadicCarlsonGap_active_of_outer_le halpha.le halpha_le
      (hdelta_nonneg m) hm.2
  have hgapBounds : ∀ᶠ m : ℕ in atTop,
      ∀ i : Fin (dyadicCarlsonLayerSchedule delta m),
        0 < dyadicCarlsonGap delta m i ∧
          dyadicCarlsonGap delta m i < 1 / 4 := by
    filter_upwards [hdelta_pos, hactive] with m hpos hact
    intro i
    exact ⟨hpos.trans_le (delta_le_dyadicCarlsonGap (hdelta_nonneg m)),
      (hact i).1.trans_lt (by norm_num)⟩
  obtain ⟨A, C₁, C₂, hA, hC₁, hC₂, hcertificate⟩ :=
    exists_actualDynamicCarlsonGapFamilyCountCertificate hgapBounds
  have hheight := actualDynamicDyadicCarlsonMinimalHeightConditions
    (C₁ := C₁) (C₂ := C₂) halpha halpha_le hdelta_nonneg
      hdelta_pos hdelta_le hgap
  have hcount := hcertificate hheight
  have hgapEighth : ∀ᶠ m : ℕ in atTop,
      ∀ i : Fin (dyadicCarlsonLayerSchedule delta m),
        0 < dyadicCarlsonGap delta m i ∧
          dyadicCarlsonGap delta m i ≤ 1 / 8 := by
    filter_upwards [hgapBounds, hactive] with m hbounds hact
    intro i
    exact ⟨(hbounds i).1, (hact i).1⟩
  have hown := eventually_actualDynamicCarlsonGapLayerMass_le_ownRatio
    hA halpha hgapEighth hcount
  let C := actualMovingCarlsonBalancedPositiveConstant A alpha
  refine ⟨C, actualMovingCarlsonBalancedPositiveConstant_pos A alpha, ?_⟩
  filter_upwards [hown, hactive, hdelta_pos, eventually_ge_atTop (1 : ℕ)] with
      m hownM hactiveM hdeltaM hm
  calc
    actualDyadicCarlsonFixedAnchorMass alpha delta
          (dyadicCarlsonLayerSchedule delta) m ≤
        ∑ rho ∈ actualDynamicCarlsonGapStripUnion alpha
            (dyadicCarlsonLayerSchedule delta) (dyadicCarlsonGap delta) m,
          ‖pntRelativeZeroContribution (m : ℝ) rho‖ :=
      actualDyadicCarlsonFixedAnchorMass_le_union alpha delta
        (dyadicCarlsonLayerSchedule delta) m
    _ = actualDynamicCarlsonGapFamilyMass alpha
          (dyadicCarlsonLayerSchedule delta) (dyadicCarlsonGap delta) m :=
      actualDynamicCarlsonGapStripUnion_mass_eq_familyMass
        (dyadicCarlsonGap_familySeparated hdelta_nonneg)
    _ ≤ carlsonDynamicGapLayeredCoarseLogPowerRatio C delta
          (dyadicCarlsonLayerSchedule delta) m := by
      unfold actualDynamicCarlsonGapFamilyMass
      apply carlsonDynamicFiniteLayerMass_le_layeredCoarseLogPowerRatio
      intro i
      refine (hownM i).trans ?_
      apply carlsonMovingBalancedLogPowerRatio_le_coarse_of_gap_le
      · exact hm
      · exact hdeltaM
      · simpa [actualDynamicCarlsonGapSchedule] using
          (delta_le_dyadicCarlsonGap (delta := delta) (m := m)
            (j := (i : ℕ)) (hdelta_nonneg m))
      · exact (hactiveM i).1.trans (by norm_num)
      · exact halpha.le
      · simpa [actualDynamicCarlsonGapSchedule] using (hactiveM i).2

end PrimeNumberTheorem

namespace PrimeNumberTheorem

noncomputable def classicalDyadicCarlsonSqrtLogMajorant
    (C rate : ℝ) (m : ℕ) : ℝ :=
  Real.exp
    (Real.log C - 3 * Real.log rate +
      11 * Real.log (1 + pntSqrtLog m) -
      rate / 4 * pntSqrtLog m)

lemma eventually_carlsonDynamicGapLayeredCoarseLogPowerRatio_le_classicalSqrtLogMajorant
    {C rate : ℝ} (hrate : 0 < rate) :
    ∀ᶠ m : ℕ in atTop,
      carlsonDynamicGapLayeredCoarseLogPowerRatio C
          (classicalAdmissibleDyadicCarlsonGapWidth rate)
          (dyadicCarlsonLayerSchedule
            (classicalAdmissibleDyadicCarlsonGapWidth rate)) m ≤
        classicalDyadicCarlsonSqrtLogMajorant C rate m := by
  filter_upwards [eventually_ge_atTop (3 : ℕ),
    tendsto_pntSqrtLog_atTop.eventually_ge_atTop (1 : ℝ),
    eventually_classicalAdmissibleDyadicCarlsonGapWidth_le_eighth hrate] with
      m hm hsone hdeltaLe
  let s := pntSqrtLog m
  let delta := classicalAdmissibleDyadicCarlsonGapWidth rate
  have hmR : (1 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 3) hm)
  have hlogpos : 0 < Real.log (m : ℝ) := Real.log_pos hmR
  have hsnonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hspos : 0 < s := lt_of_lt_of_le (by norm_num) hsone
  have hdenpos : 0 < 1 + s := by linarith
  have hsquare : s ^ 2 = Real.log (m : ℝ) := by
    simpa [s, pntSqrtLog] using Real.sq_sqrt hlogpos.le
  have hdeltaPos : 0 < delta m :=
    classicalAdmissibleDyadicCarlsonGapWidth_pos hrate m
  have hcost := carlsonDynamicMinimalLayerCountLogCost_le hdeltaPos hdeltaLe
  have hcost' :
      carlsonDynamicLayerCountLogCost (dyadicCarlsonLayerSchedule delta) m ≤
        Real.log (delta m)⁻¹ := by
    simpa [carlsonDynamicLayerCountLogCost, dyadicCarlsonLayerSchedule] using hcost
  have hdeltaInv : (delta m)⁻¹ = (1 + s) / rate := by
    dsimp [delta, classicalAdmissibleDyadicCarlsonGapWidth]
    simp only [s]
    field_simp [hrate.ne', hdenpos.ne']
  have hlogDeltaInv : Real.log (delta m)⁻¹ =
      Real.log (1 + s) - Real.log rate := by
    rw [hdeltaInv, Real.log_div hdenpos.ne' hrate.ne']
  have hsqle : Real.log (m : ℝ) ≤ (1 + s) ^ 2 := by
    rw [← hsquare]
    nlinarith
  have hloglog : Real.log (Real.log (m : ℝ)) ≤
      2 * Real.log (1 + s) := by
    have hmono := Real.log_le_log hlogpos hsqle
    rw [Real.log_pow] at hmono
    norm_num at hmono ⊢
    exact hmono
  have hfrac : s / 2 ≤ s ^ 2 / (1 + s) := by
    apply (le_div_iff₀ hdenpos).2
    nlinarith
  have hnegative : rate / 4 * s ≤
      delta m / 2 * Real.log (m : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hfrac (by positivity : 0 ≤ rate / 2)
    calc
      rate / 4 * s = rate / 2 * (s / 2) := by ring
      _ ≤ rate / 2 * (s ^ 2 / (1 + s)) := hmul
      _ = delta m / 2 * Real.log (m : ℝ) := by
        rw [← hsquare]
        dsimp [delta, classicalAdmissibleDyadicCarlsonGapWidth]
        simp only [s]
        field_simp [hdenpos.ne']
  unfold carlsonDynamicGapLayeredCoarseLogPowerRatio
    classicalDyadicCarlsonSqrtLogMajorant
  apply Real.exp_le_exp.mpr
  calc
    Real.log C + 2 * Real.log (delta m)⁻¹ +
          4 * Real.log (Real.log (m : ℝ)) +
          carlsonDynamicLayerCountLogCost
            (dyadicCarlsonLayerSchedule delta) m -
          delta m / 2 * Real.log (m : ℝ) ≤
        Real.log C + 3 * Real.log (delta m)⁻¹ +
          4 * Real.log (Real.log (m : ℝ)) -
          delta m / 2 * Real.log (m : ℝ) := by
      linarith [hcost']
    _ ≤ Real.log C - 3 * Real.log rate +
          11 * Real.log (1 + s) - rate / 4 * s := by
      rw [hlogDeltaInv]
      linarith

end PrimeNumberTheorem

namespace PrimeNumberTheorem

lemma classicalDyadicCarlsonSqrtLogMajorant_eq
    (C rate : ℝ) (m : ℕ) :
    classicalDyadicCarlsonSqrtLogMajorant C rate m =
      Real.exp (Real.log C - 3 * Real.log rate) *
        (1 + pntSqrtLog m) ^ 11 *
        Real.exp (-(rate / 4) * pntSqrtLog m) := by
  unfold classicalDyadicCarlsonSqrtLogMajorant
  rw [show Real.log C - 3 * Real.log rate +
        11 * Real.log (1 + pntSqrtLog m) -
        rate / 4 * pntSqrtLog m =
      (Real.log C - 3 * Real.log rate) +
        11 * Real.log (1 + pntSqrtLog m) +
        (-(rate / 4) * pntSqrtLog m) by ring]
  rw [Real.exp_add, Real.exp_add]
  congr 2
  have hpos : 0 < 1 + pntSqrtLog m := by
    have hs : 0 ≤ pntSqrtLog m := Real.sqrt_nonneg _
    linarith
  calc
    Real.exp (11 * Real.log (1 + pntSqrtLog m)) =
        Real.exp (Real.log (1 + pntSqrtLog m) * (11 : ℝ)) := by ring
    _ = (1 + pntSqrtLog m) ^ (11 : ℝ) :=
      (Real.rpow_def_of_pos hpos 11).symm
    _ = (1 + pntSqrtLog m) ^ 11 := Real.rpow_natCast _ _

lemma tendsto_classicalDyadicCarlsonSqrtLogMajorant_zero
    (C : ℝ) {rate : ℝ} (hrate : 0 < rate) :
    Tendsto (classicalDyadicCarlsonSqrtLogMajorant C rate) atTop (𝓝 0) := by
  have hcore :=
    tendsto_pntSqrtLog_pow_mul_exp_neg_mul_atTop_nhds_zero
      (rate / 4) (by positivity) 11
  let K := Real.exp (Real.log C - 3 * Real.log rate) * (2 : ℝ) ^ 11
  have hupper : ∀ᶠ m : ℕ in atTop,
      classicalDyadicCarlsonSqrtLogMajorant C rate m ≤
        K * (pntSqrtLog m ^ 11 *
          Real.exp (-(rate / 4) * pntSqrtLog m)) := by
    filter_upwards [tendsto_pntSqrtLog_atTop.eventually_ge_atTop (1 : ℝ)] with m hs
    have hsnonneg : 0 ≤ pntSqrtLog m := Real.sqrt_nonneg _
    have hpow : (1 + pntSqrtLog m) ^ 11 ≤
        (2 : ℝ) ^ 11 * pntSqrtLog m ^ 11 := by
      calc
        (1 + pntSqrtLog m) ^ 11 ≤ (2 * pntSqrtLog m) ^ 11 := by
          gcongr
          linarith
        _ = (2 : ℝ) ^ 11 * pntSqrtLog m ^ 11 := by rw [mul_pow]
    rw [classicalDyadicCarlsonSqrtLogMajorant_eq]
    dsimp [K]
    have hconst : 0 ≤ Real.exp (Real.log C - 3 * Real.log rate) :=
      Real.exp_nonneg _
    have hexp : 0 ≤ Real.exp (-(rate / 4) * pntSqrtLog m) :=
      Real.exp_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hpow hconst]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun m => (Real.exp_nonneg _)
  · exact hupper
  · simpa [K] using (tendsto_const_nhds.mul hcore)

end PrimeNumberTheorem

namespace PrimeNumberTheorem

lemma exists_classicalAdmissibleDyadicCarlsonQuantitativeFixedAnchorMajorant
    {rate : ℝ} (hrate : 0 < rate) :
    ∃ C : ℝ, 0 < C ∧
      (∀ᶠ m : ℕ in atTop,
        actualDyadicCarlsonFixedAnchorMass (1 / 64)
            (classicalAdmissibleDyadicCarlsonGapWidth rate)
            (dyadicCarlsonLayerSchedule
              (classicalAdmissibleDyadicCarlsonGapWidth rate)) m ≤
          classicalDyadicCarlsonSqrtLogMajorant C rate m) ∧
      Tendsto (classicalDyadicCarlsonSqrtLogMajorant C rate)
        atTop (𝓝 0) := by
  let delta := classicalAdmissibleDyadicCarlsonGapWidth rate
  have hdeltaNonneg : ∀ m, 0 ≤ delta m :=
    classicalAdmissibleDyadicCarlsonGapWidth_nonneg hrate
  have hdeltaPos : ∀ᶠ m : ℕ in atTop, 0 < delta m :=
    Filter.Eventually.of_forall fun m =>
      classicalAdmissibleDyadicCarlsonGapWidth_pos hrate m
  have hdeltaLe : ∀ᶠ m : ℕ in atTop, delta m ≤ 1 / 8 :=
    eventually_classicalAdmissibleDyadicCarlsonGapWidth_le_eighth hrate
  have hgap : IsCarlsonMovingDyadicLogPowerGap delta :=
    isCarlsonMovingDyadicLogPowerGap_classicalAdmissible hrate
  obtain ⟨C, hC, hcoarse⟩ :=
    exists_eventually_actualDyadicCarlsonMinimalFixedAnchorMass_le_layeredCoarse
      (by norm_num : (0 : ℝ) < 1 / 64)
      (by norm_num : (1 / 64 : ℝ) ≤ 1 / 16)
      hdeltaNonneg hdeltaPos hdeltaLe hgap
  refine ⟨C, hC, ?_, tendsto_classicalDyadicCarlsonSqrtLogMajorant_zero C hrate⟩
  filter_upwards [hcoarse,
    eventually_carlsonDynamicGapLayeredCoarseLogPowerRatio_le_classicalSqrtLogMajorant
      (C := C) hrate] with m hmass hmajorant
  exact hmass.trans hmajorant

/-- The canonical classical selected height has explicit square-root-logarithmic
majorants for both density-controlled right-hand zero layers. -/
theorem exists_selectedClassicalAdmissibleDyadicCarlsonQuantitativeMassMajorant :
    ∃ b rate C : ℝ,
      0 < b ∧ 0 < rate ∧ 0 < C ∧
        IsCarlsonMovingDyadicLogPowerGap
          (classicalAdmissibleDyadicCarlsonGapWidth rate) ∧
        Tendsto (classicalDyadicCarlsonSqrtLogMajorant C rate)
          atTop (𝓝 0) ∧
        ∀ selection : UniformNaturalPointGoodHeightSelection,
          IsSelectedHeightDynamicZeroFree
              (selectedClassicalAdmissibleGoodHeight b selection)
              (classicalAdmissibleDyadicCarlsonGapWidth rate) ∧
            ∀ᶠ m : ℕ in atTop,
              actualSelectedHeightMovingCarlsonMiddleMass
                    (selectedClassicalAdmissibleGoodHeight b selection)
                    (classicalAdmissibleDyadicCarlsonGapWidth rate) m ≤
                  actualSelectedHeightSevenEighthsLowMass
                    (selectedClassicalAdmissibleGoodHeight b selection) m +
                    classicalDyadicCarlsonSqrtLogMajorant C rate m ∧
                actualSelectedHeightMovingCarlsonStripMass
                    (selectedClassicalAdmissibleGoodHeight b selection)
                    (classicalAdmissibleDyadicCarlsonGapWidth rate) m ≤
                  classicalDyadicCarlsonSqrtLogMajorant C rate m := by
  obtain ⟨b, rate, hb, hrate, hgap, hzeroFree⟩ :=
    exists_selectedClassicalAdmissibleDyadicCarlsonZeroFreeGap
  obtain ⟨C, hC, hfixed, hmajorantZero⟩ :=
    exists_classicalAdmissibleDyadicCarlsonQuantitativeFixedAnchorMajorant hrate
  refine ⟨b, rate, C, hb, hrate, hC, hgap, hmajorantZero, ?_⟩
  intro selection
  refine ⟨hzeroFree selection, ?_⟩
  have hheightReal :=
    eventually_selectedClassicalAdmissibleGoodHeight_le_polynomialHeight_real
      hb (by norm_num : (0 : ℝ) < 1 / 64) selection
  have hheight := tendsto_natCast_atTop_atTop.eventually hheightReal
  have hdeltaPos : ∀ᶠ m : ℕ in atTop,
      0 < classicalAdmissibleDyadicCarlsonGapWidth rate m :=
    Filter.Eventually.of_forall fun m =>
      classicalAdmissibleDyadicCarlsonGapWidth_pos hrate m
  have hdeltaSixteenth :=
    eventually_classicalAdmissibleDyadicCarlsonGapWidth_le_sixteenth
      (rate := rate)
  filter_upwards [hheight, hdeltaPos, hdeltaSixteenth, hfixed] with
      m hH hdelta hdeltaLe hfixedM
  constructor
  · exact (actualSelectedHeightMovingCarlsonMiddleMass_le_low_add_dyadicFixedAnchor
      hH hdelta).trans (add_le_add_right hfixedM _)
  · exact (actualSelectedHeightMovingCarlsonStripMass_le_dyadicFixedAnchor
      hH hdelta hdeltaLe).trans hfixedM

end PrimeNumberTheorem
