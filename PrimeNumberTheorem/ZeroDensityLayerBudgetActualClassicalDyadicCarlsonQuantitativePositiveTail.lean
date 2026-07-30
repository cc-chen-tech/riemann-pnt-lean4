import PrimeNumberTheorem.ZeroDensityLayerBudgetActualClassicalDyadicCarlsonQuantitativeMiddleMass

open Filter Real Complex
open scoped Topology BigOperators

namespace PrimeNumberTheorem

lemma exists_eventually_dynamicPositiveOutsideClusterPNTLayerNorm_div_target_le_actualHybridMajorant_selectedHeight
    {n : ℕ} {S : Finset ℂ} {H : ℝ → ℝ}
    {beta tau alpha kappa : ℝ}
    (input : (x : ℝ) → PositiveZeroOutsideClusterBucketInput (H x) S n)
    (i : Fin n)
    (hHle : ∀ᶠ x : ℝ in atTop,
      H x ≤ carlsonPolynomialHeight alpha x)
    (hHtop : Tendsto H atTop atTop)
    (hkappa : 0 < kappa)
    (hnorm : ∀ x, ∀ rho ∈ (input x).layer i, kappa ≤ ‖rho‖)
    (hre : ∀ x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau)
    (halpha : 0 < alpha) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ x : ℝ in atTop,
        |dynamicPositiveOutsideClusterPNTLayerNorm H S input i x| /
            targetZeroPowerAmplitude beta x ≤
          actualHybridLowNormalizedLogPowerMajorant
            C kappa beta tau alpha x := by
  rcases
      exists_globalCoefficient_dynamicPositiveOutsideClusterPNTLayerNorm_le_actualHybridMajorant
        input i tau kappa hkappa hnorm hre with
    ⟨C, hC, hpointwise⟩
  have hlog :=
    eventually_one_add_log_polynomialHeight_add_six_le_log_four halpha
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ),
      hHtop.eventually (eventually_ge_atTop (4 : ℝ)), hHle, hlog] with
      x hx hHfour hHupper hlogBound
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hamplitude : 0 < targetZeroPowerAmplitude beta x :=
    Real.rpow_pos_of_pos hxpos _
  have hphysical := hpointwise x hx hHfour
  have hselectedToPower :
      actualHybridGlobalLowLayerMajorant C (H x) kappa tau x ≤
        actualHybridGlobalLowLayerMajorant C
          (carlsonPolynomialHeight alpha x) kappa tau x :=
    actualHybridGlobalLowLayerMajorant_mono_height
      hC hkappa (zero_le_one.trans hx) hHfour hHupper
  have hnormalized :
      |dynamicPositiveOutsideClusterPNTLayerNorm H S input i x| /
          targetZeroPowerAmplitude beta x ≤
        actualHybridGlobalLowLayerMajorant C
            (carlsonPolynomialHeight alpha x) kappa tau x /
          targetZeroPowerAmplitude beta x :=
    (div_le_div_iff_of_pos_right hamplitude).2
      (hphysical.trans hselectedToPower)
  have hcoefficient :
      0 ≤ C * kappa⁻¹ * x ^ (tau - beta + alpha) := by positivity
  calc
    |dynamicPositiveOutsideClusterPNTLayerNorm H S input i x| /
        targetZeroPowerAmplitude beta x ≤
      actualHybridGlobalLowLayerMajorant C
          (carlsonPolynomialHeight alpha x) kappa tau x /
        targetZeroPowerAmplitude beta x := hnormalized
    _ = C * kappa⁻¹ * x ^ (tau - beta + alpha) *
        (1 + Real.log (x ^ alpha + 6)) :=
      actualHybridGlobalLowLayerMajorant_div_target_eq hxpos
    _ ≤ C * kappa⁻¹ * x ^ (tau - beta + alpha) *
        ((alpha + 2) * Real.log x ^ 4) :=
      mul_le_mul_of_nonneg_left hlogBound hcoefficient
    _ = actualHybridLowNormalizedLogPowerMajorant
        C kappa beta tau alpha x := by
      unfold actualHybridLowNormalizedLogPowerMajorant
      ring

noncomputable def classicalCriticalHalfMajorant
    (C kappa : ℝ) (m : ℕ) : ℝ :=
  actualHybridLowNormalizedLogPowerMajorant
    C kappa 1 (1 / 2) (1 / 64) (m : ℝ)

lemma classicalCriticalHalfMajorant_eq
    (C kappa : ℝ) (m : ℕ) :
    classicalCriticalHalfMajorant C kappa m =
      (C * kappa⁻¹ * ((1 / 64 : ℝ) + 2)) *
        (m : ℝ) ^ (-(31 / 64 : ℝ)) * Real.log (m : ℝ) ^ 4 := by
  unfold classicalCriticalHalfMajorant
    actualHybridLowNormalizedLogPowerMajorant
  congr 2
  norm_num

lemma tendsto_classicalCriticalHalfMajorant_zero
    {C kappa : ℝ} (hC : 0 ≤ C) (hkappa : 0 < kappa) :
    Tendsto (classicalCriticalHalfMajorant C kappa) atTop (nhds 0) := by
  have h := tendsto_actualHybridLowNormalizedLogPowerMajorant_zero
    (C := C) (kappa := kappa) (beta := 1) (tau := 1 / 2)
    (alpha := 1 / 64) (epsilon := 1 / 128)
    hC hkappa (by norm_num) (by norm_num) (by norm_num)
  change Tendsto
    (fun m : ℕ => actualHybridLowNormalizedLogPowerMajorant
      C kappa 1 (1 / 2) (1 / 64) (m : ℝ)) atTop (nhds 0)
  exact h.comp tendsto_natCast_atTop_atTop

lemma exists_eventually_actualSelectedClassicalAdmissibleCriticalHalfPNTLayerNorm_le_majorant
    {b : ℝ} (hb : 0 < b)
    (selection : UniformNaturalPointGoodHeightSelection) :
    ∃ C kappa : ℝ, 0 ≤ C ∧ 0 < kappa ∧
      ∀ᶠ m : ℕ in atTop,
        dynamicPositiveOutsideClusterPNTLayerNorm
            (selectedClassicalAdmissibleGoodHeight b selection) ∅
            (actualSelectedHeightCriticalHalfCanonicalInput
              (selectedClassicalAdmissibleGoodHeight b selection))
            (0 : Fin 2) (m : ℝ) ≤
          classicalCriticalHalfMajorant C kappa m := by
  let H := selectedClassicalAdmissibleGoodHeight b selection
  rcases exists_canonicalTwoStripOutsideCluster_uniform_norm_lower_bound
      H (1 / 2) ∅ with ⟨kappa, hkappa, hnorm⟩
  rcases
      exists_eventually_dynamicPositiveOutsideClusterPNTLayerNorm_div_target_le_actualHybridMajorant_selectedHeight
        (input := actualSelectedHeightCriticalHalfCanonicalInput H)
        (i := (0 : Fin 2)) (beta := 1) (tau := (1 / 2 : ℝ))
        (alpha := 1 / 64) (kappa := kappa)
        (eventually_selectedClassicalAdmissibleGoodHeight_le_polynomialHeight_real
          hb (by norm_num) selection)
        (tendsto_selectedClassicalAdmissibleGoodHeight_atTop hb selection)
        hkappa
        (by
          intro x rho hrho
          exact hnorm x rho hrho)
        (by
          intro x rho hrho
          exact actualSelectedHeightCriticalHalfCanonicalInput_low_re_le hrho)
        (by norm_num) with
    ⟨C, hC, hboundReal⟩
  have hbound := tendsto_natCast_atTop_atTop.eventually hboundReal
  refine ⟨C, kappa, hC, hkappa, ?_⟩
  filter_upwards [hbound] with m hm
  simpa [H, classicalCriticalHalfMajorant, targetZeroPowerAmplitude,
    dynamicPositiveOutsideClusterPNTLayerNorm] using hm

noncomputable def classicalDyadicCarlsonPositiveZeroTailMajorant
    (E eta C kappa D rate : ℝ) (m : ℕ) : ℝ :=
  (classicalCriticalHalfMajorant E eta m +
    classicalDyadicCarlsonMiddleMajorant C kappa D rate m) +
  classicalDyadicCarlsonSqrtLogMajorant D rate m

lemma tendsto_classicalDyadicCarlsonPositiveZeroTailMajorant_zero
    {E eta C kappa D rate : ℝ}
    (hE : 0 ≤ E) (heta : 0 < eta)
    (hC : 0 ≤ C) (hkappa : 0 < kappa) (hrate : 0 < rate) :
    Tendsto
      (classicalDyadicCarlsonPositiveZeroTailMajorant
        E eta C kappa D rate) atTop (nhds 0) := by
  simpa [classicalDyadicCarlsonPositiveZeroTailMajorant] using
    ((tendsto_classicalCriticalHalfMajorant_zero hE heta).add
      (tendsto_classicalDyadicCarlsonMiddleMajorant_zero
        hC hkappa hrate)).add
      (tendsto_classicalDyadicCarlsonSqrtLogMajorant_zero D hrate)

lemma exists_selectedClassicalAdmissibleDyadicCarlsonQuantitativePositiveZeroTailMajorant :
    ∃ b rate D : ℝ,
      0 < b ∧ 0 < rate ∧ 0 < D ∧
      IsCarlsonMovingDyadicLogPowerGap
        (classicalAdmissibleDyadicCarlsonGapWidth rate) ∧
      ∀ selection : UniformNaturalPointGoodHeightSelection,
        IsSelectedHeightDynamicZeroFree
          (selectedClassicalAdmissibleGoodHeight b selection)
          (classicalAdmissibleDyadicCarlsonGapWidth rate) ∧
        ∃ E eta C kappa : ℝ,
          0 ≤ E ∧ 0 < eta ∧ 0 ≤ C ∧ 0 < kappa ∧
          Tendsto
            (classicalDyadicCarlsonPositiveZeroTailMajorant
              E eta C kappa D rate) atTop (nhds 0) ∧
          ∀ᶠ m : ℕ in atTop,
            dynamicPositivePNTTailNorm
                (selectedClassicalAdmissibleGoodHeight b selection) (m : ℝ) ≤
              classicalDyadicCarlsonPositiveZeroTailMajorant
                E eta C kappa D rate m := by
  rcases exists_selectedClassicalAdmissibleDyadicCarlsonQuantitativeMassMajorant with
    ⟨b, rate, D, hb, hrate, hD, hgap, hDzero, hselected⟩
  refine ⟨b, rate, D, hb, hrate, hD, hgap, ?_⟩
  intro selection
  let H := selectedClassicalAdmissibleGoodHeight b selection
  have hselection := hselected selection
  rcases
      exists_eventually_actualSelectedClassicalAdmissibleCriticalHalfPNTLayerNorm_le_majorant
        hb selection with
    ⟨E, eta, hE, heta, hcritical⟩
  rcases
      exists_eventually_actualSelectedClassicalAdmissibleSevenEighthsLowMass_le_majorant
        hb selection with
    ⟨C, kappa, hC, hkappa, hlow⟩
  have hcap :=
    eventually_actualSelectedHeightMovingPositiveRightEdgeCap_of_dynamicZeroFree
      hselection.1
  refine ⟨hselection.1, E, eta, C, kappa, hE, heta, hC, hkappa,
    tendsto_classicalDyadicCarlsonPositiveZeroTailMajorant_zero
      hE heta hC hkappa hrate, ?_⟩
  filter_upwards [hcritical, hlow, hselection.2, hcap] with
      m hcriticalm hlowm hmasses hcapm
  have hlowm' :
      actualSelectedHeightSevenEighthsLowMass H m ≤
        classicalSevenEighthsLowMajorant C kappa m := by
    simpa [H, classicalSevenEighthsLowMajorant] using hlowm
  have hmiddle :
      actualSelectedHeightMovingCarlsonMiddleMass H
          (classicalAdmissibleDyadicCarlsonGapWidth rate) m ≤
        classicalDyadicCarlsonMiddleMajorant C kappa D rate m := by
    calc
      actualSelectedHeightMovingCarlsonMiddleMass H
          (classicalAdmissibleDyadicCarlsonGapWidth rate) m ≤
        actualSelectedHeightSevenEighthsLowMass H m +
          classicalDyadicCarlsonSqrtLogMajorant D rate m := hmasses.1
      _ ≤ classicalSevenEighthsLowMajorant C kappa m +
          classicalDyadicCarlsonSqrtLogMajorant D rate m :=
        add_le_add hlowm' le_rfl
      _ = classicalDyadicCarlsonMiddleMajorant C kappa D rate m := rfl
  calc
    dynamicPositivePNTTailNorm H (m : ℝ) ≤
        (dynamicPositiveOutsideClusterPNTLayerNorm H ∅
            (actualSelectedHeightCriticalHalfCanonicalInput H)
            0 (m : ℝ) +
          actualSelectedHeightMovingCarlsonMiddleMass H
            (classicalAdmissibleDyadicCarlsonGapWidth rate) m) +
        actualSelectedHeightMovingCarlsonStripMass H
          (classicalAdmissibleDyadicCarlsonGapWidth rate) m :=
      dynamicPositivePNTTailNorm_le_selectedCriticalHalf_add_movingMasses hcapm
    _ ≤ (classicalCriticalHalfMajorant E eta m +
          classicalDyadicCarlsonMiddleMajorant C kappa D rate m) +
        classicalDyadicCarlsonSqrtLogMajorant D rate m :=
      add_le_add (add_le_add hcriticalm hmiddle) hmasses.2
    _ = classicalDyadicCarlsonPositiveZeroTailMajorant
        E eta C kappa D rate m := rfl

end PrimeNumberTheorem
