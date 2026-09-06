import PrimeNumberTheorem.ZeroDensityLayerBudgetActualClassicalDyadicCarlsonQuantitativeMass

open Filter Real Complex
open scoped Topology BigOperators

namespace PrimeNumberTheorem

lemma exists_eventually_actualSelectedClassicalAdmissibleSevenEighthsLowMass_le_majorant
    {b : ℝ} (hb : 0 < b)
    (selection : UniformNaturalPointGoodHeightSelection) :
    ∃ C kappa : ℝ, 0 ≤ C ∧ 0 < kappa ∧
      ∀ᶠ m : ℕ in atTop,
        actualSelectedHeightSevenEighthsLowMass
            (selectedClassicalAdmissibleGoodHeight b selection) m ≤
          actualHybridLowNormalizedLogPowerMajorant
            C kappa 1 (7 / 8) (1 / 64) (m : ℝ) := by
  let H := selectedClassicalAdmissibleGoodHeight b selection
  rcases exists_canonicalTwoStripOutsideCluster_uniform_norm_lower_bound
      H (7 / 8) ∅ with ⟨kappa, hkappa, hnorm⟩
  rcases ExplicitFormulaAux.exists_globalZeroMultiplicity_le_mul_log with
    ⟨C, hC, hglobalMultiplicity⟩
  have hHleReal : ∀ᶠ x : ℝ in atTop,
      H x ≤ carlsonPolynomialHeight (1 / 64) x :=
    eventually_selectedClassicalAdmissibleGoodHeight_le_polynomialHeight_real
      hb (by norm_num) selection
  have hHle : ∀ᶠ m : ℕ in atTop,
      H (m : ℝ) ≤ carlsonPolynomialHeight (1 / 64) (m : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually hHleReal
  have hHtop : Tendsto H atTop atTop := by
    simpa [H] using
      tendsto_selectedClassicalAdmissibleGoodHeight_atTop hb selection
  have hlogReal :=
    eventually_one_add_log_polynomialHeight_add_six_le_log_four
      (show (0 : ℝ) < 1 / 64 by norm_num)
  have hlog : ∀ᶠ m : ℕ in atTop,
      1 + Real.log ((m : ℝ) ^ (1 / 64 : ℝ) + 6) ≤
        ((1 / 64 : ℝ) + 2) * Real.log (m : ℝ) ^ 4 :=
    tendsto_natCast_atTop_atTop.eventually hlogReal
  refine ⟨C, kappa, hC, hkappa, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ),
      hHtop.comp tendsto_natCast_atTop_atTop |>.eventually
        (eventually_ge_atTop (4 : ℝ)), hHle, hlog] with
      m hm hHfour hHupper hlogBound
  have hmPos : 0 < (m : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hm)
  let layer := actualPositiveCarlsonStrip
    (1 / 2) (7 / 8) (H (m : ℝ))
  have hnormLayer : ∀ rho ∈ layer, kappa ≤ ‖rho‖ := by
    intro rho hrho
    rcases mem_actualPositiveCarlsonStrip.mp hrho with
      ⟨hzero, him, himHeight, _, hreUpper⟩
    apply hnorm (m : ℝ) rho
    apply Finset.mem_filter.mpr
    constructor
    · exact mem_positiveNontrivialZerosOutsideClusterFinset.mpr
        ⟨hzero, him, himHeight, by simp⟩
    · exact pntHybridCanonicalTwoStripOutsideCluster_low_cover
        (mem_positiveNontrivialZerosOutsideClusterFinset.mpr
          ⟨hzero, him, himHeight, by simp⟩) hreUpper
  have hkernel : ∀ rho ∈ layer,
      ‖pntRelativeSimpleZeroKernel (m : ℝ) rho‖ ≤
        stripEndpointRelativeKernelBudget kappa (7 / 8) (m : ℝ) := by
    intro rho hrho
    rcases mem_actualPositiveCarlsonStrip.mp hrho with
      ⟨_, _, _, _, hreUpper⟩
    exact norm_pntRelativeSimpleZeroKernel_le_stripEndpoint
      (by exact_mod_cast hm) hkappa (hnormLayer rho hrho) hreUpper
  have hkernelNonneg :
      0 ≤ stripEndpointRelativeKernelBudget kappa (7 / 8) (m : ℝ) :=
    stripEndpointRelativeKernelBudget_nonneg
      (by exact_mod_cast (Nat.zero_le m)) hkappa.le
  have hmass : analyticMultiplicityMass layer ≤
      ExplicitFormulaAux.globalZeroMultiplicity (H (m : ℝ)) := by
    have hsubset : layer ⊆ nontrivialZerosFinset (H (m : ℝ)) := by
      intro rho hrho
      rcases mem_actualPositiveCarlsonStrip.mp hrho with
        ⟨hzero, him, himHeight, _, _⟩
      exact mem_nontrivialZerosFinset.mpr
        ⟨hzero, by simpa [abs_of_pos him] using himHeight⟩
    unfold analyticMultiplicityMass ExplicitFormulaAux.globalZeroMultiplicity
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun rho _ _ => Nat.cast_nonneg _)
  have hphysical :
      actualSelectedHeightSevenEighthsLowMass H m ≤
        actualHybridGlobalLowLayerMajorant
          C (H (m : ℝ)) kappa (7 / 8) (m : ℝ) := by
    calc
      actualSelectedHeightSevenEighthsLowMass H m =
          ∑ rho ∈ layer, ‖pntRelativeZeroContribution (m : ℝ) rho‖ := rfl
      _ ≤ stripEndpointRelativeKernelBudget kappa (7 / 8) (m : ℝ) *
            analyticMultiplicityMass layer :=
        sum_norm_pntRelativeZeroContribution_le_kernel_mul_multiplicityMass
          layer (m : ℝ)
          (stripEndpointRelativeKernelBudget kappa (7 / 8) (m : ℝ))
          hkernelNonneg hkernel
      _ ≤ stripEndpointRelativeKernelBudget kappa (7 / 8) (m : ℝ) *
            ExplicitFormulaAux.globalZeroMultiplicity (H (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hmass hkernelNonneg
      _ ≤ stripEndpointRelativeKernelBudget kappa (7 / 8) (m : ℝ) *
            (C * H (m : ℝ) * (1 + Real.log (H (m : ℝ) + 6))) :=
        mul_le_mul_of_nonneg_left
          (hglobalMultiplicity (H (m : ℝ)) hHfour) hkernelNonneg
      _ = actualHybridGlobalLowLayerMajorant
            C (H (m : ℝ)) kappa (7 / 8) (m : ℝ) := by
        unfold actualHybridGlobalLowLayerMajorant
        ring
  have hselected :
      actualHybridGlobalLowLayerMajorant
          C (H (m : ℝ)) kappa (7 / 8) (m : ℝ) ≤
        actualHybridGlobalLowLayerMajorant C
          (carlsonPolynomialHeight (1 / 64) (m : ℝ))
          kappa (7 / 8) (m : ℝ) :=
    actualHybridGlobalLowLayerMajorant_mono_height
      hC hkappa hmPos.le hHfour hHupper
  have hcoefficient :
      0 ≤ C * kappa⁻¹ * (m : ℝ) ^
        ((7 / 8 : ℝ) - 1 + 1 / 64) := by positivity
  calc
    actualSelectedHeightSevenEighthsLowMass H m ≤
        actualHybridGlobalLowLayerMajorant C
          (carlsonPolynomialHeight (1 / 64) (m : ℝ))
          kappa (7 / 8) (m : ℝ) := hphysical.trans hselected
    _ = actualHybridGlobalLowLayerMajorant C
          (carlsonPolynomialHeight (1 / 64) (m : ℝ))
          kappa (7 / 8) (m : ℝ) /
        targetZeroPowerAmplitude 1 (m : ℝ) := by
      rw [show targetZeroPowerAmplitude 1 (m : ℝ) = 1 by
        simp [targetZeroPowerAmplitude], div_one]
    _ = C * kappa⁻¹ *
          (m : ℝ) ^ ((7 / 8 : ℝ) - 1 + 1 / 64) *
          (1 + Real.log ((m : ℝ) ^ (1 / 64 : ℝ) + 6)) :=
      actualHybridGlobalLowLayerMajorant_div_target_eq hmPos
    _ ≤ C * kappa⁻¹ *
          (m : ℝ) ^ ((7 / 8 : ℝ) - 1 + 1 / 64) *
          (((1 / 64 : ℝ) + 2) * Real.log (m : ℝ) ^ 4) :=
      mul_le_mul_of_nonneg_left hlogBound hcoefficient
    _ = actualHybridLowNormalizedLogPowerMajorant
          C kappa 1 (7 / 8) (1 / 64) (m : ℝ) := by
      unfold actualHybridLowNormalizedLogPowerMajorant
      ring

noncomputable def classicalSevenEighthsLowMajorant
    (C kappa : ℝ) (m : ℕ) : ℝ :=
  actualHybridLowNormalizedLogPowerMajorant
    C kappa 1 (7 / 8) (1 / 64) (m : ℝ)

lemma classicalSevenEighthsLowMajorant_eq
    (C kappa : ℝ) (m : ℕ) :
    classicalSevenEighthsLowMajorant C kappa m =
      (C * kappa⁻¹ * ((1 / 64 : ℝ) + 2)) *
        (m : ℝ) ^ (-(7 / 64 : ℝ)) * Real.log (m : ℝ) ^ 4 := by
  unfold classicalSevenEighthsLowMajorant
    actualHybridLowNormalizedLogPowerMajorant
  congr 2
  norm_num

lemma tendsto_classicalSevenEighthsLowMajorant_zero
    {C kappa : ℝ} (hC : 0 ≤ C) (hkappa : 0 < kappa) :
    Tendsto (classicalSevenEighthsLowMajorant C kappa) atTop (nhds 0) := by
  have h := tendsto_actualHybridLowNormalizedLogPowerMajorant_zero
    (C := C) (kappa := kappa) (beta := 1) (tau := 7 / 8)
    (alpha := 1 / 64) (epsilon := 1 / 128)
    hC hkappa (by norm_num) (by norm_num) (by norm_num)
  change Tendsto
    (fun m : ℕ => actualHybridLowNormalizedLogPowerMajorant
      C kappa 1 (7 / 8) (1 / 64) (m : ℝ)) atTop (nhds 0)
  exact h.comp tendsto_natCast_atTop_atTop

noncomputable def classicalDyadicCarlsonMiddleMajorant
    (C kappa D rate : ℝ) (m : ℕ) : ℝ :=
  classicalSevenEighthsLowMajorant C kappa m +
    classicalDyadicCarlsonSqrtLogMajorant D rate m

lemma tendsto_classicalDyadicCarlsonMiddleMajorant_zero
    {C kappa D rate : ℝ}
    (hC : 0 ≤ C) (hkappa : 0 < kappa) (hrate : 0 < rate) :
    Tendsto (classicalDyadicCarlsonMiddleMajorant C kappa D rate)
      atTop (nhds 0) := by
  change Tendsto
    (fun m : ℕ =>
      classicalSevenEighthsLowMajorant C kappa m +
        classicalDyadicCarlsonSqrtLogMajorant D rate m)
    atTop (nhds 0)
  simpa only [add_zero] using
    (tendsto_classicalSevenEighthsLowMajorant_zero hC hkappa).add
      (tendsto_classicalDyadicCarlsonSqrtLogMajorant_zero D hrate)

lemma exists_selectedClassicalAdmissibleDyadicCarlsonQuantitativeMiddleMajorant :
    ∃ b rate D : ℝ,
      0 < b ∧ 0 < rate ∧ 0 < D ∧
      IsCarlsonMovingDyadicLogPowerGap
        (classicalAdmissibleDyadicCarlsonGapWidth rate) ∧
      ∀ selection : UniformNaturalPointGoodHeightSelection,
        IsSelectedHeightDynamicZeroFree
          (selectedClassicalAdmissibleGoodHeight b selection)
          (classicalAdmissibleDyadicCarlsonGapWidth rate) ∧
        ∃ C kappa : ℝ, 0 ≤ C ∧ 0 < kappa ∧
          Tendsto (classicalDyadicCarlsonMiddleMajorant C kappa D rate)
            atTop (nhds 0) ∧
          ∀ᶠ m : ℕ in atTop,
            actualSelectedHeightMovingCarlsonMiddleMass
                (selectedClassicalAdmissibleGoodHeight b selection)
                (classicalAdmissibleDyadicCarlsonGapWidth rate) m ≤
              classicalDyadicCarlsonMiddleMajorant C kappa D rate m := by
  rcases exists_selectedClassicalAdmissibleDyadicCarlsonQuantitativeMassMajorant with
    ⟨b, rate, D, hb, hrate, hD, hgap, hDzero, hselected⟩
  refine ⟨b, rate, D, hb, hrate, hD, hgap, ?_⟩
  intro selection
  rcases
      exists_eventually_actualSelectedClassicalAdmissibleSevenEighthsLowMass_le_majorant
        hb selection with
    ⟨C, kappa, hC, hkappa, hlow⟩
  refine ⟨(hselected selection).1, C, kappa, hC, hkappa,
    tendsto_classicalDyadicCarlsonMiddleMajorant_zero hC hkappa hrate, ?_⟩
  filter_upwards [(hselected selection).2, hlow] with m hm hlowm
  have hlowm' :
      actualSelectedHeightSevenEighthsLowMass
          (selectedClassicalAdmissibleGoodHeight b selection) m ≤
        classicalSevenEighthsLowMajorant C kappa m := by
    simpa [classicalSevenEighthsLowMajorant] using hlowm
  calc
    actualSelectedHeightMovingCarlsonMiddleMass
        (selectedClassicalAdmissibleGoodHeight b selection)
        (classicalAdmissibleDyadicCarlsonGapWidth rate) m ≤
      actualSelectedHeightSevenEighthsLowMass
          (selectedClassicalAdmissibleGoodHeight b selection) m +
        classicalDyadicCarlsonSqrtLogMajorant D rate m := hm.1
    _ ≤ classicalSevenEighthsLowMajorant C kappa m +
        classicalDyadicCarlsonSqrtLogMajorant D rate m :=
      add_le_add hlowm' le_rfl
    _ = classicalDyadicCarlsonMiddleMajorant C kappa D rate m := rfl

end PrimeNumberTheorem
