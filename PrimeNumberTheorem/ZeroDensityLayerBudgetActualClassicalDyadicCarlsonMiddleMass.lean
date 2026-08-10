import PrimeNumberTheorem.ZeroDensityLayerBudgetActualClassicalDyadicCarlsonGap

/-!
# Classical selected-height dyadic Carlson middle mass

This module connects the classical admissible subpolynomial good height to the
existing polynomial-height Carlson mass estimates.

The key point is a domination argument, not selector monotonicity.  A uniform
good-height selector is only known to land in a unit interval.  We first prove
the strict asymptotic margin

`pintzCarlsonHeight k m + 1 <= m ^ alpha`.

The two unit-window certificates then imply that the classical selected height
is eventually below the polynomial selected height.  This gives decay of the
fixed low strip.  The remaining part of the moving middle strip is embedded in
the automatic dyadic fixed-anchor window, whose mass already tends to zero.
-/

open Filter Real
open scoped Topology

namespace PrimeNumberTheorem

/-- A positive polynomial height eventually dominates the Pintz--Carlson
subpolynomial height with one full unit of margin. -/
lemma eventually_pintzCarlsonHeight_add_one_le_nat_rpow
    {k alpha : ℝ} (hk : 0 ≤ k) (halpha : 0 < alpha) :
    ∀ᶠ m : ℕ in atTop,
      pintzCarlsonHeight k (m : ℝ) + 1 ≤ (m : ℝ) ^ alpha := by
  have hs : Tendsto pntSqrtLog atTop atTop := tendsto_pntSqrtLog_atTop
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    hs.eventually_ge_atTop (max 1 ((k + 1) / alpha))] with m hm hsqrt
  have hmR : (0 : ℝ) < m := by
    exact_mod_cast hm
  have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
  have hs_nonneg : 0 ≤ pntSqrtLog m := Real.sqrt_nonneg _
  have hs_one : 1 ≤ pntSqrtLog m := le_trans (le_max_left _ _) hsqrt
  have hs_ratio : (k + 1) / alpha ≤ pntSqrtLog m :=
    le_trans (le_max_right _ _) hsqrt
  have hmul : k + 1 ≤ alpha * pntSqrtLog m := by
    have := (div_le_iff₀ halpha).mp hs_ratio
    nlinarith
  have hlogtwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hexp_one : 1 ≤ Real.exp (k * pntSqrtLog m) := by
    rw [one_le_exp_iff]
    positivity
  have hexp_sum : Real.exp (k * pntSqrtLog m) + 1 ≤
      2 * Real.exp (k * pntSqrtLog m) := by
    linarith
  have hscale : Real.log 2 + k * pntSqrtLog m ≤
      alpha * (pntSqrtLog m) ^ 2 := by
    have := mul_le_mul_of_nonneg_right hmul hs_nonneg
    nlinarith
  calc
    pintzCarlsonHeight k (m : ℝ) + 1
        = Real.exp (k * pntSqrtLog m) + 1 := by
            rfl
    _ ≤ 2 * Real.exp (k * pntSqrtLog m) := hexp_sum
    _ = Real.exp (Real.log 2 + k * pntSqrtLog m) := by
          rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ Real.exp (alpha * (pntSqrtLog m) ^ 2) :=
      Real.exp_le_exp.mpr hscale
    _ = (m : ℝ) ^ alpha := by
          rw [show (pntSqrtLog m) ^ 2 = Real.log (m : ℝ) by
            simpa [pntSqrtLog] using Real.sq_sqrt hlog]
          rw [mul_comm]
          exact (Real.rpow_def_of_pos hmR alpha).symm

/-- The classical and polynomial selectors need not be monotone.  Their unit
window certificates, together with the one-unit asymptotic margin, still order
their selected heights eventually. -/
lemma eventually_selectedClassicalAdmissibleGoodHeight_le_selectedUniformGoodHeight
    {b alpha : ℝ} (hb : 0 < b) (halpha : 0 < alpha)
    (selection : UniformNaturalPointGoodHeightSelection) :
    ∀ᶠ m : ℕ in atTop,
      selectedClassicalAdmissibleGoodHeight b selection (m : ℝ) ≤
        selectedUniformGoodHeight alpha selection (m : ℝ) := by
  have hk : 0 ≤ classicalAdmissibleBalancedRate b :=
    (classicalAdmissibleBalancedRate_pos hb).le
  have hclassical :=
    tendsto_natCast_atTop_atTop.eventually
      (eventually_selectedClassicalAdmissibleGoodHeight_mem hb selection)
  have huniform :=
    tendsto_natCast_atTop_atTop.eventually
      (eventually_selectedUniformGoodHeight_mem halpha selection)
  filter_upwards [hclassical, huniform,
    eventually_pintzCarlsonHeight_add_one_le_nat_rpow hk halpha] with
      m hmC hmU hheight
  dsimp [pintzCarlsonGoodHeightBase] at hmC
  have hC : selectedClassicalAdmissibleGoodHeight b selection (m : ℝ) ≤
      pintzCarlsonHeight (classicalAdmissibleBalancedRate b) (m : ℝ) := by
    linarith [hmC.2]
  have hgap : pintzCarlsonHeight
      (classicalAdmissibleBalancedRate b) (m : ℝ) ≤
      (m : ℝ) ^ alpha - 1 := by
    linarith
  exact hC.trans (hgap.trans hmU.1)

/-- Fixed low-strip mass is monotone in the truncation height. -/
lemma actualSelectedHeightSevenEighthsLowMass_mono
    {H K : ℝ → ℝ} {m : ℕ} (hHK : H (m : ℝ) ≤ K (m : ℝ)) :
    actualSelectedHeightSevenEighthsLowMass H m ≤
      actualSelectedHeightSevenEighthsLowMass K m := by
  unfold actualSelectedHeightSevenEighthsLowMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro rho hrho
    rw [mem_actualPositiveCarlsonStrip] at hrho ⊢
    exact ⟨hrho.1, hrho.2.1, hrho.2.2.1.trans hHK, hrho.2.2.2⟩
  · intro rho _ _
    positivity

/-- The fixed low strip also decays at the classical admissible selected
height.  The proof compares it to a polynomial selected height with the same
uniform selector. -/
lemma tendsto_actualSelectedClassicalAdmissibleSevenEighthsLowMass_zero
    {b alpha : ℝ} (hb : 0 < b) (halpha : 0 < alpha)
    (halpha_lt : alpha < 1 / 16)
    (selection : UniformNaturalPointGoodHeightSelection) :
    Tendsto
      (actualSelectedHeightSevenEighthsLowMass
        (selectedClassicalAdmissibleGoodHeight b selection))
      atTop (𝓝 0) := by
  have hheight :=
    eventually_selectedClassicalAdmissibleGoodHeight_le_selectedUniformGoodHeight
      hb halpha selection
  have hle : ∀ᶠ m : ℕ in atTop,
      actualSelectedHeightSevenEighthsLowMass
          (selectedClassicalAdmissibleGoodHeight b selection) m ≤
        actualSelectedHeightSevenEighthsLowMass
          (selectedUniformGoodHeight alpha selection) m := by
    filter_upwards [hheight] with m hm
    exact actualSelectedHeightSevenEighthsLowMass_mono hm
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun m =>
      actualSelectedHeightSevenEighthsLowMass_nonneg _ _
  · exact hle
  · exact tendsto_actualSelectedHeightSevenEighthsLowMass_zero
      halpha halpha_lt (by norm_num : (0 : ℝ) < 1 / 16)
      (by norm_num : (0 : ℝ) < 1 / 32)
      (by norm_num : (1 / 16 : ℝ) + 1 / 32 < 1 / 8) selection

/-- At any height below a polynomial ceiling, the moving middle strip is
covered by the fixed low strip and the dyadic fixed-anchor window. -/
lemma actualSelectedHeightMovingCarlsonMiddleMass_le_low_add_dyadicFixedAnchor
    {H : ℝ → ℝ} {alpha : ℝ} {delta : ℕ → ℝ} {m : ℕ}
    (hheight : H (m : ℝ) ≤ carlsonPolynomialHeight alpha (m : ℝ))
    (hdelta_pos : 0 < delta m) :
    actualSelectedHeightMovingCarlsonMiddleMass H delta m ≤
      actualSelectedHeightSevenEighthsLowMass H m +
        actualDyadicCarlsonFixedAnchorMass alpha delta
          (dyadicCarlsonLayerSchedule delta) m := by
  let S := actualPositiveCarlsonStrip (1 / 2) (1 - 2 * delta m) (H (m : ℝ))
  let L := actualPositiveCarlsonStrip (1 / 2) (7 / 8) (H (m : ℝ))
  let W := actualDyadicCarlsonFixedAnchorWindow alpha delta
    (dyadicCarlsonLayerSchedule delta) m
  have hsubset : S ⊆ L ∪ W := by
    intro rho hrho
    have hr := mem_actualPositiveCarlsonStrip.mp hrho
    by_cases hlow : rho.re ≤ 7 / 8
    · apply Finset.mem_union_left
      exact mem_actualPositiveCarlsonStrip.mpr
        ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hlow⟩
    · apply Finset.mem_union_right
      apply mem_actualDyadicCarlsonMinimalFixedAnchorWindow
      · exact hr.1
      · exact hr.2.1
      · exact hr.2.2.1.trans hheight
      · exact hdelta_pos
      · exact lt_of_not_ge hlow
      · linarith [hr.2.2.2.2]
  have hdisjoint : Disjoint L W := by
    rw [Finset.disjoint_left]
    intro rho hrL hrW
    have hLmem := mem_actualPositiveCarlsonStrip.mp hrL
    have hWmem := hrW
    simp only [W, actualDyadicCarlsonFixedAnchorWindow, Finset.mem_filter] at hWmem
    have hWre : 7 / 8 < rho.re := hWmem.2.1
    linarith [hLmem.2.2.2.2]
  have hsum : (∑ rho ∈ S, ‖pntRelativeZeroContribution (m : ℝ) rho‖) ≤
      ∑ rho ∈ L ∪ W, ‖pntRelativeZeroContribution (m : ℝ) rho‖ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro rho _ _
    positivity
  rw [Finset.sum_union hdisjoint] at hsum
  simpa [actualSelectedHeightMovingCarlsonMiddleMass,
    actualSelectedHeightSevenEighthsLowMass,
    actualDyadicCarlsonFixedAnchorMass, S, L, W] using hsum

/-- A dyadic Carlson gap forces the moving middle mass to zero at every
classical admissible selected height. -/
lemma tendsto_actualSelectedClassicalAdmissibleMovingMiddleMass_zero_of_dyadic
    {b alpha : ℝ} {delta : ℕ → ℝ}
    (hb : 0 < b) (halpha : 0 < alpha) (halpha_lt : alpha < 1 / 16)
    (selection : UniformNaturalPointGoodHeightSelection)
    (hdelta_nonneg : ∀ m, 0 ≤ delta m)
    (hdelta_pos : ∀ᶠ m : ℕ in atTop, 0 < delta m)
    (hdelta_le : ∀ᶠ m : ℕ in atTop, delta m ≤ 1 / 8)
    (hgap : IsCarlsonMovingDyadicLogPowerGap delta) :
    Tendsto
      (actualSelectedHeightMovingCarlsonMiddleMass
        (selectedClassicalAdmissibleGoodHeight b selection) delta)
      atTop (𝓝 0) := by
  have hheightToUniform :=
    eventually_selectedClassicalAdmissibleGoodHeight_le_selectedUniformGoodHeight
      hb halpha selection
  have huniform :=
    tendsto_natCast_atTop_atTop.eventually
      (eventually_selectedUniformGoodHeight_mem halpha selection)
  have hheight : ∀ᶠ m : ℕ in atTop,
      selectedClassicalAdmissibleGoodHeight b selection (m : ℝ) ≤
        carlsonPolynomialHeight alpha (m : ℝ) := by
    filter_upwards [hheightToUniform, huniform] with m hCU hU
    exact hCU.trans hU.2
  have hlow :=
    tendsto_actualSelectedClassicalAdmissibleSevenEighthsLowMass_zero
      hb halpha halpha_lt selection
  obtain ⟨A, C₁, C₂, hA, hC₁, hC₂, hfixed⟩ :=
    exists_constants_tendsto_actualDyadicCarlsonMinimalFixedAnchorMass_zero_automatic
      halpha halpha_lt.le hdelta_nonneg hdelta_pos hdelta_le hgap
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun m => by
      unfold actualSelectedHeightMovingCarlsonMiddleMass
      positivity
  · filter_upwards [hheight, hdelta_pos] with m hH hdelta
    exact actualSelectedHeightMovingCarlsonMiddleMass_le_low_add_dyadicFixedAnchor
      hH hdelta
  · simpa using hlow.add hfixed

/-- The same canonical constants simultaneously provide the classical
selected-height zero-free edge and decay of its Carlson-controlled moving
middle mass. -/
theorem exists_selectedClassicalAdmissibleDyadicCarlsonMiddleMassDecay :
    ∃ b rate : ℝ,
      0 < b ∧ 0 < rate ∧
        IsCarlsonMovingDyadicLogPowerGap
          (classicalAdmissibleDyadicCarlsonGapWidth rate) ∧
        ∀ selection : UniformNaturalPointGoodHeightSelection,
          IsSelectedHeightDynamicZeroFree
              (selectedClassicalAdmissibleGoodHeight b selection)
              (classicalAdmissibleDyadicCarlsonGapWidth rate) ∧
            Tendsto
              (actualSelectedHeightMovingCarlsonMiddleMass
                (selectedClassicalAdmissibleGoodHeight b selection)
                (classicalAdmissibleDyadicCarlsonGapWidth rate))
              atTop (𝓝 0) := by
  obtain ⟨b, rate, hb, hrate, hgap, hzeroFree⟩ :=
    exists_selectedClassicalAdmissibleDyadicCarlsonZeroFreeGap
  refine ⟨b, rate, hb, hrate, hgap, ?_⟩
  intro selection
  refine ⟨hzeroFree selection, ?_⟩
  apply tendsto_actualSelectedClassicalAdmissibleMovingMiddleMass_zero_of_dyadic
    hb (by norm_num : (0 : ℝ) < 1 / 64)
    (by norm_num : (1 / 64 : ℝ) < 1 / 16) selection
  · exact classicalAdmissibleDyadicCarlsonGapWidth_nonneg hrate
  · exact Filter.Eventually.of_forall fun m =>
      classicalAdmissibleDyadicCarlsonGapWidth_pos hrate m
  · exact eventually_classicalAdmissibleDyadicCarlsonGapWidth_le_eighth hrate
  · exact hgap

end PrimeNumberTheorem
