import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDyadicCarlsonMinimalLayerMargin
import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonMovingHeightConditions

/-!
# Uniform height conditions for the minimal dyadic Carlson family

The active dyadic gaps all lie in `(0, 1 / 8]`, hence every associated
Carlson line satisfies `sigma >= 3 / 4`.  Their balanced heights are bounded
below by the single moving height with exponent `3 * alpha * delta`.  This
produces one eventual threshold valid for every active layer and removes the
remaining family-wise height-condition premise.
-/

namespace PrimeNumberTheorem

open Filter Topology

noncomputable section

/-- Uniform elementary package for Carlson's explicit pointwise height
conditions on every line `sigma >= 3 / 4`. -/
theorem carlsonPointwiseHeightConditions_of_threeFourths
    {C₁ C₂ sigma T : ℝ}
    (hT6 : 6 ≤ T)
    (hlog17 : 17 ≤ Real.log T)
    (hsigma : 3 / 4 ≤ sigma)
    (hC₁ : C₁ ≤ T)
    (hC₂ : C₂ ≤ T) :
    CarlsonPointwiseHeightConditions C₁ C₂ sigma T := by
  have hlogPos : 0 < Real.log T := by linarith
  have hsmall : 4 / Real.log T < 1 / 4 := by
    rw [div_lt_iff₀ hlogPos]
    nlinarith
  have hTOne : 1 ≤ T := by linarith
  have hexponent : 0 ≤ 2 * sigma - 1 := by linarith
  exact
    ⟨hT6, by linarith, hsmall.trans_le (by linarith),
      Real.one_le_rpow hTOne hexponent, hC₁, hC₂⟩

/-- The stronger dyadic margin implies the ordinary moving Carlson margin. -/
theorem isCarlsonMovingQuadraticLogPowerGap_of_dyadic
    {delta : ℕ → ℝ}
    (hdelta : ∀ᶠ m : ℕ in atTop, 0 < delta m)
    (hdeltaUpper : ∀ᶠ m : ℕ in atTop, delta m ≤ 1 / 8)
    (hgap : IsCarlsonMovingDyadicLogPowerGap delta) :
    IsCarlsonMovingQuadraticLogPowerGap delta := by
  unfold IsCarlsonMovingDyadicLogPowerGap at hgap
  unfold IsCarlsonMovingQuadraticLogPowerGap
  apply tendsto_atTop_mono' atTop ?_ hgap
  filter_upwards [hdelta, hdeltaUpper] with m hm hmUpper
  have hinvOne : 1 ≤ (delta m)⁻¹ :=
    (one_le_inv₀ hm).2 (hmUpper.trans (by norm_num))
  have hlogInv : 0 ≤ Real.log (delta m)⁻¹ :=
    Real.log_nonneg hinvOne
  linarith

/-- Common lower height for every balanced dyadic layer. -/
noncomputable def dyadicCarlsonBalancedHeightFloor
    (alpha : ℝ) (delta : ℕ → ℝ) (m : ℕ) : ℝ :=
  carlsonPolynomialHeight (3 * alpha * delta m) (m : ℝ)

/-- The complete dyadic margin makes the common balanced-height floor
cofinal. -/
theorem tendsto_dyadicCarlsonBalancedHeightFloor_atTop
    {alpha : ℝ} {delta : ℕ → ℝ}
    (halpha : 0 < alpha)
    (hdelta : ∀ᶠ m : ℕ in atTop, 0 < delta m)
    (hdeltaUpper : ∀ᶠ m : ℕ in atTop, delta m ≤ 1 / 8)
    (hgap : IsCarlsonMovingDyadicLogPowerGap delta) :
    Tendsto (dyadicCarlsonBalancedHeightFloor alpha delta)
      atTop atTop := by
  have hdeltaPair :
      ∀ᶠ m : ℕ in atTop, 0 < delta m ∧ delta m ≤ 1 / 8 := by
    filter_upwards [hdelta, hdeltaUpper] with m hm hmUpper
    exact ⟨hm, hmUpper⟩
  have hdeltaLog :
      Tendsto (fun m : ℕ => delta m * Real.log (m : ℝ))
        atTop atTop :=
    tendsto_delta_mul_log_of_quadraticLogPowerGap hdeltaPair
      (isCarlsonMovingQuadraticLogPowerGap_of_dyadic
        hdelta hdeltaUpper hgap)
  have hfloorLog :
      Tendsto
        (fun m : ℕ =>
          (3 * alpha * delta m) * Real.log (m : ℝ))
        atTop atTop := by
    have hscaled :
        Tendsto
          (fun m : ℕ =>
            (3 * alpha) * (delta m * Real.log (m : ℝ)))
          atTop atTop :=
      hdeltaLog.const_mul_atTop (by positivity)
    convert hscaled using 1 <;> ring
  exact tendsto_movingPolynomialHeight_atTop hfloorLog

theorem tendsto_log_dyadicCarlsonBalancedHeightFloor_atTop
    {alpha : ℝ} {delta : ℕ → ℝ}
    (halpha : 0 < alpha)
    (hdelta : ∀ᶠ m : ℕ in atTop, 0 < delta m)
    (hdeltaUpper : ∀ᶠ m : ℕ in atTop, delta m ≤ 1 / 8)
    (hgap : IsCarlsonMovingDyadicLogPowerGap delta) :
    Tendsto
      (fun m =>
        Real.log (dyadicCarlsonBalancedHeightFloor alpha delta m))
      atTop atTop := by
  have hdeltaPair :
      ∀ᶠ m : ℕ in atTop, 0 < delta m ∧ delta m ≤ 1 / 8 := by
    filter_upwards [hdelta, hdeltaUpper] with m hm hmUpper
    exact ⟨hm, hmUpper⟩
  have hdeltaLog :
      Tendsto (fun m : ℕ => delta m * Real.log (m : ℝ))
        atTop atTop :=
    tendsto_delta_mul_log_of_quadraticLogPowerGap hdeltaPair
      (isCarlsonMovingQuadraticLogPowerGap_of_dyadic
        hdelta hdeltaUpper hgap)
  have hfloorLog :
      Tendsto
        (fun m : ℕ =>
          (3 * alpha * delta m) * Real.log (m : ℝ))
        atTop atTop := by
    have hscaled :
        Tendsto
          (fun m : ℕ =>
            (3 * alpha) * (delta m * Real.log (m : ℝ)))
          atTop atTop :=
      hdeltaLog.const_mul_atTop (by positivity)
    convert hscaled using 1 <;> ring
  exact tendsto_log_movingPolynomialHeight_atTop hfloorLog

/-- One eventual threshold supplies both Carlson heights for every active
minimal dyadic layer. -/
theorem actualDynamicDyadicCarlsonMinimalHeightConditions
    {C₁ C₂ alpha : ℝ} {delta : ℕ → ℝ}
    (halpha : 0 < alpha)
    (halphaUpper : alpha ≤ 1 / 16)
    (hdeltaNonneg : ∀ m, 0 ≤ delta m)
    (hdelta : ∀ᶠ m : ℕ in atTop, 0 < delta m)
    (hdeltaUpper : ∀ᶠ m : ℕ in atTop, delta m ≤ 1 / 8)
    (hgap : IsCarlsonMovingDyadicLogPowerGap delta) :
    ActualDynamicCarlsonGapFamilyHeightConditions C₁ C₂ alpha
      (dyadicCarlsonLayerSchedule delta) (dyadicCarlsonGap delta) := by
  have hfloor :=
    tendsto_dyadicCarlsonBalancedHeightFloor_atTop
      halpha hdelta hdeltaUpper hgap
  have hfloorLog :=
    tendsto_log_dyadicCarlsonBalancedHeightFloor_atTop
      halpha hdelta hdeltaUpper hgap
  have hlogNat :
      Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hfixedLog :
      Tendsto (fun m : ℕ => alpha * Real.log (m : ℝ))
        atTop atTop :=
    hlogNat.const_mul_atTop halpha
  have hfixed :
      Tendsto
        (fun m : ℕ => carlsonPolynomialHeight alpha (m : ℝ))
        atTop atTop :=
    tendsto_movingPolynomialHeight_atTop hfixedLog
  have hfixedLogHeight :
      Tendsto
        (fun m : ℕ =>
          Real.log (carlsonPolynomialHeight alpha (m : ℝ)))
        atTop atTop :=
    tendsto_log_movingPolynomialHeight_atTop hfixedLog
  unfold ActualDynamicCarlsonGapFamilyHeightConditions
  filter_upwards
      [hdelta, hdeltaUpper, eventually_ge_atTop (1 : ℕ),
        hfloor.eventually_ge_atTop 6,
        hfloor.eventually_ge_atTop C₁,
        hfloor.eventually_ge_atTop C₂,
        hfloorLog.eventually_ge_atTop 17,
        hfixed.eventually_ge_atTop 6,
        hfixed.eventually_ge_atTop C₁,
        hfixed.eventually_ge_atTop C₂,
        hfixedLogHeight.eventually_ge_atTop 17] with
      m hm hmUpper hmOne hfloor6 hC₁Floor hC₂Floor hlogFloor
        hfixed6 hC₁Fixed hC₂Fixed hlogFixed
  intro i
  dsimp only [actualDynamicCarlsonGapSchedule]
  let g := dyadicCarlsonGap delta m i.1
  have hgPos : 0 < g := by
    dsimp [g, dyadicCarlsonGap]
    positivity
  have houter :=
    dyadicCarlsonLayerCount_outer_le_quarter hm hmUpper
  have hactive :=
    dyadicCarlsonGap_active_of_outer_le
      halpha.le halphaUpper (hdeltaNonneg m) houter i
  have hgUpper : g ≤ 1 / 8 := by
    simpa [g] using hactive.1
  have hsigma : (3 / 4 : ℝ) ≤ 1 - 2 * g := by
    linarith
  have hmRealOne : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hmOne
  have hdeltaGap : delta m ≤ g := by
    dsimp [g]
    exact delta_le_dyadicCarlsonGap (hdeltaNonneg m)
  have hbalancedExponent :
      3 * alpha * delta m ≤
        carlsonTwoHeightBalancedCut (1 - 2 * g) alpha := by
    calc
      3 * alpha * delta m ≤ 3 * alpha * g :=
        mul_le_mul_of_nonneg_left hdeltaGap (by positivity)
      _ ≤ carlsonTwoHeightBalancedCut (1 - 2 * g) alpha :=
        three_mul_alpha_mul_delta_le_carlsonMovingBalancedCut
          halpha hgPos hgUpper
  have hbalancedHeight :
      dyadicCarlsonBalancedHeightFloor alpha delta m ≤
        carlsonPolynomialHeight
          (carlsonTwoHeightBalancedCut (1 - 2 * g) alpha)
          (m : ℝ) := by
    unfold dyadicCarlsonBalancedHeightFloor carlsonPolynomialHeight
    exact Real.rpow_le_rpow_of_exponent_le hmRealOne
      hbalancedExponent
  have hbalancedLog :
      Real.log (dyadicCarlsonBalancedHeightFloor alpha delta m) ≤
        Real.log
          (carlsonPolynomialHeight
            (carlsonTwoHeightBalancedCut (1 - 2 * g) alpha)
            (m : ℝ)) :=
    Real.log_le_log (by positivity) hbalancedHeight
  constructor
  · change
      CarlsonPointwiseHeightConditions C₁ C₂ (1 - 2 * g)
        (carlsonPolynomialHeight
          (carlsonTwoHeightBalancedCut (1 - 2 * g) alpha) (m : ℝ))
    exact carlsonPointwiseHeightConditions_of_threeFourths
      (hfloor6.trans hbalancedHeight)
      (hlogFloor.trans hbalancedLog)
      hsigma
      (hC₁Floor.trans hbalancedHeight)
      (hC₂Floor.trans hbalancedHeight)
  · simpa [g] using
      carlsonPointwiseHeightConditions_of_threeFourths
        hfixed6 hlogFixed hsigma hC₁Fixed hC₂Fixed

/-- Fully automatic actual-zeta fixed-anchor decay for the minimal dyadic
cover.  All layer choices and Carlson height conditions are discharged. -/
theorem exists_constants_tendsto_actualDyadicCarlsonMinimalFixedAnchorMass_zero_automatic
    {alpha : ℝ} {delta : ℕ → ℝ}
    (halpha : 0 < alpha)
    (halphaUpper : alpha ≤ 1 / 16)
    (hdeltaNonneg : ∀ m, 0 ≤ delta m)
    (hdelta : ∀ᶠ m : ℕ in atTop, 0 < delta m)
    (hdeltaUpper : ∀ᶠ m : ℕ in atTop, delta m ≤ 1 / 8)
    (hgap : IsCarlsonMovingDyadicLogPowerGap delta) :
    ∃ A C₁ C₂ : ℝ,
      0 ≤ A ∧
      1 ≤ C₁ ∧
      1 ≤ C₂ ∧
      Tendsto
        (actualDyadicCarlsonFixedAnchorMass alpha delta
          (dyadicCarlsonLayerSchedule delta))
        atTop (𝓝 0) := by
  obtain ⟨A, C₁, C₂, hA, hC₁, hC₂, htransfer⟩ :=
    exists_constants_tendsto_actualDyadicCarlsonMinimalFixedAnchorMass_zero_of_margin
      halpha halphaUpper hdeltaNonneg hdelta hdeltaUpper hgap
  refine ⟨A, C₁, C₂, hA, hC₁, hC₂, ?_⟩
  exact htransfer
    (actualDynamicDyadicCarlsonMinimalHeightConditions
      halpha halphaUpper hdeltaNonneg hdelta hdeltaUpper hgap)

end

end PrimeNumberTheorem
