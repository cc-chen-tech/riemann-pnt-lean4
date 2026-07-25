import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTLowDensityDecay

/-!
# Decay of the complete hybrid density budget

The low-threshold part is squeezed by the global `T log T` majorant.  For the
high-threshold part, thresholds outside the selected high-index finset are
temporarily filled with `3/4`; this permits reuse of the fixed-strip Carlson
transfer while leaving every selected summand unchanged.
-/

open Filter Topology

namespace PrimeNumberTheorem

theorem pintzGlobalLowDensityBudget_nonneg
    {n : ℕ} (sigma : Fin n → ℝ) (x T : ℝ) :
    0 ≤ pintzGlobalLowDensityBudget sigma x T := by
  unfold pintzGlobalLowDensityBudget
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _)
      (ExplicitFormulaAux.globalZeroMultiplicity_nonneg T))
    (Real.exp_nonneg _)

/-- The actual low-threshold budget tends to zero for any selector in a
finite admissible positive rate grid. -/
theorem exists_pintzConstant_adaptiveGlobalLowDensityBudget_tendsto
    {n : ℕ} (sigma : Fin n → ℝ) (rates : Finset ℝ) :
    ∃ c > 0, ∀ (selectRate : ℝ → ℝ),
      (∀ x, selectRate x ∈ rates) →
      (∀ k ∈ rates, 0 < k) →
      (∀ k ∈ rates, k < 2 * Real.sqrt c) →
      Tendsto
        (fun x : ℝ =>
          pintzGlobalLowDensityBudget sigma x
            (pintzCarlsonHeight (selectRate x) x))
        atTop (𝓝 0) := by
  rcases exists_globalCoefficient_lowDensityBudget_le_growthMajorant sigma with
    ⟨C, hC, hglobal⟩
  rcases
      exists_pintzConstant_adaptiveGlobalLowDensityGrowthMajorant_tendsto
        C sigma hC rates with ⟨c, hc, hgrowth⟩
  refine ⟨c, hc, ?_⟩
  intro selectRate hselect hratesPos hratesGap
  have hheight :
      Tendsto
        (fun x : ℝ => pintzCarlsonHeight (selectRate x) x)
        atTop atTop :=
    tendsto_adaptive_pintzCarlsonHeight_atTop
      rates selectRate hselect hratesPos
  have hdominated :
      ∀ᶠ x : ℝ in atTop,
        pintzGlobalLowDensityBudget sigma x
            (pintzCarlsonHeight (selectRate x) x) ≤
          pintzGlobalLowDensityGrowthMajorant C sigma x
            (pintzCarlsonHeight (selectRate x) x) := by
    filter_upwards
        [hheight.eventually (eventually_ge_atTop (4 : ℝ))] with x hx
    exact hglobal x (pintzCarlsonHeight (selectRate x) x) hx
  refine squeeze_zero' ?_ hdominated
    (hgrowth selectRate hselect hratesPos hratesGap)
  exact Filter.Eventually.of_forall fun x =>
    pintzGlobalLowDensityBudget_nonneg sigma x
      (pintzCarlsonHeight (selectRate x) x)

/-- Extend a high-strip threshold family to every index without changing any
selected high-strip threshold. -/
noncomputable def pintzCarlsonHighExtendedSigma
    {n : ℕ} (sigma : Fin n → ℝ) (i : Fin n) : ℝ :=
  if 1 / 2 < sigma i then sigma i else 3 / 4

theorem pintzCarlsonHighExtendedSigma_gt_half
    {n : ℕ} (sigma : Fin n → ℝ) (i : Fin n) :
    1 / 2 < pintzCarlsonHighExtendedSigma sigma i := by
  unfold pintzCarlsonHighExtendedSigma
  split
  · assumption
  · norm_num

theorem pintzCarlsonHighExtendedSigma_lt_one
    {n : ℕ} (sigma : Fin n → ℝ)
    (hσ1 : ∀ i ∈ pintzCarlsonHighDensityIndices sigma, sigma i < 1)
    (i : Fin n) :
    pintzCarlsonHighExtendedSigma sigma i < 1 := by
  unfold pintzCarlsonHighExtendedSigma
  split
  · rename_i hi
    exact hσ1 i (mem_pintzCarlsonHighDensityIndices.mpr hi)
  · norm_num

/-- Carlson decay for exactly the selected high-threshold indices; no
hypothesis is imposed on thresholds outside that finset. -/
theorem exists_pintzConstant_exactHeight_highDensityTerm_tendsto
    {n : ℕ} (sigma : Fin n → ℝ)
    (hσ1 : ∀ i ∈ pintzCarlsonHighDensityIndices sigma, sigma i < 1)
    (rates : Finset ℝ) :
    ∃ c > 0, ∀ (selectRate : ℝ → ℝ),
      (∀ x, selectRate x ∈ rates) →
      (∀ k ∈ rates, 0 < k) →
      (∀ k ∈ rates, k < 2 * Real.sqrt c) →
      Tendsto
        (fun x =>
          pintzCarlsonClassicalAggregatedDensityLayerTerm
            (pintzCarlsonHighDensityIndices sigma) sigma () x
              (pintzCarlsonHeight (selectRate x) x))
        atTop (𝓝 0) := by
  rcases exists_pintzConstant_exactHeight_classicalDensityTerm_tendsto
      (pintzCarlsonHighDensityIndices sigma)
      (pintzCarlsonHighExtendedSigma sigma)
      (pintzCarlsonHighExtendedSigma_gt_half sigma)
      (pintzCarlsonHighExtendedSigma_lt_one sigma hσ1)
      rates with ⟨c, hc, htransfer⟩
  refine ⟨c, hc, ?_⟩
  intro selectRate hselect hratesPos hratesGap
  have hlimit := htransfer selectRate hselect hratesPos hratesGap
  convert hlimit using 1
  funext x
  simp only [pintzCarlsonClassicalAggregatedDensityLayerTerm,
    pintzCarlsonAggregatedDensityLayerTerm]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : 1 / 2 < sigma i :=
    mem_pintzCarlsonHighDensityIndices.mp hi
  unfold pintzCarlsonHighExtendedSigma
  split
  · rfl
  · rename_i hnot
    exact (hnot hi').elim

/-- Complete low/global plus high/Carlson density decay under one common
finite-rate gap condition. -/
theorem exists_pintzConstant_adaptiveHybridDensityBudget_tendsto
    {n : ℕ} (sigma : Fin n → ℝ)
    (hσ1 : ∀ i ∈ pintzCarlsonHighDensityIndices sigma, sigma i < 1)
    (rates : Finset ℝ) :
    ∃ c > 0, ∀ (selectRate : ℝ → ℝ),
      (∀ x, selectRate x ∈ rates) →
      (∀ k ∈ rates, 0 < k) →
      (∀ k ∈ rates, k < 2 * Real.sqrt c) →
      Tendsto
        (fun x : ℝ =>
          pintzCarlsonHybridDensityBudget sigma x
            (pintzCarlsonHeight (selectRate x) x))
        atTop (𝓝 0) := by
  rcases exists_pintzConstant_adaptiveGlobalLowDensityBudget_tendsto
      sigma rates with ⟨cLow, hcLow, hLow⟩
  rcases exists_pintzConstant_exactHeight_highDensityTerm_tendsto
      sigma hσ1 rates with ⟨cHigh, hcHigh, hHigh⟩
  refine ⟨min cLow cHigh, lt_min hcLow hcHigh, ?_⟩
  intro selectRate hselect hratesPos hratesGap
  have hgapLow : ∀ k ∈ rates, k < 2 * Real.sqrt cLow := by
    intro k hk
    exact (hratesGap k hk).trans_le
      (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (min_le_left cLow cHigh)) (by norm_num))
  have hgapHigh : ∀ k ∈ rates, k < 2 * Real.sqrt cHigh := by
    intro k hk
    exact (hratesGap k hk).trans_le
      (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (min_le_right cLow cHigh)) (by norm_num))
  have hLowLimit := hLow selectRate hselect hratesPos hgapLow
  have hHighLimit := hHigh selectRate hselect hratesPos hgapHigh
  simpa only [pintzCarlsonHybridDensityBudget, zero_add] using
    hLowLimit.add hHighLimit

end PrimeNumberTheorem
