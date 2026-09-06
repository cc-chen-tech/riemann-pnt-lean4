import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTFullRelativeDecay

/-!
# Fixed two-strip dynamic density decay

The singleton zero-threshold bucket closes the PNT transfer but leaves the
Carlson high-density part empty.  This module constructs a height-independent
two-strip decomposition:

* zeros with real part at most `3/4` enter a bucket with threshold `0`;
* zeros with real part greater than `3/4` enter a bucket with threshold `3/4`.

Thus the low bucket is controlled by the global zero count while the high
bucket uses the proved Carlson density estimate.  The threshold family is
fixed as the contour height varies.
-/

open Filter Topology

namespace PrimeNumberTheorem

/-- Fixed thresholds for the low/global and high/Carlson strips. -/
noncomputable def pntTwoStripSigma (i : Fin 2) : ℝ :=
  if i = 0 then 0 else 3 / 4

/-- The height-independent two-strip classification of positive-height
nontrivial zeros. -/
noncomputable def pntTwoStripBucketInput
    (T : ℝ) : PositiveZeroBucketInput T 2 where
  bucket := fun rho =>
    if 3 / 4 < rho.re then (1 : Fin 2) else (0 : Fin 2)
  sigma := pntTwoStripSigma
  sigma_lt_re := by
    intro rho hrho
    have hre : 0 < rho.re :=
      (mem_positiveNontrivialZerosFinset.mp hrho).1.2.1
    by_cases hhigh : 3 / 4 < rho.re
    · simp [pntTwoStripSigma, hhigh]
    · simp [pntTwoStripSigma, hhigh, hre]

@[simp]
theorem pntTwoStripBucketInput_sigma
    (T : ℝ) (i : Fin 2) :
    (pntTwoStripBucketInput T).sigma i = pntTwoStripSigma i :=
  rfl

theorem pntTwoStripSigma_high_lt_one
    (i : Fin 2) (hi : i ∈ pintzCarlsonHighDensityIndices pntTwoStripSigma) :
    pntTwoStripSigma i < 1 := by
  unfold pntTwoStripSigma
  split <;> norm_num

/-- A Pintz constant chosen before the rate controls the actual global
low-density budget for every sufficiently small positive fixed rate. -/
theorem exists_pintzConstant_fixedGlobalLowDensityBudget_tendsto
    {n : ℕ} (sigma : Fin n → ℝ) :
    ∃ c > 0, ∀ rate : ℝ, 0 < rate → rate < 2 * Real.sqrt c →
      Tendsto
        (fun x : ℝ =>
          pintzGlobalLowDensityBudget sigma x
            (pintzCarlsonHeight rate x))
        atTop (nhds 0) := by
  rcases exists_globalCoefficient_lowDensityBudget_le_growthMajorant sigma with
    ⟨C, hC, hglobal⟩
  rcases exists_pintzConstant_globalLowDensityGrowthMajorant_tendsto
      C sigma hC with ⟨c, hc, hgrowth⟩
  refine ⟨c, hc, ?_⟩
  intro rate hrate hgap
  have hheight : Tendsto (pintzCarlsonHeight rate) atTop atTop :=
    tendsto_pintzCarlsonHeight_atTop hrate
  have hdominated :
      ∀ᶠ x : ℝ in atTop,
        pintzGlobalLowDensityBudget sigma x
            (pintzCarlsonHeight rate x) ≤
          pintzGlobalLowDensityGrowthMajorant C sigma x
            (pintzCarlsonHeight rate x) := by
    filter_upwards
        [hheight.eventually (eventually_ge_atTop (4 : ℝ))] with x hx
    exact hglobal x (pintzCarlsonHeight rate x) hx
  refine squeeze_zero' ?_ hdominated (hgrowth rate hrate hgap)
  exact Filter.Eventually.of_forall fun x =>
    pintzGlobalLowDensityBudget_nonneg sigma x
      (pintzCarlsonHeight rate x)

/-- Fixed-rate version of the actual classical Carlson density transfer.  The
Pintz constant is independent of the subsequently chosen rate. -/
theorem exists_pintzConstant_fixedClassicalCarlsonDensity_tendsto
    {ι : Type*} [DecidableEq ι]
    (layers : Finset ι) (sigma : ι → ℝ)
    (hσ : ∀ i, 1 / 2 < sigma i)
    (hσ1 : ∀ i, sigma i < 1) :
    ∃ c > 0, ∀ rate : ℝ, 0 < rate → rate < 2 * Real.sqrt c →
      Tendsto
        (fun x : ℝ =>
          pintzCarlsonClassicalAggregatedDensityLayerTerm
            layers sigma () x (pintzCarlsonHeight rate x))
        atTop (nhds 0) := by
  rcases exists_finiteCarlsonClassicalCoefficients
      layers sigma hσ hσ1 with ⟨C, hC, hCarlson⟩
  rcases exists_pintzConstant_finiteCarlsonMajorantAtHeight_tendsto
      layers C sigma hC with ⟨c, hc, hmajorant⟩
  refine ⟨c, hc, ?_⟩
  intro rate hrate hgap
  let selectRate : ℝ → ℝ := fun _ => rate
  have hheight :
      Tendsto
        (fun x : ℝ => pintzCarlsonHeight (selectRate x) x)
        atTop atTop := by
    simpa only [selectRate] using tendsto_pintzCarlsonHeight_atTop hrate
  have hcountMajorized :
      ∀ i ∈ layers,
        ∀ᶠ x : ℝ in atTop,
          (ZeroDensity.zeroDensityCount
              (sigma i) (pintzCarlsonHeight (selectRate x) x) : ℝ) ≤
            C i *
              pintzCarlsonHeight (selectRate x) x ^
                (4 * sigma i * (1 - sigma i)) *
              Real.log
                (pintzCarlsonHeight (selectRate x) x) ^ 4 := by
    intro i hi
    exact hheight.eventually (hCarlson i hi)
  have hdominated :=
    eventually_pintzCarlsonActualDensityBudget_le_majorant
      layers
      (fun i T => (ZeroDensity.zeroDensityCount (sigma i) T : ℝ))
      C sigma selectRate hcountMajorized
  have hactual :
      Tendsto
        (pintzCarlsonActualDensityBudget
          layers
          (fun i T => (ZeroDensity.zeroDensityCount (sigma i) T : ℝ))
          selectRate)
        atTop (nhds 0) := by
    refine squeeze_zero' ?_ hdominated ?_
    · exact Filter.Eventually.of_forall fun x =>
        pintzCarlsonActualDensityBudget_nonneg
          layers
          (fun i T => (ZeroDensity.zeroDensityCount (sigma i) T : ℝ))
          (fun i T => Nat.cast_nonneg _)
          selectRate x
    · simpa only [selectRate, pintzCarlsonFiniteLayerBudget] using
        hmajorant rate hrate hgap
  change Tendsto
    (pintzCarlsonActualDensityBudget
      layers
      (fun i T => (ZeroDensity.zeroDensityCount (sigma i) T : ℝ))
      selectRate)
    atTop (nhds 0)
  exact hactual

/-- Carlson decay for exactly the high indices of a fixed threshold family,
with one Pintz constant valid for every sufficiently small fixed rate. -/
theorem exists_pintzConstant_fixedExactHeight_highDensityTerm_tendsto
    {n : ℕ} (sigma : Fin n → ℝ)
    (hσ1 : ∀ i ∈ pintzCarlsonHighDensityIndices sigma, sigma i < 1) :
    ∃ c > 0, ∀ rate : ℝ, 0 < rate → rate < 2 * Real.sqrt c →
      Tendsto
        (fun x : ℝ =>
          pintzCarlsonClassicalAggregatedDensityLayerTerm
            (pintzCarlsonHighDensityIndices sigma) sigma () x
              (pintzCarlsonHeight rate x))
        atTop (nhds 0) := by
  rcases exists_pintzConstant_fixedClassicalCarlsonDensity_tendsto
      (pintzCarlsonHighDensityIndices sigma)
      (pintzCarlsonHighExtendedSigma sigma)
      (pintzCarlsonHighExtendedSigma_gt_half sigma)
      (pintzCarlsonHighExtendedSigma_lt_one sigma hσ1) with
    ⟨c, hc, htransfer⟩
  refine ⟨c, hc, ?_⟩
  intro rate hrate hgap
  have hlimit := htransfer rate hrate hgap
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

/-- Complete fixed-threshold low/global plus high/Carlson density decay.  The
common Pintz constant is selected before the positive fixed rate. -/
theorem exists_pintzConstant_fixedHybridDensityBudget_tendsto
    {n : ℕ} (sigma : Fin n → ℝ)
    (hσ1 : ∀ i ∈ pintzCarlsonHighDensityIndices sigma, sigma i < 1) :
    ∃ c > 0, ∀ rate : ℝ, 0 < rate → rate < 2 * Real.sqrt c →
      Tendsto
        (fun x : ℝ =>
          pintzCarlsonHybridDensityBudget sigma x
            (pintzCarlsonHeight rate x))
        atTop (nhds 0) := by
  rcases exists_pintzConstant_fixedGlobalLowDensityBudget_tendsto sigma with
    ⟨cLow, hcLow, hLow⟩
  rcases exists_pintzConstant_fixedExactHeight_highDensityTerm_tendsto
      sigma hσ1 with ⟨cHigh, hcHigh, hHigh⟩
  refine ⟨min cLow cHigh, lt_min hcLow hcHigh, ?_⟩
  intro rate hrate hgap
  have hgapLow : rate < 2 * Real.sqrt cLow :=
    hgap.trans_le
      (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (min_le_left cLow cHigh)) (by norm_num))
  have hgapHigh : rate < 2 * Real.sqrt cHigh :=
    hgap.trans_le
      (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (min_le_right cLow cHigh)) (by norm_num))
  have hLowLimit := hLow rate hrate hgapLow
  have hHighLimit := hHigh rate hrate hgapHigh
  simpa only [pintzCarlsonHybridDensityBudget, zero_add] using
    hLowLimit.add hHighLimit

/-- The concrete two-strip dynamic density budget decays at every sufficiently
small positive fixed rate, and its high strip is the genuine `sigma = 3/4`
Carlson count. -/
theorem exists_pintzConstant_pntTwoStripHybridDensityBudget_tendsto :
    ∃ c > 0, ∀ rate : ℝ, 0 < rate → rate < 2 * Real.sqrt c →
      Tendsto
        (fun x : ℝ =>
          pintzCarlsonHybridDensityBudget pntTwoStripSigma x
            (pintzCarlsonHeight rate x))
        atTop (nhds 0) :=
  exists_pintzConstant_fixedHybridDensityBudget_tendsto
    pntTwoStripSigma pntTwoStripSigma_high_lt_one

end PrimeNumberTheorem
