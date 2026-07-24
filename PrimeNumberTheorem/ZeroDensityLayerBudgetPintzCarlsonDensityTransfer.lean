import PrimeNumberTheorem.ZeroDensityLayerBudgetPintzCarlsonAdaptiveHeight

open Filter Topology

namespace PrimeNumberTheorem

/-!
# Dynamic transfer of Carlson density counts

This module is the interface between a concrete fixed-strip zero-density
estimate and the adaptive Pintz-Carlson majorant. It assumes only the
eventual count inequality supplied by the density theorem; all dynamic
selection and finite-strip summation are proved here.
-/

/-- The actual zero-density count budget at an adaptively selected height,
weighted by the real Pintz envelope kernel. -/
noncomputable def pintzCarlsonActualDensityBudget
    {ι : Type*}
    (layers : Finset ι)
    (count : ι → ℝ → ℝ)
    (selectRate : ℝ → ℝ)
    (x : ℝ) : ℝ :=
  ∑ i ∈ layers,
    count i (pintzCarlsonHeight (selectRate x) x) *
      Real.exp (-Pintz.pintzZeroEnvelope x)

/-- Nonnegative zero counts give a nonnegative actual density budget. -/
theorem pintzCarlsonActualDensityBudget_nonneg
    {ι : Type*}
    (layers : Finset ι)
    (count : ι → ℝ → ℝ)
    (hcount : ∀ i T, 0 ≤ count i T)
    (selectRate : ℝ → ℝ)
    (x : ℝ) :
    0 ≤ pintzCarlsonActualDensityBudget
      layers count selectRate x := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg
    (hcount i (pintzCarlsonHeight (selectRate x) x))
    (Real.exp_pos _).le

/-- Stripwise Carlson count bounds imply eventual domination of the complete
actual density budget by the finite-layer Pintz-Carlson majorant. -/
theorem eventually_pintzCarlsonActualDensityBudget_le_majorant
    {ι : Type*} [DecidableEq ι]
    (layers : Finset ι)
    (count : ι → ℝ → ℝ)
    (C sigma : ι → ℝ)
    (selectRate : ℝ → ℝ)
    (hcountMajorized :
      ∀ i ∈ layers, ∀ᶠ x : ℝ in atTop,
        count i (pintzCarlsonHeight (selectRate x) x) ≤
          C i *
            pintzCarlsonHeight (selectRate x) x ^
              (4 * sigma i * (1 - sigma i)) *
            Real.log
                (pintzCarlsonHeight (selectRate x) x) ^ 4) :
    ∀ᶠ x : ℝ in atTop,
      pintzCarlsonActualDensityBudget
          layers count selectRate x ≤
        pintzCarlsonFiniteLayerBudget
          layers C sigma (selectRate x) x := by
  have hall :
      ∀ᶠ x : ℝ in atTop, ∀ i ∈ layers,
        count i (pintzCarlsonHeight (selectRate x) x) ≤
          C i *
            pintzCarlsonHeight (selectRate x) x ^
              (4 * sigma i * (1 - sigma i)) *
            Real.log
                (pintzCarlsonHeight (selectRate x) x) ^ 4 :=
    layers.eventually_all.mpr hcountMajorized
  filter_upwards [hall] with x hx
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_right
    (hx i hi)
    (Real.exp_pos _).le

/-- A single unconditional Pintz constant transfers any finite family of
Carlson-majorized zero counts, evaluated at an arbitrary admissible
finite-grid selector, to a vanishing actual density budget. -/
theorem exists_pintzConstant_adaptiveCarlsonDensityBudget_tendsto
    {ι : Type*} [DecidableEq ι]
    (layers : Finset ι)
    (count : ι → ℝ → ℝ)
    (hcount : ∀ i T, 0 ≤ count i T)
    (C sigma : ι → ℝ)
    (hC : ∀ i ∈ layers, 0 ≤ C i)
    (rates : Finset ℝ) :
    ∃ c > 0, ∀ (selectRate : ℝ → ℝ),
      (∀ x, selectRate x ∈ rates) →
      (∀ k ∈ rates, 0 < k) →
      (∀ k ∈ rates, k < 2 * Real.sqrt c) →
      (∀ i ∈ layers, ∀ᶠ x : ℝ in atTop,
        count i (pintzCarlsonHeight (selectRate x) x) ≤
          C i *
            pintzCarlsonHeight (selectRate x) x ^
              (4 * sigma i * (1 - sigma i)) *
            Real.log
                (pintzCarlsonHeight (selectRate x) x) ^ 4) →
      Tendsto
        (pintzCarlsonActualDensityBudget
          layers count selectRate)
        atTop (𝓝 0) := by
  rcases exists_pintzConstant_dominatedAdaptiveLayerBudget_tendsto
      layers C sigma hC rates with
    ⟨c, hc, hdominated⟩
  refine ⟨c, hc, ?_⟩
  intro selectRate hselect hratesPos hratesGap hcountMajorized
  exact hdominated
    selectRate
    (pintzCarlsonActualDensityBudget layers count selectRate)
    hselect
    hratesPos
    hratesGap
    (pintzCarlsonActualDensityBudget_nonneg
      layers count hcount selectRate)
    (eventually_pintzCarlsonActualDensityBudget_le_majorant
      layers count C sigma selectRate hcountMajorized)

end PrimeNumberTheorem
