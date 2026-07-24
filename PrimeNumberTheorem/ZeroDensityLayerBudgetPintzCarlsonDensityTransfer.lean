import PrimeNumberTheorem.ZeroDensityLayerBudgetPintzCarlsonAdaptiveHeight
import PrimeNumberTheorem.CarlsonAsymptotic

open Filter Topology

namespace PrimeNumberTheorem

/-!
# Dynamic transfer of Carlson density counts

This module is the interface between a concrete fixed-strip zero-density
estimate and the adaptive Pintz-Carlson majorant. It assumes only the
eventual count inequality supplied by the density theorem; all dynamic
selection and finite-strip summation are proved here.
-/

/-- Carlson's proved Big-O theorem yields a nonnegative coefficient and an
eventual pointwise classical density majorant. -/
theorem exists_carlsonClassicalCoefficient_eventually_count_le
    {sigma : ℝ}
    (hσ : 1 / 2 < sigma)
    (hσ1 : sigma < 1) :
    ∃ C ≥ 0, ∀ᶠ T : ℝ in atTop,
      (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
        C * T ^ (4 * sigma * (1 - sigma)) *
          Real.log T ^ 4 := by
  rcases
      (CarlsonZeroDensity.carlson_zeroDensity_isBigO
        hσ hσ1).exists_nonneg with
    ⟨C, hC, hbigO⟩
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbigO.bound] with T hT
  have hcount :
      0 ≤ (ZeroDensity.zeroDensityCount sigma T : ℝ) :=
    Nat.cast_nonneg _
  have hmajorant :
      0 ≤ T ^ (4 * sigma * (1 - sigma)) *
        Real.log T ^ 4 :=
    mul_nonneg (Real.rpow_nonneg _ _) (by positivity)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hcount,
      abs_of_nonneg hmajorant, mul_assoc] using hT

/-- For finitely many fixed real-part strips, Carlson coefficients can be
chosen once and their count bounds pulled back along any dynamic height
tending to infinity. -/
theorem exists_finiteCarlsonCoefficients_along_dynamicHeight
    {ι : Type*}
    (layers : Finset ι)
    (sigma : ι → ℝ)
    (hσ : ∀ i, 1 / 2 < sigma i)
    (hσ1 : ∀ i, sigma i < 1)
    (height : ℝ → ℝ)
    (hheight : Tendsto height atTop atTop) :
    ∃ C : ι → ℝ,
      (∀ i ∈ layers, 0 ≤ C i) ∧
      (∀ i ∈ layers, ∀ᶠ x : ℝ in atTop,
        (ZeroDensity.zeroDensityCount (sigma i) (height x) : ℝ) ≤
          C i * height x ^ (4 * sigma i * (1 - sigma i)) *
            Real.log (height x) ^ 4) := by
  classical
  have hcertificate :
      ∀ i, ∃ C ≥ 0, ∀ᶠ T : ℝ in atTop,
        (ZeroDensity.zeroDensityCount (sigma i) T : ℝ) ≤
          C * T ^ (4 * sigma i * (1 - sigma i)) *
            Real.log T ^ 4 :=
    fun i =>
      exists_carlsonClassicalCoefficient_eventually_count_le
        (hσ i) (hσ1 i)
  choose C hC using hcertificate
  refine ⟨C, ?_, ?_⟩
  · intro i hi
    exact (hC i).1
  · intro i hi
    exact hheight.eventually (hC i).2

/-- Carlson coefficients for a finite strip family can be fixed before any
dynamic height selector is chosen. -/
theorem exists_finiteCarlsonClassicalCoefficients
    {ι : Type*}
    (layers : Finset ι)
    (sigma : ι → ℝ)
    (hσ : ∀ i, 1 / 2 < sigma i)
    (hσ1 : ∀ i, sigma i < 1) :
    ∃ C : ι → ℝ,
      (∀ i ∈ layers, 0 ≤ C i) ∧
      (∀ i ∈ layers, ∀ᶠ T : ℝ in atTop,
        (ZeroDensity.zeroDensityCount (sigma i) T : ℝ) ≤
          C i * T ^ (4 * sigma i * (1 - sigma i)) *
            Real.log T ^ 4) := by
  classical
  have hcertificate :
      ∀ i, ∃ C ≥ 0, ∀ᶠ T : ℝ in atTop,
        (ZeroDensity.zeroDensityCount (sigma i) T : ℝ) ≤
          C * T ^ (4 * sigma i * (1 - sigma i)) *
            Real.log T ^ 4 :=
    fun i =>
      exists_carlsonClassicalCoefficient_eventually_count_le
        (hσ i) (hσ1 i)
  choose C hC using hcertificate
  exact ⟨C, fun i hi => (hC i).1, fun i hi => (hC i).2⟩

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

/-- Concrete dynamic Pintz-Carlson density transfer. For finitely many fixed
strips in the Carlson range and any adaptive selector from a finite admissible
rate grid, the actual multiplicity-counted zero-density budget weighted by the
proved Pintz envelope tends to zero. No abstract density majorization remains
in the conclusion. -/
theorem exists_pintzConstant_adaptiveClassicalCarlsonDensity_tendsto
    {ι : Type*} [DecidableEq ι]
    (layers : Finset ι)
    (sigma : ι → ℝ)
    (hσ : ∀ i, 1 / 2 < sigma i)
    (hσ1 : ∀ i, sigma i < 1)
    (rates : Finset ℝ) :
    ∃ c > 0, ∀ (selectRate : ℝ → ℝ),
      (∀ x, selectRate x ∈ rates) →
      (∀ k ∈ rates, 0 < k) →
      (∀ k ∈ rates, k < 2 * Real.sqrt c) →
      Tendsto
        (pintzCarlsonActualDensityBudget
          layers
          (fun i T =>
            (ZeroDensity.zeroDensityCount (sigma i) T : ℝ))
          selectRate)
        atTop (𝓝 0) := by
  rcases exists_finiteCarlsonClassicalCoefficients
      layers sigma hσ hσ1 with
    ⟨C, hC, hCarlson⟩
  rcases exists_pintzConstant_adaptiveCarlsonDensityBudget_tendsto
      layers
      (fun i T =>
        (ZeroDensity.zeroDensityCount (sigma i) T : ℝ))
      (fun i T => Nat.cast_nonneg _)
      C sigma hC rates with
    ⟨c, hc, htransfer⟩
  refine ⟨c, hc, ?_⟩
  intro selectRate hselect hratesPos hratesGap
  have hheight :
      Tendsto
        (fun x : ℝ =>
          pintzCarlsonHeight (selectRate x) x)
        atTop atTop :=
    tendsto_adaptive_pintzCarlsonHeight_atTop
      rates selectRate hselect hratesPos
  apply htransfer selectRate hselect hratesPos hratesGap
  intro i hi
  exact hheight.eventually (hCarlson i hi)

end PrimeNumberTheorem
