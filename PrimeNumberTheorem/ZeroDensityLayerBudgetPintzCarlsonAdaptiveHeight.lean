import PrimeNumberTheorem.ZeroDensityLayerBudgetPintzCarlsonHeight

open Filter Topology

namespace PrimeNumberTheorem

/-!
# Adaptive finite-grid Pintz-Carlson heights

An optimizer may switch between finitely many height rates as `x` changes.
Pointwise convergence for each fixed rate does not by itself justify such a
switch. This module proves the needed finite-uniform transfer.
-/

/-- The full Pintz-weighted Carlson majorant summed over a finite family of
real-part strips at height rate `k`. -/
noncomputable def pintzCarlsonFiniteLayerBudget
    {ι : Type*}
    (layers : Finset ι)
    (C sigma : ι → ℝ)
    (k x : ℝ) : ℝ :=
  ∑ i ∈ layers,
    C i *
      pintzCarlsonHeight k x ^ (4 * sigma i * (1 - sigma i)) *
      Real.log (pintzCarlsonHeight k x) ^ 4 *
      Real.exp (-Pintz.pintzZeroEnvelope x)

/-- Nonnegative strip coefficients make the finite layer budget
nonnegative, independently of the selected height rate. -/
theorem pintzCarlsonFiniteLayerBudget_nonneg
    {ι : Type*}
    (layers : Finset ι)
    (C sigma : ι → ℝ)
    (hC : ∀ i ∈ layers, 0 ≤ C i)
    (k x : ℝ) :
    0 ≤ pintzCarlsonFiniteLayerBudget layers C sigma k x := by
  apply Finset.sum_nonneg
  intro i hi
  have hheight :
      0 ≤ pintzCarlsonHeight k x ^ (4 * sigma i * (1 - sigma i)) :=
    Real.rpow_nonneg _ _
  have hlogFourth :
      0 ≤ Real.log (pintzCarlsonHeight k x) ^ 4 := by
    positivity
  have hexp : 0 ≤ Real.exp (-Pintz.pintzZeroEnvelope x) :=
    (Real.exp_pos _).le
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (hC i hi) hheight)
      hlogFourth)
    hexp

/-- A single Pintz constant controls any selector that switches arbitrarily
among finitely many admissible rates. The proof gives finite-uniform decay by
dominating the selected budget with the sum of all candidate budgets. -/
theorem exists_pintzConstant_adaptiveFiniteHeightBudget_tendsto
    {ι : Type*} [DecidableEq ι]
    (layers : Finset ι)
    (C sigma : ι → ℝ)
    (hC : ∀ i ∈ layers, 0 ≤ C i)
    (rates : Finset ℝ) :
    ∃ c > 0, ∀ (selectRate : ℝ → ℝ),
      (∀ x, selectRate x ∈ rates) →
      (∀ k ∈ rates, 0 < k) →
      (∀ k ∈ rates, k < 2 * Real.sqrt c) →
      Tendsto
        (fun x : ℝ =>
          pintzCarlsonFiniteLayerBudget
            layers C sigma (selectRate x) x)
        atTop (𝓝 0) := by
  rcases exists_pintzConstant_finiteCarlsonMajorantAtHeight_tendsto
      layers C sigma hC with
    ⟨c, hc, hfixed⟩
  refine ⟨c, hc, ?_⟩
  intro selectRate hselect hratesPos hratesGap
  have hupper :
      Tendsto
        (fun x : ℝ =>
          ∑ k ∈ rates,
            pintzCarlsonFiniteLayerBudget layers C sigma k x)
        atTop (𝓝 0) := by
    apply tendsto_finset_sum
    intro k hk
    exact hfixed k (hratesPos k hk) (hratesGap k hk)
  refine squeeze_zero' ?_ ?_ hupper
  · exact Filter.Eventually.of_forall fun x =>
      pintzCarlsonFiniteLayerBudget_nonneg
        layers C sigma hC (selectRate x) x
  · exact Filter.Eventually.of_forall fun x =>
      Finset.single_le_sum
        (fun k hk =>
          pintzCarlsonFiniteLayerBudget_nonneg
            layers C sigma hC k x)
        (hselect x)

end PrimeNumberTheorem
