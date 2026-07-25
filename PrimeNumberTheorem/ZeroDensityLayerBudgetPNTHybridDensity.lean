import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTGoodHeightCarlsonCeiling

/-!
# Hybrid low-real-part and Carlson density budgets

Carlson's classical theorem applies only to thresholds strictly between
`1 / 2` and `1`.  A positive-zero bucket family covering every nontrivial zero
may also contain thresholds at or below `1 / 2`.  This module separates those
indices automatically:

* low-threshold layers are bounded by the global multiplicity estimate
  `O(T log T)`;
* high-threshold layers retain the actual multiplicity-weighted Carlson count.

Thus no Carlson estimate is used outside its proved strip.
-/

open Filter Topology
open scoped BigOperators

namespace PrimeNumberTheorem

/-- Bucket indices whose lower real-part threshold is outside the strict
Carlson range on the left. -/
noncomputable def pintzCarlsonLowDensityIndices
    {n : ℕ} (sigma : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun i => sigma i ≤ 1 / 2

/-- Bucket indices whose lower real-part threshold lies to the right of the
critical line.  An additional upper hypothesis `sigma i < 1` is required
before applying Carlson. -/
noncomputable def pintzCarlsonHighDensityIndices
    {n : ℕ} (sigma : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun i => 1 / 2 < sigma i

theorem mem_pintzCarlsonLowDensityIndices
    {n : ℕ} {sigma : Fin n → ℝ} {i : Fin n} :
    i ∈ pintzCarlsonLowDensityIndices sigma ↔ sigma i ≤ 1 / 2 := by
  simp only [pintzCarlsonLowDensityIndices, Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem mem_pintzCarlsonHighDensityIndices
    {n : ℕ} {sigma : Fin n → ℝ} {i : Fin n} :
    i ∈ pintzCarlsonHighDensityIndices sigma ↔ 1 / 2 < sigma i := by
  simp only [pintzCarlsonHighDensityIndices, Finset.mem_filter,
    Finset.mem_univ, true_and]

/-- Contribution assigned to all low-threshold layers, bounded by total
nontrivial-zero multiplicity. -/
noncomputable def pintzGlobalLowDensityBudget
    {n : ℕ} (sigma : Fin n → ℝ) (x T : ℝ) : ℝ :=
  ((pintzCarlsonLowDensityIndices sigma).card : ℝ) *
    ExplicitFormulaAux.globalZeroMultiplicity T *
    Real.exp (-Pintz.pintzZeroEnvelope x)

/-- Complete density budget: global counting for low thresholds and actual
Carlson counts for high thresholds. -/
noncomputable def pintzCarlsonHybridDensityBudget
    {n : ℕ} (sigma : Fin n → ℝ) (x T : ℝ) : ℝ :=
  pintzGlobalLowDensityBudget sigma x T +
    pintzCarlsonClassicalAggregatedDensityLayerTerm
      (pintzCarlsonHighDensityIndices sigma) sigma () x T

/-- Every multiplicity-weighted density layer is covered by the hybrid
low/global plus high/Carlson budget. -/
theorem pintzCarlsonClassicalAggregatedDensityLayerTerm_le_hybrid
    {n : ℕ} (sigma : Fin n → ℝ) (x T : ℝ) :
    pintzCarlsonClassicalAggregatedDensityLayerTerm
        (Finset.univ : Finset (Fin n)) sigma () x T ≤
      pintzCarlsonHybridDensityBudget sigma x T := by
  classical
  let f : Fin n → ℝ := fun i =>
    (ZeroDensity.zeroDensityCount (sigma i) T : ℝ) *
      Real.exp (-Pintz.pintzZeroEnvelope x)
  have hsplit :
      (∑ i : Fin n, f i) =
        (∑ i ∈ pintzCarlsonLowDensityIndices sigma, f i) +
          ∑ i ∈ pintzCarlsonHighDensityIndices sigma, f i := by
    simpa only [pintzCarlsonLowDensityIndices,
      pintzCarlsonHighDensityIndices, Finset.sum_filter, not_le] using
      (Finset.sum_filter_add_sum_filter_not
        (Finset.univ : Finset (Fin n))
        (fun i => sigma i ≤ 1 / 2) f).symm
  have hlow :
      (∑ i ∈ pintzCarlsonLowDensityIndices sigma, f i) ≤
        ((pintzCarlsonLowDensityIndices sigma).card : ℝ) *
          ExplicitFormulaAux.globalZeroMultiplicity T *
          Real.exp (-Pintz.pintzZeroEnvelope x) := by
    calc
      (∑ i ∈ pintzCarlsonLowDensityIndices sigma, f i) ≤
          ∑ _i ∈ pintzCarlsonLowDensityIndices sigma,
            ExplicitFormulaAux.globalZeroMultiplicity T *
              Real.exp (-Pintz.pintzZeroEnvelope x) := by
        apply Finset.sum_le_sum
        intro i hi
        dsimp [f]
        exact mul_le_mul_of_nonneg_right
          (ZeroDensity.zeroDensityCount_le_globalZeroMultiplicity
            (sigma i) T)
          (Real.exp_nonneg _)
      _ = ((pintzCarlsonLowDensityIndices sigma).card : ℝ) *
          ExplicitFormulaAux.globalZeroMultiplicity T *
          Real.exp (-Pintz.pintzZeroEnvelope x) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
  calc
    pintzCarlsonClassicalAggregatedDensityLayerTerm
        (Finset.univ : Finset (Fin n)) sigma () x T =
        (∑ i : Fin n, f i) := by
      rfl
    _ = (∑ i ∈ pintzCarlsonLowDensityIndices sigma, f i) +
          ∑ i ∈ pintzCarlsonHighDensityIndices sigma, f i := hsplit
    _ ≤ ((pintzCarlsonLowDensityIndices sigma).card : ℝ) *
          ExplicitFormulaAux.globalZeroMultiplicity T *
          Real.exp (-Pintz.pintzZeroEnvelope x) +
        ∑ i ∈ pintzCarlsonHighDensityIndices sigma, f i :=
      add_le_add hlow le_rfl
    _ = pintzCarlsonHybridDensityBudget sigma x T := by
      rfl

/-- Explicit `T log T` majorant for the low-threshold part of the hybrid
budget. -/
noncomputable def pintzGlobalLowDensityGrowthMajorant
    {n : ℕ} (C : ℝ) (sigma : Fin n → ℝ) (x T : ℝ) : ℝ :=
  ((pintzCarlsonLowDensityIndices sigma).card : ℝ) *
    (C * T * (1 + Real.log (T + 6))) *
    Real.exp (-Pintz.pintzZeroEnvelope x)

theorem exists_globalCoefficient_lowDensityBudget_le_growthMajorant
    {n : ℕ} (sigma : Fin n → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (x T : ℝ), 4 ≤ T →
        pintzGlobalLowDensityBudget sigma x T ≤
          pintzGlobalLowDensityGrowthMajorant C sigma x T := by
  rcases ExplicitFormulaAux.exists_globalZeroMultiplicity_le_mul_log with
    ⟨C, hC, hglobal⟩
  refine ⟨C, hC, ?_⟩
  intro x T hT
  dsimp [pintzGlobalLowDensityBudget,
    pintzGlobalLowDensityGrowthMajorant]
  gcongr
  exact hglobal T hT

theorem pintzCarlsonHybridDensityBudget_nonneg
    {n : ℕ} (sigma : Fin n → ℝ) (x T : ℝ) :
    0 ≤ pintzCarlsonHybridDensityBudget sigma x T := by
  apply add_nonneg
  · exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _)
        (ExplicitFormulaAux.globalZeroMultiplicity_nonneg T))
      (Real.exp_nonneg _)
  · exact pintzCarlsonClassicalAggregatedDensityLayerTerm_nonneg
      (pintzCarlsonHighDensityIndices sigma) sigma x T

end PrimeNumberTheorem
