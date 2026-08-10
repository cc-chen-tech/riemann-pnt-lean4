import PrimeNumberTheorem.ZeroDensityLayerBudgetWeightedPowerDominatedConvergence

/-!
# Weighted power layers with a boundary mass

Pointwise strict separation from the target exponent makes every summand
decay.  If one weakens this to `sigma i <= beta`, Tannery's theorem still
identifies the exact limit: only indices on the boundary `sigma i = beta`
survive.

This is the quantitative interface needed to retain a summable rightmost
zero layer instead of incorrectly treating it as target-negligible.
-/

open Filter Topology

namespace PrimeNumberTheorem

/-- Summable coefficient mass lying exactly on the target exponent. -/
noncomputable def weightedPowerBoundaryMass
    {ι : Type*} (beta : ℝ) (weight sigma : ι → ℝ) : ℝ :=
  ∑' i : ι, if sigma i = beta then weight i else 0

/-- A summable nonnegative weighted family supported in `sigma <= beta`
converges, on the target scale, to precisely its boundary coefficient mass. -/
theorem weightedPowerLayers_tendsto_boundaryMass_of_summable
    {ι : Type*}
    {beta : ℝ}
    {weight sigma : ι → ℝ}
    (hweight : Summable weight)
    (hweightNonneg : ∀ i, 0 ≤ weight i)
    (hsigma : ∀ i, sigma i ≤ beta) :
    Tendsto
      (fun m : ℕ =>
        ∑' i : ι,
          weight i * pntPowerLayerToTargetRatio beta (sigma i) m)
      atTop
      (𝓝 (weightedPowerBoundaryMass beta weight sigma)) := by
  have hpoint :
      ∀ i : ι,
        Tendsto
          (fun m : ℕ =>
            weight i *
              pntPowerLayerToTargetRatio beta (sigma i) m)
          atTop
          (𝓝 (if sigma i = beta then weight i else 0)) := by
    intro i
    by_cases heq : sigma i = beta
    · simpa [heq, pntPowerLayerToTargetRatio] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => weight i) atTop (𝓝 (weight i)))
    · have hlt : sigma i < beta := lt_of_le_of_ne (hsigma i) heq
      simpa [heq] using
        (pntPowerLayerToTargetRatio_tendsto_zero_of_lt hlt).const_mul
          (weight i)
  have hbound :
      ∀ᶠ m in atTop,
        ∀ i : ι,
          ‖weight i *
              pntPowerLayerToTargetRatio beta (sigma i) m‖ ≤
            weight i := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm i
    have hlog : 0 ≤ Real.log (m : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hm)
    have hexponent :
        (sigma i - beta) * Real.log (m : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (hsigma i)) hlog
    have hratio :
        pntPowerLayerToTargetRatio beta (sigma i) m ≤ 1 := by
      unfold pntPowerLayerToTargetRatio
      exact Real.exp_le_one_iff.mpr hexponent
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (hweightNonneg i)]
    have hratioPos :
        0 ≤ pntPowerLayerToTargetRatio beta (sigma i) m :=
      (Real.exp_pos _).le
    rw [abs_of_nonneg hratioPos]
    simpa using
      mul_le_mul_of_nonneg_left hratio (hweightNonneg i)
  simpa [weightedPowerBoundaryMass] using
    tendsto_tsum_of_dominated_convergence hweight hpoint hbound

/-- The strict-gap dominated-convergence theorem is the zero-boundary-mass
special case of the boundary limit. -/
theorem weightedPowerBoundaryMass_eq_zero_of_lt
    {ι : Type*}
    {beta : ℝ}
    {weight sigma : ι → ℝ}
    (hsigma : ∀ i, sigma i < beta) :
    weightedPowerBoundaryMass beta weight sigma = 0 := by
  unfold weightedPowerBoundaryMass
  simp [fun i => ne_of_lt (hsigma i)]

end PrimeNumberTheorem
