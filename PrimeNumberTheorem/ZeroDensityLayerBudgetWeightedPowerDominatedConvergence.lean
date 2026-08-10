import PrimeNumberTheorem.ZeroDensityLayerBudgetMovingGapBarrier

/-!
# Weighted power layers by dominated convergence

If the explicit-formula weights of a zero family are summable, then no
uniform real-part gap below the target exponent is needed. Pointwise strict
separation `sigma i < beta` makes each normalized power tend to zero, while
summability supplies a common majorant.

This is the abstract transfer interface needed to retain the `1 / |rho|`
factor instead of replacing it by one uniform denominator guard before
applying zero density.
-/

open Filter Topology

namespace PrimeNumberTheorem

/--
A summable nonnegative weighted family of power layers strictly to the left
of `beta` is negligible on the target `beta`-power scale.

Unlike finite-strip worst-case aggregation, this theorem requires no
uniform positive lower bound on `beta - sigma i`.
-/
theorem weightedPowerLayers_tendsto_zero_of_summable
    {ι : Type*}
    {beta : ℝ}
    {weight sigma : ι → ℝ}
    (hweight : Summable weight)
    (hweightNonneg : ∀ i, 0 ≤ weight i)
    (hsigma : ∀ i, sigma i < beta) :
    Tendsto
      (fun m : ℕ =>
        ∑' i : ι,
          weight i * pntPowerLayerToTargetRatio beta (sigma i) m)
      atTop (𝓝 0) := by
  have hpoint :
      ∀ i : ι,
        Tendsto
          (fun m : ℕ =>
            weight i *
              pntPowerLayerToTargetRatio beta (sigma i) m)
          atTop (𝓝 0) := by
    intro i
    simpa using
      (pntPowerLayerToTargetRatio_tendsto_zero_of_lt
        (hsigma i)).const_mul (weight i)
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
        (sub_nonpos.mpr (hsigma i).le) hlog
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
  simpa only [tsum_zero] using
    tendsto_tsum_of_dominated_convergence hweight hpoint hbound

/-- Complex-valued coefficients are handled by summability of their norms;
the normalized sum of norms still tends to zero. -/
theorem weightedComplexPowerLayerNorms_tendsto_zero_of_summable
    {ι : Type*}
    {beta : ℝ}
    {coefficient : ι → ℂ}
    {sigma : ι → ℝ}
    (hcoefficient : Summable fun i => ‖coefficient i‖)
    (hsigma : ∀ i, sigma i < beta) :
    Tendsto
      (fun m : ℕ =>
        ∑' i : ι,
          ‖coefficient i‖ *
            pntPowerLayerToTargetRatio beta (sigma i) m)
      atTop (𝓝 0) := by
  exact weightedPowerLayers_tendsto_zero_of_summable
    hcoefficient (fun i => norm_nonneg _) hsigma

end PrimeNumberTheorem
