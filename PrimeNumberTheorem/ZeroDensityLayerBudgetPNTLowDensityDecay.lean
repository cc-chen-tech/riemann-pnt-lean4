import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTHybridDensity

/-!
# Decay of the global low-threshold density contribution

The global zero count contributes `T * (1 + log (T + 6))`.  At the adaptive
Pintz--Carlson height this has the same exponential power as the endpoint
Carlson model `sigma = 1/2`, up to a harmless fourth logarithmic power.  This
module proves that comparison and obtains decay for fixed rates and selectors
from a finite positive rate grid.
-/

open Filter Topology

namespace PrimeNumberTheorem

/-- Eventually the logarithm in the global zero-count bound is absorbed by
four powers of the logarithm of the Pintz--Carlson height. -/
theorem eventually_one_add_log_height_add_six_le_four_mul_log_pow_four
    {k : ℝ} (hk : 0 < k) :
    ∀ᶠ x : ℝ in atTop,
      1 + Real.log (pintzCarlsonHeight k x + 6) ≤
        4 * Real.log (pintzCarlsonHeight k x) ^ 4 := by
  have hheight := tendsto_pintzCarlsonHeight_atTop hk
  filter_upwards
      [hheight.eventually
        (eventually_ge_atTop (max (Real.exp 2) 6))] with x hx
  let H := pintzCarlsonHeight k x
  have hHexp : Real.exp 2 ≤ H := (le_max_left _ _).trans hx
  have hH6 : 6 ≤ H := (le_max_right _ _).trans hx
  have hHpos : 0 < H := by linarith
  have hlogH2 : 2 ≤ Real.log H :=
    (Real.le_log_iff_exp_le hHpos).mpr hHexp
  have hlog2_le_logH : Real.log 2 ≤ Real.log H :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlogadd :
      Real.log (H + 6) ≤ Real.log (2 * H) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlogmul : Real.log (2 * H) = Real.log 2 + Real.log H := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hHpos)]
  have hlogadd_le : Real.log (H + 6) ≤ 2 * Real.log H := by
    rw [hlogmul] at hlogadd
    linarith
  have hlogH0 : 0 ≤ Real.log H := by linarith
  have hlogH_le_sq : Real.log H ≤ Real.log H ^ 2 := by
    nlinarith [sq_nonneg (Real.log H - 1)]
  have hsq_le_fourth : Real.log H ^ 2 ≤ Real.log H ^ 4 := by
    nlinarith [sq_nonneg (Real.log H ^ 2 - Real.log H)]
  change 1 + Real.log (H + 6) ≤ 4 * Real.log H ^ 4
  calc
    1 + Real.log (H + 6) ≤ 1 + 2 * Real.log H := by linarith
    _ ≤ 3 * Real.log H ^ 2 := by
      nlinarith [sq_nonneg (Real.log H - 1)]
    _ ≤ 4 * Real.log H ^ 4 := by
      nlinarith [sq_nonneg (Real.log H ^ 2)]

/-- Nonnegativity of the explicit global low-density growth majorant at a
nonnegative height. -/
theorem pintzGlobalLowDensityGrowthMajorant_nonneg
    {n : ℕ} {C x T : ℝ} (sigma : Fin n → ℝ)
    (hC : 0 ≤ C) (hT : 0 ≤ T) :
    0 ≤ pintzGlobalLowDensityGrowthMajorant C sigma x T := by
  have hlog : 0 ≤ 1 + Real.log (T + 6) := by
    have : 0 ≤ Real.log (T + 6) :=
      Real.log_nonneg (by linarith)
    linarith
  unfold pintzGlobalLowDensityGrowthMajorant
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (mul_nonneg hC hT) hlog))
    (Real.exp_nonneg _)

/-- The explicit global-count growth majorant tends to zero at every
admissible fixed Pintz--Carlson rate. -/
theorem exists_pintzConstant_globalLowDensityGrowthMajorant_tendsto
    {n : ℕ} (C : ℝ) (sigma : Fin n → ℝ) (hC : 0 ≤ C) :
    ∃ c > 0, ∀ k : ℝ, 0 < k → k < 2 * Real.sqrt c →
      Tendsto
        (fun x : ℝ =>
          pintzGlobalLowDensityGrowthMajorant C sigma x
            (pintzCarlsonHeight k x))
        atTop (𝓝 0) := by
  rcases exists_pintzConstant_carlsonMajorantAtHeight_tendsto with
    ⟨c, hc, hmajorant⟩
  refine ⟨c, hc, ?_⟩
  intro k hk hgap
  let coefficient : ℝ :=
    4 * ((pintzCarlsonLowDensityIndices sigma).card : ℝ) * C
  have hcoefficient : 0 ≤ coefficient := by
    dsimp [coefficient]
    positivity
  have hproxy :=
    hmajorant coefficient (1 / 2) k hcoefficient hk hgap
  refine squeeze_zero' ?_ ?_ hproxy
  · exact Filter.Eventually.of_forall fun x => by
      exact pintzGlobalLowDensityGrowthMajorant_nonneg sigma hC
        (pintzCarlsonHeight_pos k x).le
  · filter_upwards
        [eventually_one_add_log_height_add_six_le_four_mul_log_pow_four hk]
        with x hx
    have hheight : 0 ≤ pintzCarlsonHeight k x :=
      (pintzCarlsonHeight_pos k x).le
    have hcard :
        0 ≤ ((pintzCarlsonLowDensityIndices sigma).card : ℝ) :=
      Nat.cast_nonneg _
    have hexp : 0 ≤ Real.exp (-Pintz.pintzZeroEnvelope x) :=
      (Real.exp_pos _).le
    dsimp [pintzGlobalLowDensityGrowthMajorant, coefficient]
    calc
      ((pintzCarlsonLowDensityIndices sigma).card : ℝ) *
              (C * pintzCarlsonHeight k x *
                (1 + Real.log (pintzCarlsonHeight k x + 6))) *
            Real.exp (-Pintz.pintzZeroEnvelope x) ≤
          ((pintzCarlsonLowDensityIndices sigma).card : ℝ) *
              (C * pintzCarlsonHeight k x *
                (4 * Real.log (pintzCarlsonHeight k x) ^ 4)) *
            Real.exp (-Pintz.pintzZeroEnvelope x) := by
        gcongr
      _ =
          (4 * ((pintzCarlsonLowDensityIndices sigma).card : ℝ) * C) *
              pintzCarlsonHeight k x ^
                (4 * (1 / 2 : ℝ) * (1 - 1 / 2)) *
              Real.log (pintzCarlsonHeight k x) ^ 4 *
              Real.exp (-Pintz.pintzZeroEnvelope x) := by
        norm_num
        ring

/-- A selector ranging over finitely many positive admissible rates preserves
decay of the global low-density growth majorant. -/
theorem exists_pintzConstant_adaptiveGlobalLowDensityGrowthMajorant_tendsto
    {n : ℕ} (C : ℝ) (sigma : Fin n → ℝ) (hC : 0 ≤ C)
    (rates : Finset ℝ) :
    ∃ c > 0, ∀ (selectRate : ℝ → ℝ),
      (∀ x, selectRate x ∈ rates) →
      (∀ k ∈ rates, 0 < k) →
      (∀ k ∈ rates, k < 2 * Real.sqrt c) →
      Tendsto
        (fun x : ℝ =>
          pintzGlobalLowDensityGrowthMajorant C sigma x
            (pintzCarlsonHeight (selectRate x) x))
        atTop (𝓝 0) := by
  rcases exists_pintzConstant_globalLowDensityGrowthMajorant_tendsto
      C sigma hC with ⟨c, hc, hfixed⟩
  refine ⟨c, hc, ?_⟩
  intro selectRate hselect hratesPos hratesGap
  have hsum :
      Tendsto
        (fun x : ℝ =>
          ∑ k ∈ rates,
            pintzGlobalLowDensityGrowthMajorant C sigma x
              (pintzCarlsonHeight k x))
        atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finset_sum rates fun k hk =>
        hfixed k (hratesPos k hk) (hratesGap k hk)
  refine squeeze_zero' ?_ ?_ hsum
  · exact Filter.Eventually.of_forall fun x => by
      exact pintzGlobalLowDensityGrowthMajorant_nonneg sigma hC
        (pintzCarlsonHeight_pos (selectRate x) x).le
  · exact Filter.Eventually.of_forall fun x => by
      apply Finset.single_le_sum
          (s := rates)
          (f := fun k =>
            pintzGlobalLowDensityGrowthMajorant C sigma x
              (pintzCarlsonHeight k x))
      · intro k hk
        exact pintzGlobalLowDensityGrowthMajorant_nonneg sigma hC
          (pintzCarlsonHeight_pos k x).le
      · exact hselect x

end PrimeNumberTheorem
