import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTFixedSigmaTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTTwoStripDensityDecay

open Filter Topology

namespace PrimeNumberTheorem

/-!
# Parametric two-strip Pintz-Carlson transfer

This module replaces the fixed high-strip boundary `3 / 4` by a parameter
`threshold`.  For `1 / 2 < threshold < 1`, the second strip is a genuine
Carlson-density strip, and the resulting hybrid density decay feeds the
fixed-sigma explicit-formula schedule.
-/

/-- Two real-part thresholds: the global-count strip starts at `0`, while the
Carlson strip starts at the optimizable parameter `threshold`. -/
def pntParametricTwoStripSigma (threshold : ℝ) : Fin 2 → ℝ :=
  fun i => if i = 0 then 0 else threshold

/-- Assign a positive-ordinate nontrivial zero to the Carlson strip exactly
when its real part lies strictly to the right of `threshold`. -/
noncomputable def pntParametricTwoStripBucketInput (threshold T : ℝ) :
    PositiveZeroBucketInput T 2 where
  bucket := fun rho => if threshold < rho.re then 1 else 0
  sigma := pntParametricTwoStripSigma threshold
  sigma_lt_re := by
    intro rho hrho
    by_cases hhigh : threshold < rho.re
    · simpa [pntParametricTwoStripSigma, hhigh] using hhigh
    · have hzero := (mem_positiveNontrivialZerosFinset.mp hrho).1
      simpa [pntParametricTwoStripSigma, hhigh] using hzero.2.1

/-- Above the Carlson boundary `1 / 2`, the high bucket is genuinely classified
as a high-density index rather than being absorbed into the global count. -/
theorem pntParametricTwoStrip_one_mem_highDensityIndices
    {threshold : ℝ} (hhalf : 1 / 2 < threshold) :
    (1 : Fin 2) ∈
      pintzCarlsonHighDensityIndices
        (pntParametricTwoStripSigma threshold) := by
  simpa [pintzCarlsonHighDensityIndices, pntParametricTwoStripSigma] using hhalf

/-- Every high-density index of the parametric two-strip family stays left of
the pole at real part `1`. -/
theorem pntParametricTwoStripSigma_high_lt_one
    {threshold : ℝ} (hlt : threshold < 1) :
    ∀ i ∈
        pintzCarlsonHighDensityIndices
          (pntParametricTwoStripSigma threshold),
      pntParametricTwoStripSigma threshold i < 1 := by
  intro i _hi
  by_cases hi : i = 0
  · simp [pntParametricTwoStripSigma, hi]
  · simpa [pntParametricTwoStripSigma, hi] using hlt

/-- A parameter in `(1 / 2, 1)` produces actual Carlson high-strip decay.
The membership conjunct records that this is not the vacuous no-high-strip
special case. -/
theorem exists_pintzConstant_parametricTwoStripHybridDensityBudget_tendsto
    (threshold : ℝ) (hhalf : 1 / 2 < threshold) (hlt : threshold < 1) :
    ∃ c > 0,
      (1 : Fin 2) ∈
          pintzCarlsonHighDensityIndices
            (pntParametricTwoStripSigma threshold) ∧
      ∀ rate : ℝ, 0 < rate → rate < 2 * Real.sqrt c →
        Tendsto
          (fun x : ℝ =>
            pintzCarlsonHybridDensityBudget
              (pntParametricTwoStripSigma threshold) x
              (pintzCarlsonHeight rate x))
          atTop (𝓝 0) := by
  rcases
      exists_pintzConstant_fixedHybridDensityBudget_tendsto
        (pntParametricTwoStripSigma threshold)
        (pntParametricTwoStripSigma_high_lt_one hlt) with
    ⟨c, hc, hdecay⟩
  exact
    ⟨c, hc, pntParametricTwoStrip_one_mem_highDensityIndices hhalf, hdecay⟩

/-- The parameterized bucket family feeds the generic fixed-sigma explicit
formula scheduler without changing its threshold as the height varies. -/
theorem exists_parametricTwoStripPNTUpperSchedule
    (threshold : ℝ) {rate : ℝ} (hrate : 0 < rate) :
    ∃ C, 0 ≤ C ∧
      Nonempty
        (FixedSigmaPNTUpperSchedule C rate
          (pntParametricTwoStripSigma threshold)) := by
  have hsigma :
      (pntParametricTwoStripBucketInput threshold 0).sigma =
        pntParametricTwoStripSigma threshold := by
    funext i
    rfl
  rw [← hsigma]
  exact exists_fixedSigmaPNTUpperSchedule hrate
    (pntParametricTwoStripBucketInput threshold) (fun _ => rfl)

/-- For every fixed strip boundary in `(1 / 2, 1)`, some positive
Pintz-Carlson height rate gives decay of the actual relative PNT error on
natural points.  This is a family of certified transfers, not yet a theorem
that optimizes the boundary over a finite grid. -/
theorem exists_fixedRate_parametricTwoStrip_relativeChebyshevPsi0Error_tendsto
    (threshold : ℝ) (hhalf : 1 / 2 < threshold) (hlt : threshold < 1) :
    ∃ rate : ℝ, 0 < rate ∧ rate ≤ 1 ∧
      Tendsto
        (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        atTop (𝓝 0) := by
  rcases
      exists_pintzConstant_parametricTwoStripHybridDensityBudget_tendsto
        threshold hhalf hlt with
    ⟨c, hc, _hhigh, hdensity⟩
  let rate : ℝ := min 1 (Real.sqrt c)
  have hsqrt : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hrate : 0 < rate := by
    exact lt_min zero_lt_one hsqrt
  have hrateOne : rate ≤ 1 := min_le_left 1 (Real.sqrt c)
  have hrateSqrt : rate ≤ Real.sqrt c :=
    min_le_right 1 (Real.sqrt c)
  have hgap : rate < 2 * Real.sqrt c := by
    linarith
  rcases exists_parametricTwoStripPNTUpperSchedule threshold hrate with
    ⟨C, hC, ⟨schedule⟩⟩
  have hbudget :=
    schedule.relativeBudget_tendsto hC hrate hrateOne
      (hdensity rate hrate hgap)
  exact
    ⟨rate, hrate, hrateOne,
      schedule.relativeError_tendsto hbudget⟩

end PrimeNumberTheorem
