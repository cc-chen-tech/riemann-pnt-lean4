import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonBoundarySlopeFloor

/-!
# Adaptive local-density costs at a target boundary

Let `gap(m)` be the real-part separation from a target zero and let
`densityLogCost(m)` be the logarithm of the effective local zero-count cost.
After target-amplitude normalization, the exact logarithmic margin is

`gap(m) * log m - densityLogCost(m)`.

This module isolates the positive input that can replace a classical global
Carlson aggregate near a moving boundary.  The margin must tend to infinity;
mere pointwise positivity is not enough.
-/

open Filter Topology

namespace PrimeNumberTheorem

/-- Logarithmic target-normalized margin for an arbitrary local density cost. -/
noncomputable def pntAdaptiveBoundaryLocalDensityLogMargin
    (gap densityLogCost : ℕ → ℝ) (m : ℕ) : ℝ :=
  gap m * Real.log (m : ℝ) - densityLogCost m

/-- An adaptive local density cost is admissible when the remaining
target-normalized logarithmic margin tends to infinity. -/
def IsAdaptiveBoundaryLocalDensityAdmissible
    (gap densityLogCost : ℕ → ℝ) : Prop :=
  Tendsto
    (pntAdaptiveBoundaryLocalDensityLogMargin gap densityLogCost)
    atTop atTop

/-- Exponential majorant corresponding to the adaptive local-density margin. -/
noncomputable def pntAdaptiveBoundaryLocalDensityNormalizedMajorant
    (gap densityLogCost : ℕ → ℝ) (m : ℕ) : ℝ :=
  Real.exp
    (densityLogCost m - gap m * Real.log (m : ℝ))

/-- Divergence of the adaptive local-density margin makes its normalized
exponential majorant tend to zero. -/
theorem tendsto_pntAdaptiveBoundaryLocalDensityNormalizedMajorant_zero
    {gap densityLogCost : ℕ → ℝ}
    (hadmissible :
      IsAdaptiveBoundaryLocalDensityAdmissible gap densityLogCost) :
    Tendsto
      (pntAdaptiveBoundaryLocalDensityNormalizedMajorant gap densityLogCost)
      atTop (𝓝 0) := by
  have hnegative :
      Tendsto
        (fun m : ℕ =>
          -pntAdaptiveBoundaryLocalDensityLogMargin
            gap densityLogCost m)
        atTop atBot :=
    tendsto_neg_atTop_atBot.comp hadmissible
  have hexp :
      Tendsto
        (fun m : ℕ =>
          Real.exp
            (-pntAdaptiveBoundaryLocalDensityLogMargin
              gap densityLogCost m))
        atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hnegative
  refine hexp.congr' ?_
  filter_upwards with m
  unfold pntAdaptiveBoundaryLocalDensityNormalizedMajorant
    pntAdaptiveBoundaryLocalDensityLogMargin
  apply congrArg Real.exp
  ring

/-- Any admissible local density cost is eventually strictly smaller than the
available gap-logarithm budget. -/
theorem eventually_densityLogCost_lt_gap_mul_log_of_admissible
    {gap densityLogCost : ℕ → ℝ}
    (hadmissible :
      IsAdaptiveBoundaryLocalDensityAdmissible gap densityLogCost) :
    ∀ᶠ m in atTop,
      densityLogCost m < gap m * Real.log (m : ℝ) := by
  have hpositive :
      ∀ᶠ m in atTop,
        0 <
          pntAdaptiveBoundaryLocalDensityLogMargin
            gap densityLogCost m :=
    hadmissible.eventually (eventually_gt_atTop 0)
  filter_upwards [hpositive] with m hm
  unfold pntAdaptiveBoundaryLocalDensityLogMargin at hm
  linarith

/--
A fixed fractional saving in the gap-logarithm budget is sufficient, provided
that the full gap-logarithm budget itself tends to infinity.
-/
theorem isAdaptiveBoundaryLocalDensityAdmissible_of_fraction
    {gap densityLogCost : ℕ → ℝ} {epsilon : ℝ}
    (hepsilon : 0 < epsilon)
    (hgapLog :
      Tendsto
        (fun m : ℕ => gap m * Real.log (m : ℝ))
        atTop atTop)
    (hcost :
      ∀ᶠ m in atTop,
        densityLogCost m ≤
          (1 - epsilon) * (gap m * Real.log (m : ℝ))) :
    IsAdaptiveBoundaryLocalDensityAdmissible gap densityLogCost := by
  have hscaled :
      Tendsto
        (fun m : ℕ =>
          epsilon * (gap m * Real.log (m : ℝ)))
        atTop atTop :=
    hgapLog.const_mul_atTop hepsilon
  apply tendsto_atTop_mono' atTop ?_ hscaled
  filter_upwards [hcost] with m hm
  unfold pntAdaptiveBoundaryLocalDensityLogMargin
  nlinarith

/-- A magnitude bounded by a constant multiple of the adaptive normalized
majorant tends to zero. -/
theorem tendsto_abs_zero_of_le_adaptiveBoundaryLocalDensityMajorant
    {gap densityLogCost remainder : ℕ → ℝ} {C : ℝ}
    (hadmissible :
      IsAdaptiveBoundaryLocalDensityAdmissible gap densityLogCost)
    (hbound :
      ∀ᶠ m in atTop,
        |remainder m| ≤
          C *
            pntAdaptiveBoundaryLocalDensityNormalizedMajorant
              gap densityLogCost m) :
    Tendsto (fun m : ℕ => |remainder m|) atTop (𝓝 0) := by
  refine squeeze_zero' ?_ hbound ?_
  · filter_upwards with m
    exact abs_nonneg _
  · exact
      (by
        simpa using
          (tendsto_pntAdaptiveBoundaryLocalDensityNormalizedMajorant_zero
            hadmissible).const_mul C)

/-- The arbitrary local-density margin specializes definitionally to the
existing fixed-`q` moving-density margin. -/
theorem pntAdaptiveBoundaryLocalDensityLogMargin_fixedHeightCost
    (q : ℝ) (logHeight gap : ℕ → ℝ) (m : ℕ) :
    pntAdaptiveBoundaryLocalDensityLogMargin gap
        (fun k => q * logHeight k) m =
      pntMovingDensityLogMargin q logHeight gap m := by
  rfl

/-- Admissibility for the fixed height-power cost is exactly the existing
moving-density-gap condition. -/
theorem isAdaptiveBoundaryLocalDensityAdmissible_fixedHeightCost_iff
    (q : ℝ) (logHeight gap : ℕ → ℝ) :
    IsAdaptiveBoundaryLocalDensityAdmissible gap
        (fun m => q * logHeight m) ↔
      IsMovingDensityGapAdmissible q logHeight gap := by
  rfl

/-- Positive local-density input for the selected gap of the actual dynamic
equal-real-part zeta-zero package. -/
theorem
    tendsto_actualDynamicBoundaryLocalDensityNormalizedMajorant_zero
    {H : ℝ → ℝ} {beta : ℝ}
    (hright :
      ∀ m : ℕ, ∀ z ∈ positiveNontrivialZerosFinset (H (m : ℝ)),
        z.re ≤ beta)
    {densityLogCost : ℕ → ℝ}
    (hadmissible :
      IsAdaptiveBoundaryLocalDensityAdmissible
        (dynamicEqualRealPartOutsideGap H beta hright)
        densityLogCost) :
    Tendsto
      (pntAdaptiveBoundaryLocalDensityNormalizedMajorant
        (dynamicEqualRealPartOutsideGap H beta hright)
        densityLogCost)
      atTop (𝓝 0) := by
  exact
    tendsto_pntAdaptiveBoundaryLocalDensityNormalizedMajorant_zero
      hadmissible

end PrimeNumberTheorem
