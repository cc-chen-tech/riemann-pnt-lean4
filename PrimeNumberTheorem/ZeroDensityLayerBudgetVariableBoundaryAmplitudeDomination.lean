import PrimeNumberTheorem.ZeroDensityLayerBudgetVariableBoundaryExponentTransfer

/-!
# Variable-boundary target-amplitude domination

Fixed-exponent remainder estimates can be reused for a moving boundary whose
exponent is eventually no smaller.  This module isolates the elementary but
important denominator-monotonicity step: enlarging a positive normalization
amplitude preserves natural-point negligibility.

The result transports existing analytic remainder inputs.  It does not
construct a moving right edge or a moving-package oscillation witness.
-/

namespace PrimeNumberTheorem

open Filter Topology

/-- A remainder negligible relative to an eventually positive amplitude
remains negligible after the normalization amplitude is eventually enlarged. -/
theorem NaturalPointTargetAmplitudeNegligible.mono_amplitude
    {smaller larger remainder : ℕ → ℝ}
    (hsmallerPos : ∀ᶠ m in atTop, 0 < smaller m)
    (hlargerPos : ∀ᶠ m in atTop, 0 < larger m)
    (hle : ∀ᶠ m in atTop, smaller m ≤ larger m)
    (hnegligible :
      NaturalPointTargetAmplitudeNegligible smaller remainder) :
    NaturalPointTargetAmplitudeNegligible larger remainder := by
  unfold NaturalPointTargetAmplitudeNegligible at hnegligible ⊢
  rw [tendsto_order] at hnegligible ⊢
  constructor
  · intro a ha
    filter_upwards [hlargerPos] with m hlargerM
    exact ha.trans_le (div_nonneg (abs_nonneg _) hlargerM.le)
  · intro b hb
    filter_upwards
        [hnegligible.2 b hb, hsmallerPos, hlargerPos, hle] with
        m hratioM hsmallerM hlargerM hleM
    have hquotient :
        |remainder m| / larger m ≤ |remainder m| / smaller m := by
      apply (div_le_div_iff₀ hlargerM hsmallerM).2
      exact mul_le_mul_of_nonneg_left hleM (abs_nonneg _)
    exact hquotient.trans_lt hratioM

/-- At a natural point at least one, raising the target exponent enlarges the
real-power target amplitude. -/
theorem targetZeroPowerAmplitude_le_variableBoundaryTargetAmplitude
    {beta0 : ℝ} {beta : ℝ → ℝ} {m : ℕ}
    (hm : 1 ≤ m) (hbeta : beta0 ≤ beta (m : ℝ)) :
    targetZeroPowerAmplitude beta0 (m : ℝ) ≤
      variableBoundaryTargetAmplitude beta (m : ℝ) := by
  unfold variableBoundaryTargetAmplitude targetZeroPowerAmplitude
  exact Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast hm) (sub_le_sub_right hbeta 1)

/-- Any natural-point remainder negligible at a fixed exponent remains
negligible at a moving exponent which is eventually no smaller. -/
theorem naturalPointTargetAmplitudeNegligible_variableBoundary_of_fixed
    {beta0 : ℝ} {beta : ℝ → ℝ} {remainder : ℕ → ℝ}
    (hbeta : ∀ᶠ m : ℕ in atTop, beta0 ≤ beta (m : ℝ))
    (hnegligible :
      NaturalPointTargetAmplitudeNegligible
        (fun m : ℕ => targetZeroPowerAmplitude beta0 (m : ℝ))
        remainder) :
    NaturalPointTargetAmplitudeNegligible
      (fun m : ℕ => variableBoundaryTargetAmplitude beta (m : ℝ))
      remainder := by
  apply hnegligible.mono_amplitude
  · exact eventually_naturalPoint_pos_of_eventually_pos
      (targetZeroPowerAmplitude_eventually_pos beta0)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    unfold variableBoundaryTargetAmplitude targetZeroPowerAmplitude
    exact Real.rpow_pos_of_pos (by positivity) _
  · filter_upwards [hbeta, eventually_ge_atTop (1 : ℕ)] with m hbetaM hm
    exact targetZeroPowerAmplitude_le_variableBoundaryTargetAmplitude hm hbetaM

end PrimeNumberTheorem
