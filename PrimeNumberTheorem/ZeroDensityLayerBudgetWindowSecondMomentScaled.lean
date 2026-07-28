import PrimeNumberTheorem.ZeroDensityLayerBudgetWindowSecondMomentBadCount

/-!
# Scaled window second-moment transfer

A second moment is naturally estimated after division by the target
amplitude, whereas the oscillation transfer uses the unnormalized bad event

`threshold * amplitude m <= |remainder m|`.

This module proves that an eventually positive amplitude identifies these two
bad events on sufficiently far windows.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Filter

/-- A second-moment certificate for the normalized remainder yields the
unnormalized window-cardinality advantage once the amplitude is eventually
positive. -/
theorem HasFarWindowSecondMomentAdvantage.toScaledWindowCardAdvantage
    {good : ℕ → Prop} {amplitude remainder : ℕ → ℝ} {threshold : ℝ}
    (hthreshold : 0 < threshold)
    (hamplitude : ∀ᶠ m : ℕ in atTop, 0 < amplitude m)
    (hsecond :
      HasFarWindowSecondMomentAdvantage
        good (fun m => remainder m / amplitude m) threshold) :
    HasFarWindowCardAdvantage
      good (fun m => threshold * amplitude m ≤ |remainder m|) := by
  rcases eventually_atTop.1 hamplitude with ⟨M₀, hM₀⟩
  intro M
  rcases hsecond (max M M₀) with ⟨G, hfar, hgood, hsum⟩
  let B :=
    G.filter
      (fun m => threshold ≤ |remainder m / amplitude m|)
  refine ⟨G, B, ?_, hgood, ?_, ?_⟩
  · intro m hm
    exact le_trans (le_max_left M M₀) (hfar m hm)
  · intro m hmG hmBad
    have hmAmp : 0 < amplitude m :=
      hM₀ m (le_trans (le_max_right M M₀) (hfar m hmG))
    have hmNormalized :
        threshold ≤ |remainder m / amplitude m| := by
      rw [abs_div, abs_of_pos hmAmp]
      exact (le_div_iff₀ hmAmp).2 hmBad
    exact Finset.mem_filter.mpr ⟨hmG, hmNormalized⟩
  · exact
      filter_card_lt_of_sum_sq_lt_card_mul_sq
        G (fun m => remainder m / amplitude m) hthreshold hsum

end PrimeNumberTheorem
