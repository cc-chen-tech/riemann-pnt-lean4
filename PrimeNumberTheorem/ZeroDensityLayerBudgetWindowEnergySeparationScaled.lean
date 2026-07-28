import PrimeNumberTheorem.ZeroDensityLayerBudgetWindowEnergySeparation

/-!
# Scaled window energy separation

This module transports a window-cardinality advantage for two sequences
normalized by the same eventually positive amplitude back to their
unnormalized threshold events.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Filter

/-- Simultaneously clear an eventually positive amplitude from the main-good
and extension-bad threshold predicates. -/
theorem HasFarWindowCardAdvantage.scaleBoth
    {main extension amplitude : ℕ → ℝ}
    {mainThreshold extensionThreshold : ℝ}
    (hamplitude : ∀ᶠ m : ℕ in atTop, 0 < amplitude m)
    (hcard :
      HasFarWindowCardAdvantage
        (fun m => mainThreshold ≤ |main m / amplitude m|)
        (fun m => extensionThreshold ≤ |extension m / amplitude m|)) :
    HasFarWindowCardAdvantage
      (fun m => mainThreshold * amplitude m ≤ |main m|)
      (fun m => extensionThreshold * amplitude m ≤ |extension m|) := by
  rcases eventually_atTop.1 hamplitude with ⟨M₀, hM₀⟩
  intro M
  rcases hcard (max M M₀) with
    ⟨G, B, hfar, hmain, hcover, hcardLt⟩
  refine ⟨G, B, ?_, ?_, ?_, hcardLt⟩
  · intro m hm
    exact le_trans (le_max_left M M₀) (hfar m hm)
  · intro m hm
    have hmAmp : 0 < amplitude m :=
      hM₀ m (le_trans (le_max_right M M₀) (hfar m hm))
    have hmNormalized := hmain m hm
    change mainThreshold ≤ |main m / amplitude m| at hmNormalized
    rw [abs_div, abs_of_pos hmAmp] at hmNormalized
    exact (le_div_iff₀ hmAmp).1 hmNormalized
  · intro m hmG hmBad
    have hmAmp : 0 < amplitude m :=
      hM₀ m (le_trans (le_max_right M M₀) (hfar m hmG))
    apply hcover m hmG
    change extensionThreshold ≤ |extension m / amplitude m|
    rw [abs_div, abs_of_pos hmAmp]
    exact (le_div_iff₀ hmAmp).2 hmBad

/-- A normalized main/extension energy separation yields the unnormalized
window-cardinality advantage after clearing an eventually positive amplitude.
-/
theorem HasFarWindowEnergySeparation.toScaledWindowCardAdvantage
    {main extension amplitude : ℕ → ℝ}
    {mainThreshold extensionThreshold mainCap : ℝ}
    (hmainThreshold : 0 ≤ mainThreshold)
    (hmainCap : mainThreshold < mainCap)
    (hextensionThreshold : 0 < extensionThreshold)
    (hamplitude : ∀ᶠ m : ℕ in atTop, 0 < amplitude m)
    (henergy :
      HasFarWindowEnergySeparation
        (fun m => main m / amplitude m)
        (fun m => extension m / amplitude m)
        mainThreshold extensionThreshold mainCap) :
    HasFarWindowCardAdvantage
      (fun m => mainThreshold * amplitude m ≤ |main m|)
      (fun m => extensionThreshold * amplitude m ≤ |extension m|) :=
  (henergy.toWindowCardAdvantage
      hmainThreshold hmainCap hextensionThreshold).scaleBoth hamplitude

end PrimeNumberTheorem
