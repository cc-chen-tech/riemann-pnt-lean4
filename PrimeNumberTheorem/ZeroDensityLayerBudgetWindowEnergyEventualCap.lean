import PrimeNumberTheorem.ZeroDensityLayerBudgetWindowEnergySeparation

/-!
# Window energy budgets with an eventual main cap

The quantitative window-energy package previously repeated a pointwise main
cap inside every selected window.  This module separates the genuinely local
energy budgets from an eventual cap, then synchronizes the latter with each
far window.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Filter

/-- Far-window lower/upper energy budgets without a repeated pointwise cap
field. -/
def HasFarWindowEnergyBudgets
    (main extension : ℕ → ℝ)
    (mainThreshold extensionThreshold mainCap : ℝ) : Prop :=
  ∀ M : ℕ, ∃ G : Finset ℕ, ∃ K : ℕ,
    (∀ m ∈ G, M ≤ m) ∧
    ((G.card : ℝ) * mainThreshold ^ 2 +
          (K : ℝ) * (mainCap ^ 2 - mainThreshold ^ 2) <
        ∑ m ∈ G, (main m) ^ 2) ∧
    ((∑ m ∈ G.filter
          (fun n => extensionThreshold ≤ |extension n|),
        (extension m) ^ 2) <
      (K : ℝ) * extensionThreshold ^ 2)

/-- An eventual pointwise main cap can be synchronized with every far-window
energy budget. -/
theorem HasFarWindowEnergyBudgets.toEnergySeparation
    {main extension : ℕ → ℝ}
    {mainThreshold extensionThreshold mainCap : ℝ}
    (hcap : ∀ᶠ m : ℕ in atTop, |main m| ≤ mainCap)
    (hbudget :
      HasFarWindowEnergyBudgets
        main extension mainThreshold extensionThreshold mainCap) :
    HasFarWindowEnergySeparation
      main extension mainThreshold extensionThreshold mainCap := by
  rcases eventually_atTop.1 hcap with ⟨M₀, hM₀⟩
  intro M
  rcases hbudget (max M M₀) with
    ⟨G, K, hfar, hmainEnergy, hextensionEnergy⟩
  refine ⟨G, K, ?_, ?_, hmainEnergy, hextensionEnergy⟩
  · intro m hm
    exact le_trans (le_max_left M M₀) (hfar m hm)
  · intro m hm
    exact hM₀ m (le_trans (le_max_right M M₀) (hfar m hm))

end PrimeNumberTheorem
