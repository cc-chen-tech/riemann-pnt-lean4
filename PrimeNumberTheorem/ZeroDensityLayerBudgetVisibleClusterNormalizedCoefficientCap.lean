import PrimeNumberTheorem.ZeroDensityLayerBudgetVisibleClusterCoefficientMass
import PrimeNumberTheorem.ZeroDensityLayerBudgetWindowEnergyEventualCap

/-!
# Automatic normalized coefficient cap for visible clusters

The deterministic finite coefficient-mass bound is divided by the eventually
positive target zero-power amplitude.  It supplies exactly the eventual main
cap needed by the reduced window-energy budget package.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Filter

/-- A finite visible cluster whose real parts are at most `beta` is eventually
bounded, after target-amplitude normalization, by its coefficient mass. -/
theorem
    eventually_abs_dynamicVisibleClusterPNTMain_div_targetAmplitude_le_coefficientMass
    (T : ℝ → ℝ) (E : Finset ℂ) {beta : ℝ}
    (hre : ∀ rho ∈ E, rho.re ≤ beta) :
    ∀ᶠ m : ℕ in atTop,
      |dynamicVisibleClusterPNTMain T E (m : ℝ) /
          targetZeroPowerAmplitude beta (m : ℝ)| ≤
        finiteVisibleClusterCoefficientMass E := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  have hmReal : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  have hamplitude :
      0 < targetZeroPowerAmplitude beta (m : ℝ) :=
    Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hmReal) _
  rw [abs_div, abs_of_pos hamplitude]
  apply (div_le_iff₀ hamplitude).2
  exact
    abs_dynamicVisibleClusterPNTMain_le_coefficientMass_mul_targetAmplitude
      T E hmReal hre

/-- The automatic normalized coefficient cap upgrades reduced local energy
budgets for a visible main cluster to full energy separation. -/
theorem HasFarWindowEnergyBudgets.visibleClusterNormalized_toEnergySeparation
    (T : ℝ → ℝ) (E : Finset ℂ)
    {extension : ℕ → ℝ}
    {beta mainThreshold extensionThreshold : ℝ}
    (hre : ∀ rho ∈ E, rho.re ≤ beta)
    (hbudget :
      HasFarWindowEnergyBudgets
        (fun m =>
          dynamicVisibleClusterPNTMain T E (m : ℝ) /
            targetZeroPowerAmplitude beta (m : ℝ))
        extension mainThreshold extensionThreshold
          (finiteVisibleClusterCoefficientMass E)) :
    HasFarWindowEnergySeparation
      (fun m =>
        dynamicVisibleClusterPNTMain T E (m : ℝ) /
          targetZeroPowerAmplitude beta (m : ℝ))
      extension mainThreshold extensionThreshold
        (finiteVisibleClusterCoefficientMass E) :=
  hbudget.toEnergySeparation
    (eventually_abs_dynamicVisibleClusterPNTMain_div_targetAmplitude_le_coefficientMass
      T E hre)

end PrimeNumberTheorem
