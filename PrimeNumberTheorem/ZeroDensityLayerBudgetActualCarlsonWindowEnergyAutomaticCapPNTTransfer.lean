import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonWindowEnergyBidirectionalPNTTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetVisibleClusterNormalizedCoefficientCap

namespace PrimeNumberTheorem

/--
Discharge the normalized main-cluster pointwise cap in an actual-PNT
window-energy transfer from the finite visible coefficient mass.

The remaining analytic input is exactly the pair of window-energy budgets:
a lower budget for the selected visible cluster and an upper budget for its
extension.  The conclusion concerns the genuine `chebyshevPsi0Error`.
-/
theorem HasFarWindowEnergyBudgets.visibleClusterNormalized_toActualPNTWitness
    (T : ℝ → ℝ) (E : Finset ℂ)
    {extension : ℕ → ℝ}
    {beta mainThreshold extensionThreshold : ℝ}
    {scale : ℝ → ℝ}
    (hre : ∀ rho ∈ E, rho.re ≤ beta)
    (htransfer :
      HasFarWindowEnergySeparation
          (fun m =>
            dynamicVisibleClusterPNTMain T E (m : ℝ) /
              targetZeroPowerAmplitude beta (m : ℝ))
          extension mainThreshold extensionThreshold
            (finiteVisibleClusterCoefficientMass E) →
        HasFarTargetAmplitudeWitness chebyshevPsi0Error scale)
    (hbudget :
      HasFarWindowEnergyBudgets
        (fun m =>
          dynamicVisibleClusterPNTMain T E (m : ℝ) /
            targetZeroPowerAmplitude beta (m : ℝ))
        extension mainThreshold extensionThreshold
          (finiteVisibleClusterCoefficientMass E)) :
    HasFarTargetAmplitudeWitness chebyshevPsi0Error scale :=
  htransfer
    (hbudget.visibleClusterNormalized_toEnergySeparation T E hre)

/--
Canonical sharp-real specialization of
`visibleClusterNormalized_toActualPNTWitness`.
-/
theorem HasFarWindowEnergyBudgets.visibleClusterNormalized_toCanonicalSharpRealPNTWitness
    (T : ℝ → ℝ) (E : Finset ℂ)
    {extension : ℕ → ℝ}
    {beta c loss : ℝ}
    (hre : ∀ rho ∈ E, rho.re ≤ beta)
    (htransfer :
      HasFarWindowEnergySeparation
          (fun m =>
            dynamicVisibleClusterPNTMain T E (m : ℝ) /
              targetZeroPowerAmplitude beta (m : ℝ))
          extension c loss (finiteVisibleClusterCoefficientMass E) →
        HasFarTargetAmplitudeWitness chebyshevPsi0Error
          (fun x => ((c - loss) / 2) * x ^ beta))
    (hbudget :
      HasFarWindowEnergyBudgets
        (fun m =>
          dynamicVisibleClusterPNTMain T E (m : ℝ) /
            targetZeroPowerAmplitude beta (m : ℝ))
        extension c loss (finiteVisibleClusterCoefficientMass E)) :
    HasFarTargetAmplitudeWitness chebyshevPsi0Error
      (fun x => ((c - loss) / 2) * x ^ beta) :=
  hbudget.visibleClusterNormalized_toActualPNTWitness T E hre htransfer

end PrimeNumberTheorem
