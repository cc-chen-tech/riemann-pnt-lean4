import PrimeNumberTheorem.ZeroDensityLayerBudgetActualZeroPackageReciprocalSignAlternative
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualZeroPackageAutomaticEnergyBoundaryBudget

/-!
# Automatic reciprocal PNT sign alternative from a target-line seed

A nonempty finite seed on the target real-part line automatically determines
an actual equal-real-part package with positive energy and sufficiently small
Carlson boundary mass.  The reciprocal fixed-cluster transfer then gives one
persistent sign for the true relative PNT error under `sigma < beta`.
-/

namespace PrimeNumberTheorem

open scoped Topology
open Complex Filter ZeroForcedOscillation

noncomputable section

/-- Automatic actual-package sign alternative from a nonempty target-line
seed, with the improved reciprocal threshold `sigma < beta`. -/
theorem exists_targetLineSeed_actualReciprocalPNTSignAlternative_automatic
    {S₀ : Finset ℂ} {sigma beta q heightDelta : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hseed : IsTargetRealPartNontrivialZeroSeed beta S₀)
    (hnonempty : S₀.Nonempty)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hsigmaBeta : sigma < beta) (hbetaOne : beta < 1)
    (hheightDelta : 0 < heightDelta) (hheightDeltaBeta : heightDelta < beta)
    (hcap : OutsideClusterRealPartCap S₀ beta)
    (hrealStrict : ∀ rho : ℂ,
      RiemannHypothesis.IsNontrivialZero rho →
        rho.im = 0 → rho.re < beta)
    (hq : 0 < q) (hqOne : q < 1) :
    ∃ T L : ℝ,
      0 ≤ T ∧
      0 < L ∧
      (∀ rho ∈ S₀, rho ∈ equalRealPartZeroPackage T beta) ∧
      0 < actualEqualRealPartZeroPackageEnergy T beta L ∧
      (let coefficient :=
        (q * Real.sqrt (actualEqualRealPartZeroPackageEnergy T beta L) -
          2 * actualCarlsonOutsideClusterBoundaryMass
            (sigma := sigma) beta (equalRealPartZeroPackage T beta)) / 2
       0 < coefficient ∧
        (HasFarNaturalPointPositiveTargetAmplitudeWitness
            (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
            (fun m : ℕ => coefficient *
              targetZeroPowerAmplitude beta (m : ℝ)) ∨
          HasFarNaturalPointNegativeTargetAmplitudeWitness
            (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
            (fun m : ℕ => coefficient *
              targetZeroPowerAmplitude beta (m : ℝ)))) := by
  rcases exists_actualZeroPackage_energy_boundaryBudget
      (sigma := sigma) (beta := beta) (q := q)
      hseed hnonempty hhalf hone hcap hq with
    ⟨T, L, hT, hL, hseedPackage, hcapPackage, henergy, houtside⟩
  have hsign := actualZeroPackage_reciprocalPNTSignAlternative
    selection hhalf hone hsigmaBeta hbetaOne hheightDelta hheightDeltaBeta
    hL henergy hqOne hcapPackage hrealStrict houtside
  exact ⟨T, L, hT, hL, hseedPackage, henergy, hsign⟩

end
end PrimeNumberTheorem
