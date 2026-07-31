import PrimeNumberTheorem.ZeroDensityLayerBudgetActualZeroPackageAutomaticEnergyBoundaryBudget
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualZeroPackageCarlsonUnnormalizedSignAlternative

/-!
# Automatic target-line seed to one unnormalized PNT sign

The automatic energy-boundary budget is composed with the actual zero-package
Carlson transfer.  Starting from a nonempty finite seed on an attained global
right edge, the theorem chooses the package height and smoothing window and
returns one persistent sign for the centered Chebyshev error at `x^beta`
scale.
-/

namespace PrimeNumberTheorem

open scoped Topology
open Complex Filter ZeroForcedOscillation

noncomputable section

/--
A nonempty target-line seed, a global outside real-part cap, and strictness for
real-ordinate zeros automatically produce an actual package whose energy
dominates its Carlson boundary tail and hence one persistent unnormalized PNT
sign at the exact net `x^beta` scale.
-/
theorem exists_targetLineSeed_actualCarlsonPNTUnnormalizedSignAlternative_automatic
    {S₀ : Finset ℂ} {sigma beta q : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hseed : IsTargetRealPartNontrivialZeroSeed beta S₀)
    (hnonempty : S₀.Nonempty)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hbalance : (1 + sigma) / 2 < beta)
    (hcap : OutsideClusterRealPartCap S₀ beta)
    (hrealStrict :
      ∀ rho : ℂ,
        RiemannHypothesis.IsNontrivialZero rho →
          rho.im = 0 → rho.re < beta)
    (hq : 0 < q) (hqOne : q < 1) :
    ∃ T L rate loss : ℝ, ∃ S : Finset ℂ,
      0 ≤ T ∧
      0 < L ∧
      (∀ rho ∈ S₀, rho ∈ equalRealPartZeroPackage T beta) ∧
      0 < actualEqualRealPartZeroPackageEnergy T beta L ∧
      actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta (equalRealPartZeroPackage T beta) <
        (q * Real.sqrt
          (actualEqualRealPartZeroPackageEnergy T beta L)) / 2 ∧
      0 < rate ∧
      rate ≤ 1 ∧
      Tendsto
        (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        atTop (nhds 0) ∧
      0 < loss ∧
      0 <
        q * Real.sqrt
            (actualEqualRealPartZeroPackageEnergy T beta L) - loss ∧
      (∀ rho ∈ equalRealPartZeroPackage T beta, rho ∈ S) ∧
      IsTargetRealPartNontrivialZeroSeed beta S ∧
      finiteVisibleClusterCoefficientMass
          (S \ equalRealPartZeroPackage T beta) < loss ∧
      2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S <
        (q * Real.sqrt
            (actualEqualRealPartZeroPackageEnergy T beta L) - loss) -
          (q * Real.sqrt
              (actualEqualRealPartZeroPackageEnergy T beta L) - loss) / 2 ∧
      (HasFarPositiveTargetAmplitudeWitness
          chebyshevPsi0Error
          (fun x : ℝ =>
            ((q * Real.sqrt
                (actualEqualRealPartZeroPackageEnergy T beta L) - loss) / 2) *
              x ^ beta) ∨
        HasFarNegativeTargetAmplitudeWitness
          chebyshevPsi0Error
          (fun x : ℝ =>
            ((q * Real.sqrt
                (actualEqualRealPartZeroPackageEnergy T beta L) - loss) / 2) *
              x ^ beta)) := by
  rcases
      exists_actualZeroPackage_energy_boundaryBudget
        (sigma := sigma) (beta := beta) (q := q)
        hseed hnonempty hhalf hone hcap hq with
    ⟨T, L, hT, hL, hS₀Package, hcapPackage, henergy, houtside⟩
  rcases
      exists_actualZeroPackage_actualCarlsonHalfThresholdPNTUnnormalizedSignAlternative
        selection hhalf hone hbalance hL henergy hq hqOne
          hcapPackage hrealStrict houtside with
    ⟨rate, loss, S, hrate, hrateOne, hupper, hloss, hnet,
      hPackageS, htarget, hmass, hgap, hsign⟩
  exact
    ⟨T, L, rate, loss, S, hT, hL, hS₀Package, henergy, houtside,
      hrate, hrateOne, hupper, hloss, hnet, hPackageS, htarget,
      hmass, hgap, hsign⟩

end
end PrimeNumberTheorem
