import PrimeNumberTheorem.ZeroDensityLayerBudgetActualZeroPackageCarlsonSignAlternativePNTTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTUnnormalizedTargetAmplitudeTransfer

/-!
# Unnormalized actual zero-package sign alternative

The actual-package relative PNT sign alternative is converted to the centered
Chebyshev error at the exact `x^beta` scale.  No new zero estimate is used:
natural-point witnesses embed into the real-variable interface, and
multiplication by the positive sample point restores one power of `x`.
-/

namespace PrimeNumberTheorem

open scoped Topology
open Complex Filter ZeroForcedOscillation

noncomputable section

/--
The stack94 actual-package certificate expressed for the unnormalized error
`chebyshevPsi0 x - x`.  One persistent sign occurs at the exact net
coefficient times `x^beta`.
-/
theorem exists_actualZeroPackage_actualCarlsonHalfThresholdPNTUnnormalizedSignAlternative
    {T beta L q sigma : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hbalance : (1 + sigma) / 2 < beta)
    (hL : 0 < L)
    (henergy : 0 < actualEqualRealPartZeroPackageEnergy T beta L)
    (hq : 0 < q) (hqOne : q < 1)
    (hcap :
      OutsideClusterRealPartCap
        (equalRealPartZeroPackage T beta) beta)
    (hrealStrict :
      ∀ rho : ℂ,
        RiemannHypothesis.IsNontrivialZero rho →
          rho.im = 0 → rho.re < beta)
    (houtside :
      actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta (equalRealPartZeroPackage T beta) <
        (q * Real.sqrt
          (actualEqualRealPartZeroPackageEnergy T beta L)) / 2) :
    ∃ rate loss : ℝ, ∃ S : Finset ℂ,
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
      exists_actualZeroPackage_actualCarlsonHalfThresholdPNTSignAlternative
        selection hhalf hone hbalance hL henergy hq hqOne hcap hrealStrict
          houtside with
    ⟨rate, loss, S, hrate, hrateOne, hupper, hloss, hnet,
      hsub, hseed, hmass, hgap, hsign⟩
  have hunnormalized :
      HasFarPositiveTargetAmplitudeWitness
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
              x ^ beta) := by
    rcases hsign with hpos | hneg
    · exact Or.inl
        hpos.toReal.relativeChebyshevPsi0Error_to_unnormalized
    · exact Or.inr
        hneg.toReal.relativeChebyshevPsi0Error_to_unnormalized
  exact
    ⟨rate, loss, S, hrate, hrateOne, hupper, hloss, hnet,
      hsub, hseed, hmass, hgap, hunnormalized⟩

end
end PrimeNumberTheorem
