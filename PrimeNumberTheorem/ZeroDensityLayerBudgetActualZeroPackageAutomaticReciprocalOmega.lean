import PrimeNumberTheorem.ZeroDensityLayerBudgetActualZeroPackageAutomaticReciprocalSignAlternative

/-!
# Automatic reciprocal unnormalized PNT Omega sign alternative

The automatic natural-point relative-error sign alternative is converted to a
real-point statement for `psi0(x) - x` at the exact `x^beta` scale.
-/

namespace PrimeNumberTheorem

open scoped Topology
open Complex Filter ZeroForcedOscillation

noncomputable section

/-- A nonempty target-line seed forces either an `Omega_+` or an `Omega_-`
witness for the actual unnormalized Chebyshev error, under the explicit
right-edge hypotheses and the reciprocal threshold `sigma < beta`. -/
theorem exists_targetLineSeed_actualReciprocalPNTUnnormalizedOmegaAlternative_automatic
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
    ∃ T L coefficient : ℝ,
      0 ≤ T ∧ 0 < L ∧ 0 < coefficient ∧
      (∀ rho ∈ S₀, rho ∈ equalRealPartZeroPackage T beta) ∧
      0 < actualEqualRealPartZeroPackageEnergy T beta L ∧
      (HasFarPositiveTargetAmplitudeWitness chebyshevPsi0Error
          (fun x : ℝ => coefficient * x ^ beta) ∨
        HasFarNegativeTargetAmplitudeWitness chebyshevPsi0Error
          (fun x : ℝ => coefficient * x ^ beta)) := by
  rcases exists_targetLineSeed_actualReciprocalPNTSignAlternative_automatic
      selection hseed hnonempty hhalf hone hsigmaBeta hbetaOne
      hheightDelta hheightDeltaBeta hcap hrealStrict hq hqOne with
    ⟨T, L, hT, hL, hseedPackage, henergy, hcoefficient, hsign⟩
  let coefficient :=
    (q * Real.sqrt (actualEqualRealPartZeroPackageEnergy T beta L) -
      2 * actualCarlsonOutsideClusterBoundaryMass
        (sigma := sigma) beta (equalRealPartZeroPackage T beta)) / 2
  refine ⟨T, L, coefficient, hT, hL, hcoefficient, hseedPackage, henergy, ?_⟩
  rcases hsign with hpos | hneg
  · left
    exact hpos.toReal.relativeChebyshevPsi0Error_to_unnormalized
  · right
    exact hneg.toReal.relativeChebyshevPsi0Error_to_unnormalized

end
end PrimeNumberTheorem
