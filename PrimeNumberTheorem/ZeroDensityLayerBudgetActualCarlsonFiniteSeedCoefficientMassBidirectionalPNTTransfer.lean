import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonFiniteSeedPerturbedBidirectionalPNTTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetVisibleClusterCoefficientMass
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonFiniteSeedExtensionCap

/-!
# Actual PNT transfer from a finite seed and coefficient mass

These theorems replace the functional perturbation input in the perturbed-seed
actual-PNT transfer by the finite numerical condition

`finiteVisibleClusterCoefficientMass (S \ S₀) < loss`.

The Carlson selector's boundary-support certificate and the original seed cap
automatically give `Re rho ≤ beta` on `S \ S₀`, so the explicit coefficient
mass estimate supplies the required eventual perturbation bound.

The mass inequality remains an input.  In particular, this module does not
claim that Carlson boundary capture makes the newly adjoined mass small, nor
does it close an unconditional oscillation theorem.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- Joint upper/lower actual-PNT certificate whose only added-cluster
perturbation input is a finite coefficient-mass inequality. -/
theorem
    exists_actualCarlsonFiniteSeedCoefficientMassBidirectionalPNTCanonicalSharpRealTransfer
    {S₀ : Finset ℂ} {sigma beta c loss : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hS₀ : ∀ rho : ℂ, rho ∈ S₀ ↔ (starRingEnd ℂ) rho ∈ S₀)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hbalance : (1 + sigma) / 2 < beta)
    (hnet : 0 < c - loss)
    (hcap : OutsideClusterRealPartCap S₀ beta) :
    ∃ rate : ℝ, ∃ S : Finset ℂ,
      0 < rate ∧
      rate ≤ 1 ∧
      Tendsto
        (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        atTop (nhds 0) ∧
      (∀ rho ∈ S₀, rho ∈ S) ∧
      0 < (c - loss) / 2 ∧
      (∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S) ∧
      OutsideClusterRealPartCap S beta ∧
      (∀ rho ∈ S,
        rho ∉ S₀ →
        rho ∉ realOrdinateNontrivialZerosFinset 0 →
        rho.re = beta) ∧
      (∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
        actualCarlsonPositiveZeroRealPart index ≤ beta) ∧
      (∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) ∧
      2 * actualCarlsonOutsideClusterBoundaryMass (sigma := sigma) beta S <
        (c - loss) - (c - loss) / 2 ∧
      (HasFarNaturalPointTargetAmplitudeWitness
          (fun m =>
            dynamicVisibleClusterPNTMain
              (selectedUniformGoodHeight
                (actualCarlsonBalancedHeightExponent sigma) selection)
              S₀ (m : ℝ))
          (fun m => c * targetZeroPowerAmplitude beta (m : ℝ)) →
        finiteVisibleClusterCoefficientMass (S \ S₀) < loss →
        HasFarTargetAmplitudeWitness
          chebyshevPsi0Error
          (fun x => ((c - loss) / 2) * x ^ beta)) := by
  rcases
      exists_actualCarlsonFiniteSeedPerturbedBidirectionalPNTCanonicalSharpRealTransfer
        selection hS₀ hhalf hone hbalance hnet hcap with
    ⟨rate, S, hrate, hrateOne, hupper, hcontains, hq, hS, hcapS,
      hsupport, hreHigh, hreReal, hgap, hlower⟩
  refine
    ⟨rate, S, hrate, hrateOne, hupper, hcontains, hq, hS, hcapS,
      hsupport, hreHigh, hreReal, hgap, ?_⟩
  intro hseed hmass
  apply hlower hseed
  exact
    eventually_abs_dynamicVisibleClusterPNTMain_lt_loss_mul_targetAmplitude
      (selectedUniformGoodHeight
        (actualCarlsonBalancedHeightExponent sigma) selection)
      (S \ S₀)
      (finiteSeedExtension_realPart_le_of_boundarySupport hcap hsupport)
      hmass

/-- Signed coefficient-mass version.  The same finite mass inequality controls
the added cluster for both witness signs. -/
theorem
    exists_actualCarlsonFiniteSeedCoefficientMassBidirectionalPNTCanonicalSharpSignedRealTransfer
    {S₀ : Finset ℂ} {sigma beta c loss : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hS₀ : ∀ rho : ℂ, rho ∈ S₀ ↔ (starRingEnd ℂ) rho ∈ S₀)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hbalance : (1 + sigma) / 2 < beta)
    (hnet : 0 < c - loss)
    (hcap : OutsideClusterRealPartCap S₀ beta) :
    ∃ rate : ℝ, ∃ S : Finset ℂ,
      0 < rate ∧
      rate ≤ 1 ∧
      Tendsto
        (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        atTop (nhds 0) ∧
      (∀ rho ∈ S₀, rho ∈ S) ∧
      0 < (c - loss) / 2 ∧
      (∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S) ∧
      OutsideClusterRealPartCap S beta ∧
      (∀ rho ∈ S,
        rho ∉ S₀ →
        rho ∉ realOrdinateNontrivialZerosFinset 0 →
        rho.re = beta) ∧
      (∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
        actualCarlsonPositiveZeroRealPart index ≤ beta) ∧
      (∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) ∧
      2 * actualCarlsonOutsideClusterBoundaryMass (sigma := sigma) beta S <
        (c - loss) - (c - loss) / 2 ∧
      (HasFarNaturalPointPositiveTargetAmplitudeWitness
          (fun m =>
            dynamicVisibleClusterPNTMain
              (selectedUniformGoodHeight
                (actualCarlsonBalancedHeightExponent sigma) selection)
              S₀ (m : ℝ))
          (fun m => c * targetZeroPowerAmplitude beta (m : ℝ)) →
        HasFarNaturalPointNegativeTargetAmplitudeWitness
            (fun m =>
              dynamicVisibleClusterPNTMain
                (selectedUniformGoodHeight
                  (actualCarlsonBalancedHeightExponent sigma) selection)
                S₀ (m : ℝ))
            (fun m => c * targetZeroPowerAmplitude beta (m : ℝ)) →
        finiteVisibleClusterCoefficientMass (S \ S₀) < loss →
        HasFarSignedTargetAmplitudeWitnesses
          chebyshevPsi0Error
          (fun x => ((c - loss) / 2) * x ^ beta)) := by
  rcases
      exists_actualCarlsonFiniteSeedPerturbedBidirectionalPNTCanonicalSharpSignedRealTransfer
        selection hS₀ hhalf hone hbalance hnet hcap with
    ⟨rate, S, hrate, hrateOne, hupper, hcontains, hq, hS, hcapS,
      hsupport, hreHigh, hreReal, hgap, hlower⟩
  refine
    ⟨rate, S, hrate, hrateOne, hupper, hcontains, hq, hS, hcapS,
      hsupport, hreHigh, hreReal, hgap, ?_⟩
  intro hseedPos hseedNeg hmass
  apply hlower hseedPos hseedNeg
  exact
    eventually_abs_dynamicVisibleClusterPNTMain_lt_loss_mul_targetAmplitude
      (selectedUniformGoodHeight
        (actualCarlsonBalancedHeightExponent sigma) selection)
      (S \ S₀)
      (finiteSeedExtension_realPart_le_of_boundarySupport hcap hsupport)
      hmass

end PrimeNumberTheorem
