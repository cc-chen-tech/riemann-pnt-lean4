import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonFiniteSeedBidirectionalPNTTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetVisibleClusterSeedExtension

/-!
# Actual PNT transfer from a perturbed finite seed

These theorems refine the finite-seed bidirectional PNT certificate by moving
the local oscillation hypothesis back from the automatically expanded cluster
to the prescribed seed `S₀`.

If the seed has coefficient `c` and the newly adjoined visible terms cost at
most `loss` on the target scale, the expanded cluster has coefficient
`c - loss`.  The canonical Carlson boundary transfer then retains
`(c - loss) / 2` for the actual unnormalized PNT error.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- Joint upper/lower actual-PNT certificate whose local oscillation input is
stated on the prescribed seed cluster rather than on the selected extension. -/
theorem
    exists_actualCarlsonFiniteSeedPerturbedBidirectionalPNTCanonicalSharpRealTransfer
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
        (∀ᶠ m : ℕ in atTop,
          |dynamicVisibleClusterPNTMain
              (selectedUniformGoodHeight
                (actualCarlsonBalancedHeightExponent sigma) selection)
              (S \ S₀) (m : ℝ)| <
            loss * targetZeroPowerAmplitude beta (m : ℝ)) →
        HasFarTargetAmplitudeWitness
          chebyshevPsi0Error
          (fun x => ((c - loss) / 2) * x ^ beta)) := by
  rcases
      exists_actualCarlsonFiniteSeedBidirectionalPNTCanonicalSharpRealTransfer
        (c := c - loss) selection hS₀ hhalf hone hbalance hnet hcap with
    ⟨rate, S, hrate, hrateOne, hupper, hcontains, hq, hS, hcapS,
      hsupport, hreHigh, hreReal, hgap, hlower⟩
  refine
    ⟨rate, S, hrate, hrateOne, hupper, hcontains, hq, hS, hcapS,
      hsupport, hreHigh, hreReal, hgap, ?_⟩
  intro hseed hnew
  apply hlower
  exact
    hasFarNaturalPointTargetAmplitudeWitness_visibleCluster_of_seed
      (selectedUniformGoodHeight
        (actualCarlsonBalancedHeightExponent sigma) selection)
      hcontains hseed hnew

/-- Signed perturbed-seed version.  One added-term budget is shared by the
positive and negative seed witnesses. -/
theorem
    exists_actualCarlsonFiniteSeedPerturbedBidirectionalPNTCanonicalSharpSignedRealTransfer
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
        (∀ᶠ m : ℕ in atTop,
          |dynamicVisibleClusterPNTMain
              (selectedUniformGoodHeight
                (actualCarlsonBalancedHeightExponent sigma) selection)
              (S \ S₀) (m : ℝ)| <
            loss * targetZeroPowerAmplitude beta (m : ℝ)) →
        HasFarSignedTargetAmplitudeWitnesses
          chebyshevPsi0Error
          (fun x => ((c - loss) / 2) * x ^ beta)) := by
  rcases
      exists_actualCarlsonFiniteSeedBidirectionalPNTCanonicalSharpSignedRealTransfer
        (c := c - loss) selection hS₀ hhalf hone hbalance hnet hcap with
    ⟨rate, S, hrate, hrateOne, hupper, hcontains, hq, hS, hcapS,
      hsupport, hreHigh, hreReal, hgap, hlower⟩
  refine
    ⟨rate, S, hrate, hrateOne, hupper, hcontains, hq, hS, hcapS,
      hsupport, hreHigh, hreReal, hgap, ?_⟩
  intro hseedPos hseedNeg hnew
  apply hlower
  · exact
      hasFarNaturalPointPositiveTargetAmplitudeWitness_visibleCluster_of_seed
        (selectedUniformGoodHeight
          (actualCarlsonBalancedHeightExponent sigma) selection)
        hcontains hseedPos hnew
  · exact
      hasFarNaturalPointNegativeTargetAmplitudeWitness_visibleCluster_of_seed
        (selectedUniformGoodHeight
          (actualCarlsonBalancedHeightExponent sigma) selection)
        hcontains hseedNeg hnew

end PrimeNumberTheorem
