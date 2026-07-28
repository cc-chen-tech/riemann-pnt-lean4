import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonFiniteSeedZeroSupportedPNTCanonicalTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonFiniteSeedCoefficientMassBidirectionalPNTTransfer

/-!
# Zero-supported coefficient-mass bidirectional actual-PNT transfer

The same selected finite cluster now carries:

* fixed-rate natural-point decay of the relative `psi0` error;
* nontrivial-zeta-zero support on the extension of the prescribed seed;
* a canonical actual-PNT oscillation transfer at coefficient
  `(c - loss) / 2`;
* a numerical finite coefficient-mass premise replacing a functional
  perturbation bound.

The seed oscillation witness and coefficient-mass inequality remain inputs.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- Unsigned joint upper/lower actual-PNT certificate with a zero-supported
selected extension and a numerical coefficient-mass perturbation premise. -/
theorem
    exists_zeroSupportedActualCarlsonFiniteSeedCoefficientMassBidirectionalPNTCanonicalSharpRealTransfer
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
      (∀ rho ∈ S \ S₀,
        RiemannHypothesis.IsNontrivialZero rho) ∧
      (∀ rho ∈ S,
        rho ∉ S₀ →
          rho ∉ realOrdinateNontrivialZerosFinset 0 →
            rho.re = beta) ∧
      (∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
          actualCarlsonPositiveZeroRealPart index ≤ beta) ∧
      (∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) ∧
      2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S <
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
      exists_fixedRate_parametricTwoStrip_relativeChebyshevPsi0Error_tendsto
        sigma hhalf hone with
    ⟨rate, hrate, hrateOne, hupper⟩
  rcases
      exists_zeroSupportedActualCarlsonFiniteSeedCanonicalSharpRealTransfer
        (c := c - loss) selection hS₀ hhalf hone hbalance hnet hcap with
    ⟨S, hcontains, hq, hstable, hcapS, hzero, hsupport,
      hreHigh, hreReal, hgap, hlower⟩
  refine
    ⟨rate, S, hrate, hrateOne, hupper, hcontains, hq, hstable,
      hcapS, hzero, hsupport, hreHigh, hreReal, hgap, ?_⟩
  intro hseed hmass
  apply hlower
  exact
    hasFarNaturalPointTargetAmplitudeWitness_visibleCluster_of_seed
      (selectedUniformGoodHeight
        (actualCarlsonBalancedHeightExponent sigma) selection)
      hcontains hseed
      (eventually_abs_dynamicVisibleClusterPNTMain_lt_loss_mul_targetAmplitude
        (selectedUniformGoodHeight
          (actualCarlsonBalancedHeightExponent sigma) selection)
        (S \ S₀)
        (finiteSeedExtension_realPart_le_of_boundarySupport hcap hsupport)
        hmass)

/-- Signed joint certificate. The same zero-supported cluster and finite
coefficient-mass premise control both witness signs. -/
theorem
    exists_zeroSupportedActualCarlsonFiniteSeedCoefficientMassBidirectionalPNTCanonicalSharpSignedRealTransfer
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
      (∀ rho ∈ S \ S₀,
        RiemannHypothesis.IsNontrivialZero rho) ∧
      (∀ rho ∈ S,
        rho ∉ S₀ →
          rho ∉ realOrdinateNontrivialZerosFinset 0 →
            rho.re = beta) ∧
      (∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
          actualCarlsonPositiveZeroRealPart index ≤ beta) ∧
      (∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) ∧
      2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S <
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
      exists_fixedRate_parametricTwoStrip_relativeChebyshevPsi0Error_tendsto
        sigma hhalf hone with
    ⟨rate, hrate, hrateOne, hupper⟩
  rcases
      exists_zeroSupportedActualCarlsonFiniteSeedCanonicalSharpSignedRealTransfer
        (c := c - loss) selection hS₀ hhalf hone hbalance hnet hcap with
    ⟨S, hcontains, hq, hstable, hcapS, hzero, hsupport,
      hreHigh, hreReal, hgap, hlower⟩
  refine
    ⟨rate, S, hrate, hrateOne, hupper, hcontains, hq, hstable,
      hcapS, hzero, hsupport, hreHigh, hreReal, hgap, ?_⟩
  intro hseedPos hseedNeg hmass
  have hnew :
      ∀ᶠ m : ℕ in atTop,
        |dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight
              (actualCarlsonBalancedHeightExponent sigma) selection)
            (S \ S₀) (m : ℝ)| <
          loss * targetZeroPowerAmplitude beta (m : ℝ) :=
    eventually_abs_dynamicVisibleClusterPNTMain_lt_loss_mul_targetAmplitude
      (selectedUniformGoodHeight
        (actualCarlsonBalancedHeightExponent sigma) selection)
      (S \ S₀)
      (finiteSeedExtension_realPart_le_of_boundarySupport hcap hsupport)
      hmass
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
