import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonZeroSupportedCoefficientMassBidirectionalPNTTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetWindowCountAntiCancellation

/-!
# Window-count bidirectional actual-PNT transfer

This module replaces the global coefficient-mass smallness premise in the
zero-supported bidirectional transfer by a synchronized finite-window count
advantage.  In every sufficiently far finite window, the prescribed seed has
strictly more large points than the selected extension has perturbative bad
points.  A seed-good, extension-not-bad point therefore exists in each window.

The count advantage remains an external analytic input.  The conclusion uses
the same selected Carlson cluster for the relative PNT upper bound and the
actual `psi0` oscillation lower transfer.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- Unsigned joint upper/lower actual-PNT certificate driven by a synchronized
window-count anti-cancellation premise. -/
theorem
    exists_zeroSupportedActualCarlsonFiniteSeedWindowCountBidirectionalPNTCanonicalSharpRealTransfer
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
      (HasFarWindowCardAdvantage
          (fun m =>
            c * targetZeroPowerAmplitude beta (m : ℝ) ≤
              |dynamicVisibleClusterPNTMain
                (selectedUniformGoodHeight
                  (actualCarlsonBalancedHeightExponent sigma) selection)
                S₀ (m : ℝ)|)
          (fun m =>
            loss * targetZeroPowerAmplitude beta (m : ℝ) ≤
              |dynamicVisibleClusterPNTMain
                (selectedUniformGoodHeight
                  (actualCarlsonBalancedHeightExponent sigma) selection)
                (S \ S₀) (m : ℝ)|) →
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
  intro hwindow
  apply hlower
  exact
    hasFarNaturalPointTargetAmplitudeWitness_visibleCluster_of_seed_windowCount
      (selectedUniformGoodHeight
        (actualCarlsonBalancedHeightExponent sigma) selection)
      hcontains hwindow

/-- Signed joint certificate.  Separate positive and negative seed-good counts
are compared with the same extension-bad predicate. -/
theorem
    exists_zeroSupportedActualCarlsonFiniteSeedWindowCountBidirectionalPNTCanonicalSharpSignedRealTransfer
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
      (HasFarWindowCardAdvantage
          (fun m =>
            c * targetZeroPowerAmplitude beta (m : ℝ) ≤
              dynamicVisibleClusterPNTMain
                (selectedUniformGoodHeight
                  (actualCarlsonBalancedHeightExponent sigma) selection)
                S₀ (m : ℝ))
          (fun m =>
            loss * targetZeroPowerAmplitude beta (m : ℝ) ≤
              |dynamicVisibleClusterPNTMain
                (selectedUniformGoodHeight
                  (actualCarlsonBalancedHeightExponent sigma) selection)
                (S \ S₀) (m : ℝ)|) →
        HasFarWindowCardAdvantage
          (fun m =>
            dynamicVisibleClusterPNTMain
                (selectedUniformGoodHeight
                  (actualCarlsonBalancedHeightExponent sigma) selection)
                S₀ (m : ℝ) ≤
              -(c * targetZeroPowerAmplitude beta (m : ℝ)))
          (fun m =>
            loss * targetZeroPowerAmplitude beta (m : ℝ) ≤
              |dynamicVisibleClusterPNTMain
                (selectedUniformGoodHeight
                  (actualCarlsonBalancedHeightExponent sigma) selection)
                (S \ S₀) (m : ℝ)|) →
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
  intro hwindowPos hwindowNeg
  apply hlower
  · exact
      hasFarNaturalPointPositiveTargetAmplitudeWitness_visibleCluster_of_seed_windowCount
        (selectedUniformGoodHeight
          (actualCarlsonBalancedHeightExponent sigma) selection)
        hcontains hwindowPos
  · exact
      hasFarNaturalPointNegativeTargetAmplitudeWitness_visibleCluster_of_seed_windowCount
        (selectedUniformGoodHeight
          (actualCarlsonBalancedHeightExponent sigma) selection)
        hcontains hwindowNeg

end PrimeNumberTheorem
