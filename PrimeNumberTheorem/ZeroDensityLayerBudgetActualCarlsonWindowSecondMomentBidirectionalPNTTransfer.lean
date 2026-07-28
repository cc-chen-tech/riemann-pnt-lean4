import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonWindowCountBidirectionalPNTTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetWindowSecondMomentScaled
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTReverseClusterExclusion

/-!
# Window-second-moment bidirectional actual-PNT transfer

This module specializes the window-count actual-PNT certificate to a
second-moment premise for the selected extension normalized by the target
zero-power amplitude.

The normalized second-moment premise remains an external analytic input.  The
same zero-supported Carlson cluster supports both the relative PNT upper bound
and the actual `psi0` lower transfer.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- Unsigned actual-PNT transfer from a normalized extension second-moment
certificate. -/
theorem
    exists_zeroSupportedActualCarlsonFiniteSeedWindowSecondMomentBidirectionalPNTCanonicalSharpRealTransfer
    {S₀ : Finset ℂ} {sigma beta c loss : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hS₀ : ∀ rho : ℂ, rho ∈ S₀ ↔ (starRingEnd ℂ) rho ∈ S₀)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hbalance : (1 + sigma) / 2 < beta)
    (hnet : 0 < c - loss)
    (hloss : 0 < loss)
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
      (HasFarWindowSecondMomentAdvantage
          (fun m =>
            c * targetZeroPowerAmplitude beta (m : ℝ) ≤
              |dynamicVisibleClusterPNTMain
                (selectedUniformGoodHeight
                  (actualCarlsonBalancedHeightExponent sigma) selection)
                S₀ (m : ℝ)|)
          (fun m =>
            dynamicVisibleClusterPNTMain
                (selectedUniformGoodHeight
                  (actualCarlsonBalancedHeightExponent sigma) selection)
                (S \ S₀) (m : ℝ) /
              targetZeroPowerAmplitude beta (m : ℝ))
          loss →
        HasFarTargetAmplitudeWitness
          chebyshevPsi0Error
          (fun x => ((c - loss) / 2) * x ^ beta)) := by
  rcases
      exists_zeroSupportedActualCarlsonFiniteSeedWindowCountBidirectionalPNTCanonicalSharpRealTransfer
        selection hS₀ hhalf hone hbalance hnet hcap with
    ⟨rate, S, hrate, hrateOne, hupper, hcontains, hq, hstable,
      hcapS, hzero, hsupport, hreHigh, hreReal, hgap, hlower⟩
  refine
    ⟨rate, S, hrate, hrateOne, hupper, hcontains, hq, hstable,
      hcapS, hzero, hsupport, hreHigh, hreReal, hgap, ?_⟩
  intro hsecond
  apply hlower
  exact
    hsecond.toScaledWindowCardAdvantage
      hloss (eventually_targetZeroPowerAmplitude_natural_pos beta)

/-- Signed actual-PNT transfer from positive and negative normalized
second-moment certificates sharing the same selected extension. -/
theorem
    exists_zeroSupportedActualCarlsonFiniteSeedWindowSecondMomentBidirectionalPNTCanonicalSharpSignedRealTransfer
    {S₀ : Finset ℂ} {sigma beta c loss : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hS₀ : ∀ rho : ℂ, rho ∈ S₀ ↔ (starRingEnd ℂ) rho ∈ S₀)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hbalance : (1 + sigma) / 2 < beta)
    (hnet : 0 < c - loss)
    (hloss : 0 < loss)
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
      (HasFarWindowSecondMomentAdvantage
          (fun m =>
            c * targetZeroPowerAmplitude beta (m : ℝ) ≤
              dynamicVisibleClusterPNTMain
                (selectedUniformGoodHeight
                  (actualCarlsonBalancedHeightExponent sigma) selection)
                S₀ (m : ℝ))
          (fun m =>
            dynamicVisibleClusterPNTMain
                (selectedUniformGoodHeight
                  (actualCarlsonBalancedHeightExponent sigma) selection)
                (S \ S₀) (m : ℝ) /
              targetZeroPowerAmplitude beta (m : ℝ))
          loss →
        HasFarWindowSecondMomentAdvantage
          (fun m =>
            dynamicVisibleClusterPNTMain
                (selectedUniformGoodHeight
                  (actualCarlsonBalancedHeightExponent sigma) selection)
                S₀ (m : ℝ) ≤
              -(c * targetZeroPowerAmplitude beta (m : ℝ)))
          (fun m =>
            dynamicVisibleClusterPNTMain
                (selectedUniformGoodHeight
                  (actualCarlsonBalancedHeightExponent sigma) selection)
                (S \ S₀) (m : ℝ) /
              targetZeroPowerAmplitude beta (m : ℝ))
          loss →
        HasFarSignedTargetAmplitudeWitnesses
          chebyshevPsi0Error
          (fun x => ((c - loss) / 2) * x ^ beta)) := by
  rcases
      exists_zeroSupportedActualCarlsonFiniteSeedWindowCountBidirectionalPNTCanonicalSharpSignedRealTransfer
        selection hS₀ hhalf hone hbalance hnet hcap with
    ⟨rate, S, hrate, hrateOne, hupper, hcontains, hq, hstable,
      hcapS, hzero, hsupport, hreHigh, hreReal, hgap, hlower⟩
  refine
    ⟨rate, S, hrate, hrateOne, hupper, hcontains, hq, hstable,
      hcapS, hzero, hsupport, hreHigh, hreReal, hgap, ?_⟩
  intro hsecondPos hsecondNeg
  apply hlower
  · exact
      hsecondPos.toScaledWindowCardAdvantage
        hloss (eventually_targetZeroPowerAmplitude_natural_pos beta)
  · exact
      hsecondNeg.toScaledWindowCardAdvantage
        hloss (eventually_targetZeroPowerAmplitude_natural_pos beta)

end PrimeNumberTheorem
