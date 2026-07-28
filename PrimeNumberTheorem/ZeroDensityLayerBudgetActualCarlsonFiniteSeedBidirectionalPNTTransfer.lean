import PrimeNumberTheorem.ZeroForcingUnifiedTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonFiniteSeedGapPNTCanonicalUnnormalizedTransfer

/-!
# Actual finite-seed bidirectional PNT transfer

The same strip parameter `sigma` now controls both sides of an actual PNT
certificate:

* the Pintz--Carlson two-strip upper chain gives natural-point decay of the
  relative `psi₀` error;
* the finite-seed Carlson boundary construction selects one finite cluster
  whose visible-main witness transfers to an unnormalized `x ^ beta` lower
  bound.

The visible-cluster oscillation witness remains an explicit implication
hypothesis.  Thus these theorems do not claim an unconditional `Omega` or
`Omega_±` result.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- Joint actual-PNT certificate with a canonical unsigned lower coefficient.

The upper decay rate and the finite Carlson transfer cluster are selected in
one existential package.  In particular, this is stronger than returning an
abstract upper/lower facade: the cluster retains the prescribed zeta seed,
the final outside-cluster zeta cap, the boundary-support certificate, and the
strict boundary-mass gap used by the actual explicit-formula transfer. -/
theorem
    exists_actualCarlsonFiniteSeedBidirectionalPNTCanonicalSharpRealTransfer
    {S₀ : Finset ℂ} {sigma beta c : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hS₀ : ∀ rho : ℂ, rho ∈ S₀ ↔ (starRingEnd ℂ) rho ∈ S₀)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hbalance : (1 + sigma) / 2 < beta)
    (hc : 0 < c)
    (hcap : OutsideClusterRealPartCap S₀ beta) :
    ∃ rate : ℝ, ∃ S : Finset ℂ,
      0 < rate ∧
      rate ≤ 1 ∧
      Tendsto
        (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        atTop (nhds 0) ∧
      (∀ rho ∈ S₀, rho ∈ S) ∧
      0 < c / 2 ∧
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
        c - c / 2 ∧
      (HasFarNaturalPointTargetAmplitudeWitness
          (fun m =>
            dynamicVisibleClusterPNTMain
              (selectedUniformGoodHeight
                (actualCarlsonBalancedHeightExponent sigma) selection)
              S (m : ℝ))
          (fun m => c * targetZeroPowerAmplitude beta (m : ℝ)) →
        HasFarTargetAmplitudeWitness
          chebyshevPsi0Error
          (fun x => (c / 2) * x ^ beta)) := by
  rcases
      exists_fixedRate_parametricTwoStrip_relativeChebyshevPsi0Error_tendsto
        sigma hhalf hone with
    ⟨rate, hrate, hrateOne, hupper⟩
  rcases
      exists_actualCarlsonFiniteSeedGapClusterAndPsi0ErrorCanonicalSharpRealTransfer
        selection hS₀ hhalf hone hbalance hc hcap with
    ⟨S, hseed, hq, hS, hcapS, hsupport, hreHigh, hreReal, hgap, hlower⟩
  exact
    ⟨rate, S, hrate, hrateOne, hupper, hseed, hq, hS, hcapS,
      hsupport, hreHigh, hreReal, hgap, hlower⟩

/-- Signed version of the joint actual-PNT certificate.

The same selected finite cluster must supply both positive and negative
visible-main witnesses; all upper, seed, cap, support, and boundary-gap
certificates are shared. -/
theorem
    exists_actualCarlsonFiniteSeedBidirectionalPNTCanonicalSharpSignedRealTransfer
    {S₀ : Finset ℂ} {sigma beta c : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hS₀ : ∀ rho : ℂ, rho ∈ S₀ ↔ (starRingEnd ℂ) rho ∈ S₀)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hbalance : (1 + sigma) / 2 < beta)
    (hc : 0 < c)
    (hcap : OutsideClusterRealPartCap S₀ beta) :
    ∃ rate : ℝ, ∃ S : Finset ℂ,
      0 < rate ∧
      rate ≤ 1 ∧
      Tendsto
        (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        atTop (nhds 0) ∧
      (∀ rho ∈ S₀, rho ∈ S) ∧
      0 < c / 2 ∧
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
        c - c / 2 ∧
      (HasFarNaturalPointPositiveTargetAmplitudeWitness
          (fun m =>
            dynamicVisibleClusterPNTMain
              (selectedUniformGoodHeight
                (actualCarlsonBalancedHeightExponent sigma) selection)
              S (m : ℝ))
          (fun m => c * targetZeroPowerAmplitude beta (m : ℝ)) →
        HasFarNaturalPointNegativeTargetAmplitudeWitness
            (fun m =>
              dynamicVisibleClusterPNTMain
                (selectedUniformGoodHeight
                  (actualCarlsonBalancedHeightExponent sigma) selection)
                S (m : ℝ))
            (fun m => c * targetZeroPowerAmplitude beta (m : ℝ)) →
          HasFarSignedTargetAmplitudeWitnesses
            chebyshevPsi0Error
            (fun x => (c / 2) * x ^ beta)) := by
  rcases
      exists_fixedRate_parametricTwoStrip_relativeChebyshevPsi0Error_tendsto
        sigma hhalf hone with
    ⟨rate, hrate, hrateOne, hupper⟩
  rcases
      exists_actualCarlsonFiniteSeedGapClusterAndPsi0ErrorCanonicalSharpSignedRealTransfer
        selection hS₀ hhalf hone hbalance hc hcap with
    ⟨S, hseed, hq, hS, hcapS, hsupport, hreHigh, hreReal, hgap, hlower⟩
  exact
    ⟨rate, S, hrate, hrateOne, hupper, hseed, hq, hS, hcapS,
      hsupport, hreHigh, hreReal, hgap, hlower⟩

end PrimeNumberTheorem
