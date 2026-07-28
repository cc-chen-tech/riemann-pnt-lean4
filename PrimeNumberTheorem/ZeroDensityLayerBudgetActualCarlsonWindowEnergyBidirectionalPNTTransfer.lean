import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonWindowCountBidirectionalPNTTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetWindowEnergySeparationScaled
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTReverseClusterExclusion

/-!
# Window-energy bidirectional actual-PNT transfer

The zero-supported Carlson selector is combined with a quantitative normalized
energy separation between the prescribed seed and its selected extension.
This yields a single unsigned upper/lower actual-PNT certificate.

The energy separation remains an external local analytic input.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- The same zero-supported selected cluster carries fixed-rate relative PNT
decay and an unsigned actual-`psi0` lower transfer whenever its normalized seed
and extension satisfy the quantitative far-window energy separation. -/
theorem
    exists_zeroSupportedActualCarlsonFiniteSeedWindowEnergyBidirectionalPNTCanonicalSharpRealTransfer
    {S₀ : Finset ℂ} {sigma beta c loss mainCap : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hS₀ : ∀ rho : ℂ, rho ∈ S₀ ↔ (starRingEnd ℂ) rho ∈ S₀)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hbalance : (1 + sigma) / 2 < beta)
    (hnet : 0 < c - loss)
    (hloss : 0 < loss)
    (hmainCap : c < mainCap)
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
      (HasFarWindowEnergySeparation
          (fun m =>
            dynamicVisibleClusterPNTMain
                (selectedUniformGoodHeight
                  (actualCarlsonBalancedHeightExponent sigma) selection)
                S₀ (m : ℝ) /
              targetZeroPowerAmplitude beta (m : ℝ))
          (fun m =>
            dynamicVisibleClusterPNTMain
                (selectedUniformGoodHeight
                  (actualCarlsonBalancedHeightExponent sigma) selection)
                (S \ S₀) (m : ℝ) /
              targetZeroPowerAmplitude beta (m : ℝ))
          c loss mainCap →
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
  intro henergy
  apply hlower
  have hc : 0 ≤ c := by linarith
  exact
    henergy.toScaledWindowCardAdvantage
      hc hmainCap hloss
      (eventually_targetZeroPowerAmplitude_natural_pos beta)

end PrimeNumberTheorem
