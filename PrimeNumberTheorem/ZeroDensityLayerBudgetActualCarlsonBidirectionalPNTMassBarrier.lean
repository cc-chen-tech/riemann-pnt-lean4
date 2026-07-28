import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonZeroSupportedCoefficientMassBidirectionalPNTTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonZeroSupportedSelectorBudgetAlternative

/-!
# Mass barrier inside the bidirectional actual-PNT certificate

When the seed outside boundary mass is at least `c / 2`, the same selected
cluster that carries the upper/lower actual-PNT transfer package necessarily
has extension coefficient mass at least `loss`.  Hence the strict
coefficient-mass premise of the lower branch cannot hold for that package.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- A zero-supported bidirectional actual-PNT certificate selected above the
half-coefficient seed threshold carries an explicit lower bound on its
extension coefficient mass. -/
theorem
    exists_zeroSupportedActualCarlsonBidirectionalPNTCertificate_with_extensionMassBarrier
    {S₀ : Finset ℂ} {sigma beta c loss : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hS₀ : ∀ rho : ℂ, rho ∈ S₀ ↔ (starRingEnd ℂ) rho ∈ S₀)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hbalance : (1 + sigma) / 2 < beta)
    (hnet : 0 < c - loss)
    (hcap : OutsideClusterRealPartCap S₀ beta)
    (hseedOutside :
      c / 2 ≤ actualCarlsonOutsideClusterBoundaryMass
        (sigma := sigma) beta S₀) :
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
      loss ≤ finiteVisibleClusterCoefficientMass (S \ S₀) ∧
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
      exists_zeroSupportedActualCarlsonFiniteSeedCoefficientMassBidirectionalPNTCanonicalSharpRealTransfer
        selection hS₀ hhalf hone hbalance hnet hcap with
    ⟨rate, S, hrate, hrateOne, hupper, hcontains, hq, hstable,
      hcapS, hzero, hsupport, hreHigh, hreReal, hgap, hlower⟩
  have hsub : S₀ ⊆ S := by
    intro rho hrho
    exact hcontains rho hrho
  have hstableExtension :
      ∀ rho : ℂ,
        rho ∈ S \ S₀ ↔ (starRingEnd ℂ) rho ∈ S \ S₀ :=
    finiteSeedExtension_sdiff_conjugationStable hS₀ hstable
  have hmass :
      loss ≤ finiteVisibleClusterCoefficientMass (S \ S₀) :=
    actualCarlsonFiniteExtensionCoefficientMass_ge_loss_of_halfCoefficient_le_seedOutside
      hsub hhalf hone hnet hseedOutside hstableExtension hzero hgap
  exact
    ⟨rate, S, hrate, hrateOne, hupper, hcontains, hq, hstable,
      hcapS, hzero, hsupport, hreHigh, hreReal, hgap, hmass, hlower⟩

/-- In the high-seed regime, the strict coefficient-mass trigger attached to
the selected bidirectional certificate is impossible. -/
theorem
    zeroSupportedActualCarlsonBidirectionalPNT_massTrigger_impossible
    {sigma beta c loss : ℝ} {S₀ S : Finset ℂ}
    (hsub : S₀ ⊆ S)
    (hS₀ : ∀ rho : ℂ, rho ∈ S₀ ↔ (starRingEnd ℂ) rho ∈ S₀)
    (hS : ∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hnet : 0 < c - loss)
    (hseedOutside :
      c / 2 ≤ actualCarlsonOutsideClusterBoundaryMass
        (sigma := sigma) beta S₀)
    (hzero :
      ∀ rho ∈ S \ S₀,
        RiemannHypothesis.IsNontrivialZero rho)
    (hgap :
      2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S <
        (c - loss) - (c - loss) / 2) :
    ¬ finiteVisibleClusterCoefficientMass (S \ S₀) < loss := by
  have hstableExtension :=
    finiteSeedExtension_sdiff_conjugationStable hS₀ hS
  have hmass :=
    actualCarlsonFiniteExtensionCoefficientMass_ge_loss_of_halfCoefficient_le_seedOutside
      hsub hhalf hone hnet hseedOutside hstableExtension hzero hgap
  exact not_lt_of_ge hmass

end PrimeNumberTheorem
