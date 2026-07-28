import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonFiniteSeedZeroSupportedSelector
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonConjugateFiniteSeedBarrier

/-!
# Zero-supported selector budget alternative

The zero-supported finite-seed selector always supplies the canonical Carlson
outside-mass gap.  If the seed already has outside boundary mass at least
`c / 2`, conjugation forces the selected extension to spend at least `loss`
in finite coefficient mass.

This isolates the remaining obstruction in the coefficient-mass budget.
-/

namespace PrimeNumberTheorem

/-- Above the half-coefficient seed threshold, every conjugation-stable,
zero-supported extension satisfying the canonical outside gap has finite
coefficient mass at least `loss`. -/
theorem
    actualCarlsonFiniteExtensionCoefficientMass_ge_loss_of_halfCoefficient_le_seedOutside
    {sigma beta c loss : ℝ} {S₀ S : Finset ℂ}
    (hsub : S₀ ⊆ S)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hnet : 0 < c - loss)
    (hseedOutside :
      c / 2 ≤ actualCarlsonOutsideClusterBoundaryMass
        (sigma := sigma) beta S₀)
    (hstable :
      ∀ rho : ℂ,
        rho ∈ S \ S₀ ↔ (starRingEnd ℂ) rho ∈ S \ S₀)
    (hzero :
      ∀ rho ∈ S \ S₀,
        RiemannHypothesis.IsNontrivialZero rho)
    (hgap :
      2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S <
        (c - loss) - (c - loss) / 2) :
    loss ≤ finiteVisibleClusterCoefficientMass (S \ S₀) := by
  by_contra hmass
  have hadded :
      finiteVisibleClusterCoefficientMass (S \ S₀) < loss :=
    lt_of_not_ge hmass
  have hseedLt :=
    actualCarlsonSeedOutside_lt_half_localCoefficient_of_conjugateCanonicalExtension
      hsub hhalf hone hnet hstable hzero hadded hgap
  linarith

/-- The zero-supported seeded selector realizes the following quantitative
alternative: at or above the half-coefficient seed threshold it still
achieves every structural and Carlson-gap output, but its extension
coefficient mass is necessarily at least `loss`. -/
theorem
    exists_zeroSupportedActualCarlsonFiniteSeedCanonicalGap_with_extensionMass_ge
    {S₀ : Finset ℂ} {sigma beta c loss : ℝ}
    (hS₀ : ∀ rho : ℂ, rho ∈ S₀ ↔ (starRingEnd ℂ) rho ∈ S₀)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hnet : 0 < c - loss)
    (hcap : OutsideClusterRealPartCap S₀ beta)
    (hseedOutside :
      c / 2 ≤ actualCarlsonOutsideClusterBoundaryMass
        (sigma := sigma) beta S₀) :
    ∃ S : Finset ℂ,
      (∀ rho ∈ S₀, rho ∈ S) ∧
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
      loss ≤ finiteVisibleClusterCoefficientMass (S \ S₀) := by
  have hselectorGap : 0 < (c - loss) / 2 := by
    linarith
  rcases
      exists_zeroSupportedExtension_actualCarlsonFiniteSeedGapTransferCluster
        (sigma := sigma) (beta := beta)
        (c := (c - loss) / 2) (q := 0)
        hS₀ hhalf hone hselectorGap hcap with
    ⟨S, hseed, hstableS, hcapS, hzero, hsupport,
      hreHigh, hreReal, hgap⟩
  have hsub : S₀ ⊆ S := by
    intro rho hrho
    exact hseed rho hrho
  have hstableExtension :
      ∀ rho : ℂ,
        rho ∈ S \ S₀ ↔ (starRingEnd ℂ) rho ∈ S \ S₀ :=
    finiteSeedExtension_sdiff_conjugationStable hS₀ hstableS
  have hcanonicalGap :
      2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S <
        (c - loss) - (c - loss) / 2 := by
    linarith
  have hmass :=
    actualCarlsonFiniteExtensionCoefficientMass_ge_loss_of_halfCoefficient_le_seedOutside
      hsub hhalf hone hnet hseedOutside
      hstableExtension hzero hcanonicalGap
  exact
    ⟨S, hseed, hstableS, hcapS, hzero, hsupport,
      hreHigh, hreReal, hcanonicalGap, hmass⟩

end PrimeNumberTheorem
