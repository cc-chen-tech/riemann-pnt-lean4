import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonFiniteSeedGapTransferCluster
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonZeroSupportedFiniteCapture

/-!
# Zero-supported finite seeded Carlson selector

This is the finite-seed transfer-cluster construction with one additional
certificate: every newly adjoined member is a nontrivial zeta zero.  No
zero-membership assumption is imposed on the seed itself.
-/

namespace PrimeNumberTheorem

open Complex

/-- A conjugation-stable finite seed with an outside real-part cap extends to
a transfer cluster whose difference from the seed consists entirely of
nontrivial zeta zeros. -/
theorem exists_zeroSupportedExtension_actualCarlsonFiniteSeedGapTransferCluster
    {S₀ : Finset ℂ} {sigma beta c q : ℝ}
    (hS₀ : ∀ rho : ℂ, rho ∈ S₀ ↔ (starRingEnd ℂ) rho ∈ S₀)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hqC : q < c)
    (hcap : OutsideClusterRealPartCap S₀ beta) :
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
          (sigma := sigma) beta S < c - q := by
  rcases
      exists_conjugationStable_zeroSupported_boundarySupported_actualCarlsonOutsideClusterBoundaryMass_two_mul_lt_gap
        hhalf hone hqC with
    ⟨S₁, hS₁, hS₁Zero, hS₁Boundary, hgap⟩
  let S :=
    actualCarlsonAdjoinRealOrdinateZeros (S₁ ∪ S₀)
  have hUnion :
      ∀ rho : ℂ,
        rho ∈ S₁ ∪ S₀ ↔ (starRingEnd ℂ) rho ∈ S₁ ∪ S₀ := by
    intro rho
    simp only [Finset.mem_union]
    exact or_congr (hS₁ rho) (hS₀ rho)
  have hS :
      ∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S :=
    actualCarlsonAdjoinRealOrdinateZeros_conjugationStable
      (S₁ ∪ S₀) hUnion
  have hseed : ∀ rho ∈ S₀, rho ∈ S := by
    intro rho hrho
    exact Finset.mem_union_left _
      (Finset.mem_union_right S₁ hrho)
  have hcapS : OutsideClusterRealPartCap S beta := by
    intro rho hzero hout
    apply hcap rho hzero
    intro hrho
    exact hout (hseed rho hrho)
  have hzeroExtension :
      ∀ rho ∈ S \ S₀,
        RiemannHypothesis.IsNontrivialZero rho := by
    intro rho hrho
    have hmemS : rho ∈ S := (Finset.mem_sdiff.mp hrho).1
    have houtSeed : rho ∉ S₀ := (Finset.mem_sdiff.mp hrho).2
    have hrho' :
        rho ∈ (S₁ ∪ S₀) ∪ realOrdinateNontrivialZerosFinset 0 := by
      simpa [S, actualCarlsonAdjoinRealOrdinateZeros] using hmemS
    rcases Finset.mem_union.mp hrho' with hUnionMem | hReal
    · rcases Finset.mem_union.mp hUnionMem with hBoundary | hSeed
      · exact hS₁Zero rho hBoundary
      · exact False.elim (houtSeed hSeed)
    · exact
        (mem_nontrivialZerosFinset.mp
          (mem_realOrdinateNontrivialZerosFinset.mp hReal).1).1
  have hsupport :
      ∀ rho ∈ S,
        rho ∉ S₀ →
          rho ∉ realOrdinateNontrivialZerosFinset 0 →
            rho.re = beta := by
    intro rho hrho houtSeed houtReal
    have hrho' :
        rho ∈ (S₁ ∪ S₀) ∪ realOrdinateNontrivialZerosFinset 0 := by
      simpa [S, actualCarlsonAdjoinRealOrdinateZeros] using hrho
    rcases Finset.mem_union.mp hrho' with hUnionMem | hReal
    · rcases Finset.mem_union.mp hUnionMem with hBoundary | hSeed
      · exact hS₁Boundary rho hBoundary
      · exact False.elim (houtSeed hSeed)
    · exact False.elim (houtReal hReal)
  have hreHigh :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
          actualCarlsonPositiveZeroRealPart index ≤ beta := by
    intro index hout
    have houtUnion :
        actualCarlsonPositiveZero index ∉ S₁ ∪ S₀ := by
      intro hin
      exact hout (Finset.mem_union_left _ hin)
    have houtSeed :
        actualCarlsonPositiveZero index ∉ S₀ := by
      intro hin
      exact houtUnion (Finset.mem_union_right S₁ hin)
    exact hcap.actualCarlsonPositiveZeroRealPart_le index houtSeed
  have hreReal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta := by
    intro rho hrho
    have hempty :
        realOrdinateNontrivialZerosOutsideClusterFinset 0 S = ∅ :=
      realOrdinateNontrivialZerosOutsideClusterFinset_adjoin_eq_empty
        (S₁ ∪ S₀)
    rw [hempty] at hrho
    simp at hrho
  have hUnionMass :
      actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta (S₁ ∪ S₀) ≤
        actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S₁ := by
    apply actualCarlsonOutsideClusterBoundaryMass_antitone hhalf hone
    intro rho hrho
    exact Finset.mem_union_left _ hrho
  have hAdjoinMass :
      actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S ≤
        actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta (S₁ ∪ S₀) :=
    actualCarlsonOutsideClusterBoundaryMass_adjoinRealOrdinate_le
      (S₁ ∪ S₀) hhalf hone
  refine
    ⟨S, hseed, hS, hcapS, hzeroExtension, hsupport,
      hreHigh, hreReal, ?_⟩
  linarith

end PrimeNumberTheorem
