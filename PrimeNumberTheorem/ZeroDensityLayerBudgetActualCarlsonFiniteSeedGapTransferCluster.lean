import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonFiniteGapTransferCluster
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTHybridCanonicalOutsideClusterCapTransfer

/-!
# Finite seeded Carlson transfer clusters

A finite conjugation-stable seed cluster may contain the exceptional or
rightmost zeros.  A zeta-level real-part cap is required only outside that
seed.  The resulting transfer cluster contains the seed, captures enough
Carlson boundary mass, and absorbs every real-ordinate zero.
-/

namespace PrimeNumberTheorem

open Complex

/-- A zeta-level outside-cluster cap applies directly to every indexed actual
Carlson positive zero outside the same cluster. -/
theorem OutsideClusterRealPartCap.actualCarlsonPositiveZeroRealPart_le
    {S : Finset ℂ} {sigma beta : ℝ}
    (hcap : OutsideClusterRealPartCap S beta)
    (index : ActualCarlsonPositiveZeroIndex sigma)
    (hout : actualCarlsonPositiveZero index ∉ S) :
    actualCarlsonPositiveZeroRealPart index ≤ beta := by
  simpa [actualCarlsonPositiveZeroRealPart] using
    hcap (actualCarlsonPositiveZero index)
      (actualCarlsonPositiveZero_spec index).1 hout

/-- For every strict coefficient gap `q < c`, a finite conjugation-stable seed
cluster with a zeta-level outside cap extends to a finite transfer cluster.
The extension keeps the seed, absorbs all real-ordinate zeros, and preserves
the required Carlson boundary-mass gap. -/
theorem exists_actualCarlsonFiniteSeedGapTransferCluster
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
      (∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
          actualCarlsonPositiveZeroRealPart index ≤ beta) ∧
      (∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) ∧
      2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S < c - q := by
  rcases
      exists_conjugationStable_actualCarlsonOutsideClusterBoundaryMass_two_mul_lt_gap
        hhalf hone hqC with
    ⟨S₁, hS₁, hgap⟩
  let S :=
    actualCarlsonAdjoinRealOrdinateZeros (S₁ ∪ S₀)
  have hUnion :
      ∀ rho : ℂ,
        rho ∈ S₁ ∪ S₀ ↔ (starRingEnd ℂ) rho ∈ S₁ ∪ S₀ := by
    intro rho
    simp only [Finset.mem_union]
    exact or_congr (hS₁ rho) (hS₀ rho)
  have hS :
      ∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S := by
    exact actualCarlsonAdjoinRealOrdinateZeros_conjugationStable
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
        realOrdinateNontrivialZerosOutsideClusterFinset 0 S = ∅ := by
      exact
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
          (sigma := sigma) beta (S₁ ∪ S₀) := by
    exact
      actualCarlsonOutsideClusterBoundaryMass_adjoinRealOrdinate_le
        (S₁ ∪ S₀) hhalf hone
  refine ⟨S, hseed, hS, hcapS, hreHigh, hreReal, ?_⟩
  linarith

end PrimeNumberTheorem
