import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBoundaryMassFiniteGapCapture

/-!
# Boundary-supported finite Carlson capture

The Carlson boundary mass depends only on cluster members lying on
`Re rho = beta`.  Filtering a cluster to that boundary therefore preserves
the mass exactly and yields a finite-gap capture with explicit support.
-/

namespace PrimeNumberTheorem

open Complex

/-- The part of a finite cluster lying on the target real-part boundary. -/
noncomputable def actualCarlsonBoundaryClusterPart
    (beta : ℝ) (S : Finset ℂ) : Finset ℂ :=
  S.filter fun rho => rho.re = beta

theorem mem_actualCarlsonBoundaryClusterPart
    {beta : ℝ} {S : Finset ℂ} {rho : ℂ} :
    rho ∈ actualCarlsonBoundaryClusterPart beta S ↔
      rho ∈ S ∧ rho.re = beta := by
  simp [actualCarlsonBoundaryClusterPart]

/-- Filtering a finite cluster to `Re rho = beta` leaves the actual Carlson
outside-cluster boundary mass unchanged. -/
theorem actualCarlsonOutsideClusterBoundaryMass_boundaryClusterPart
    {sigma beta : ℝ} (S : Finset ℂ) :
    actualCarlsonOutsideClusterBoundaryMass
        (sigma := sigma) beta
        (actualCarlsonBoundaryClusterPart beta S) =
      actualCarlsonOutsideClusterBoundaryMass
        (sigma := sigma) beta S := by
  unfold actualCarlsonOutsideClusterBoundaryMass
  unfold weightedPowerBoundaryMass
  apply tsum_congr
  intro index
  have hsub : beta - 1 ≠ beta := by linarith
  by_cases hmem : actualCarlsonPositiveZero index ∈ S
  · by_cases hre : actualCarlsonPositiveZeroRealPart index = beta
    · have hre' : (actualCarlsonPositiveZero index).re = beta := by
        simpa [actualCarlsonPositiveZeroRealPart] using hre
      simp [actualCarlsonBoundaryClusterPart,
        actualCarlsonOutsideClusterWeight,
        actualCarlsonOutsideClusterRealPart,
        hmem, hre, hre', hsub]
    · have hre' : (actualCarlsonPositiveZero index).re ≠ beta := by
        simpa [actualCarlsonPositiveZeroRealPart] using hre
      simp [actualCarlsonBoundaryClusterPart,
        actualCarlsonOutsideClusterWeight,
        actualCarlsonOutsideClusterRealPart,
        hmem, hre, hre', hsub]
  · simp [actualCarlsonBoundaryClusterPart,
      actualCarlsonOutsideClusterWeight,
      actualCarlsonOutsideClusterRealPart,
      actualCarlsonPositiveZeroRealPart, hmem]

/-- Boundary filtering preserves conjugation stability. -/
theorem actualCarlsonBoundaryClusterPart_conjugationStable
    {beta : ℝ} {S : Finset ℂ}
    (hS : ∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S)
    (rho : ℂ) :
    rho ∈ actualCarlsonBoundaryClusterPart beta S ↔
      (starRingEnd ℂ) rho ∈ actualCarlsonBoundaryClusterPart beta S := by
  simp only [mem_actualCarlsonBoundaryClusterPart]
  rw [hS rho]
  simp

/-- Every member of the filtered cluster lies on the target boundary. -/
theorem actualCarlsonBoundaryClusterPart_realPart
    {beta : ℝ} {S : Finset ℂ} {rho : ℂ}
    (hrho : rho ∈ actualCarlsonBoundaryClusterPart beta S) :
    rho.re = beta :=
  (mem_actualCarlsonBoundaryClusterPart.mp hrho).2

/-- Every strict coefficient gap admits a finite conjugation-stable Carlson
capture supported entirely on `Re rho = beta`. -/
theorem
    exists_conjugationStable_boundarySupported_actualCarlsonOutsideClusterBoundaryMass_two_mul_lt_gap
    {sigma beta c q : ℝ}
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hqC : q < c) :
    ∃ S : Finset ℂ,
      (∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S) ∧
      (∀ rho ∈ S, rho.re = beta) ∧
      2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S < c - q := by
  rcases
      exists_conjugationStable_actualCarlsonOutsideClusterBoundaryMass_two_mul_lt_gap
        hhalf hone hqC with
    ⟨S, hS, hgap⟩
  refine
    ⟨actualCarlsonBoundaryClusterPart beta S,
      actualCarlsonBoundaryClusterPart_conjugationStable hS,
      ?_, ?_⟩
  · intro rho hrho
    exact actualCarlsonBoundaryClusterPart_realPart hrho
  · rw [actualCarlsonOutsideClusterBoundaryMass_boundaryClusterPart]
    exact hgap

end PrimeNumberTheorem
