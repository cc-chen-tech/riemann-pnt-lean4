import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonOutsideClusterBoundaryLimit

/-!
# Visible-cluster capture of Carlson boundary mass

Enlarging the visible finite cluster can only remove terms from the
outside-cluster boundary mass.  If every indexed positive zero on
`Re rho = beta` is included in the cluster, that mass vanishes exactly.
-/

namespace PrimeNumberTheorem

open scoped BigOperators

noncomputable section

/-- The summands defining the actual outside-cluster Carlson boundary mass are
summable. -/
theorem summable_actualCarlsonOutsideClusterBoundaryTerm
    {sigma beta : ℝ} (S : Finset ℂ)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1) :
    Summable
      (fun index : ActualCarlsonPositiveZeroIndex sigma =>
        if actualCarlsonOutsideClusterRealPart beta S index = beta then
          actualCarlsonOutsideClusterWeight S index
        else 0) := by
  refine Summable.of_nonneg_of_le ?_ ?_
    (summable_actualCarlsonOutsideClusterWeight S hhalf hone)
  · intro index
    by_cases heq :
        actualCarlsonOutsideClusterRealPart beta S index = beta
    · simp [heq, actualCarlsonOutsideClusterWeight_nonneg S index]
    · simp [heq]
  · intro index
    by_cases heq :
        actualCarlsonOutsideClusterRealPart beta S index = beta
    · simp [heq]
    · simp [heq, actualCarlsonOutsideClusterWeight_nonneg S index]

/-- Boundary mass is antitone in the visible cluster: enlarging the cluster can
only decrease the outside-cluster coefficient. -/
theorem actualCarlsonOutsideClusterBoundaryMass_antitone
    {sigma beta : ℝ} {S T : Finset ℂ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hST : S ⊆ T) :
    actualCarlsonOutsideClusterBoundaryMass
        (sigma := sigma) beta T ≤
      actualCarlsonOutsideClusterBoundaryMass
        (sigma := sigma) beta S := by
  unfold actualCarlsonOutsideClusterBoundaryMass weightedPowerBoundaryMass
  apply Summable.tsum_le_tsum
  · intro index
    by_cases hmemT : actualCarlsonPositiveZero index ∈ T
    · have hnonneg :
          0 ≤
            (if actualCarlsonOutsideClusterRealPart beta S index = beta then
              actualCarlsonOutsideClusterWeight S index
            else 0) := by
          by_cases heq :
              actualCarlsonOutsideClusterRealPart beta S index = beta
          · simp [heq, actualCarlsonOutsideClusterWeight_nonneg S index]
          · simp [heq]
      simpa [actualCarlsonOutsideClusterWeight,
        actualCarlsonOutsideClusterRealPart, hmemT] using hnonneg
    · have hmemS : actualCarlsonPositiveZero index ∉ S := by
        intro hmem
        exact hmemT (hST hmem)
      simp [actualCarlsonOutsideClusterWeight,
        actualCarlsonOutsideClusterRealPart, hmemT, hmemS]
  · exact
      summable_actualCarlsonOutsideClusterBoundaryTerm T hhalf hone
  · exact
      summable_actualCarlsonOutsideClusterBoundaryTerm S hhalf hone

/-- If the visible cluster contains every indexed positive zero on
`Re rho = beta`, then the outside-cluster boundary mass is exactly zero. -/
theorem actualCarlsonOutsideClusterBoundaryMass_eq_zero_of_boundary_captured
    {sigma beta : ℝ} (S : Finset ℂ)
    (hcapture :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZeroRealPart index = beta →
          actualCarlsonPositiveZero index ∈ S) :
    actualCarlsonOutsideClusterBoundaryMass
        (sigma := sigma) beta S = 0 := by
  unfold actualCarlsonOutsideClusterBoundaryMass weightedPowerBoundaryMass
  have hzero :
      (fun index : ActualCarlsonPositiveZeroIndex sigma =>
        if actualCarlsonOutsideClusterRealPart beta S index = beta then
          actualCarlsonOutsideClusterWeight S index
        else 0) =
      (fun _ => 0) := by
    funext index
    by_cases hmem : actualCarlsonPositiveZero index ∈ S
    · simp [actualCarlsonOutsideClusterWeight,
        actualCarlsonOutsideClusterRealPart, hmem]
    · have hne :
          actualCarlsonPositiveZeroRealPart index ≠ beta := by
        intro heq
        exact hmem (hcapture index heq)
      simp [actualCarlsonOutsideClusterWeight,
        actualCarlsonOutsideClusterRealPart, hmem, hne]
  rw [hzero]
  simp

end

end PrimeNumberTheorem
