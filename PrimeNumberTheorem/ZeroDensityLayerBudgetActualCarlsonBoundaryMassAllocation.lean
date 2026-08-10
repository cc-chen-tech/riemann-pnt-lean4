import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBoundaryMassFiniteCapture

/-!
# Exact allocation of actual Carlson boundary mass

The positive-zero boundary coefficient mass splits exactly into the part
captured by a visible cluster and the part remaining outside it.  This module
keeps the split at the Carlson index level.  It therefore makes no unproved
identification between indexed mass and a finite sum over distinct complex
zeros.
-/

namespace PrimeNumberTheorem

open scoped BigOperators

noncomputable section

/-- The full indexed positive-zero coefficient mass on `Re rho = beta`. -/
def actualCarlsonTotalBoundaryMass
    {sigma : ℝ} (beta : ℝ) : ℝ :=
  ∑' index : ActualCarlsonPositiveZeroIndex sigma,
    actualCarlsonBoundaryTerm beta index

/-- The boundary coefficient term captured by a visible finite cluster. -/
def actualCarlsonCapturedBoundaryTerm
    {sigma : ℝ} (beta : ℝ) (S : Finset ℂ)
    (index : ActualCarlsonPositiveZeroIndex sigma) : ℝ :=
  if actualCarlsonPositiveZeroRealPart index = beta then
    if actualCarlsonPositiveZero index ∈ S then
      actualCarlsonPositiveZeroWeight index
    else 0
  else 0

/-- The total indexed boundary coefficient mass captured by a cluster. -/
def actualCarlsonCapturedBoundaryMass
    {sigma : ℝ} (beta : ℝ) (S : Finset ℂ) : ℝ :=
  ∑' index : ActualCarlsonPositiveZeroIndex sigma,
    actualCarlsonCapturedBoundaryTerm beta S index

theorem actualCarlsonCapturedBoundaryTerm_nonneg
    {sigma beta : ℝ} (S : Finset ℂ)
    (index : ActualCarlsonPositiveZeroIndex sigma) :
    0 ≤ actualCarlsonCapturedBoundaryTerm beta S index := by
  by_cases hre : actualCarlsonPositiveZeroRealPart index = beta
  · by_cases hmem : actualCarlsonPositiveZero index ∈ S
    · simp [actualCarlsonCapturedBoundaryTerm, hre, hmem,
        actualCarlsonPositiveZeroWeight_nonneg index]
    · simp [actualCarlsonCapturedBoundaryTerm, hre, hmem]
  · simp [actualCarlsonCapturedBoundaryTerm, hre]

theorem summable_actualCarlsonCapturedBoundaryTerm
    {sigma beta : ℝ} (S : Finset ℂ)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1) :
    Summable
      (fun index : ActualCarlsonPositiveZeroIndex sigma =>
        actualCarlsonCapturedBoundaryTerm beta S index) := by
  refine Summable.of_nonneg_of_le
    (fun index =>
      actualCarlsonCapturedBoundaryTerm_nonneg S index) ?_
    (summable_actualCarlsonBoundaryTerm (beta := beta) hhalf hone)
  intro index
  by_cases hre : actualCarlsonPositiveZeroRealPart index = beta
  · by_cases hmem : actualCarlsonPositiveZero index ∈ S
    · simp [actualCarlsonCapturedBoundaryTerm, actualCarlsonBoundaryTerm,
        hre, hmem]
    · simp [actualCarlsonCapturedBoundaryTerm, actualCarlsonBoundaryTerm,
        hre, hmem, actualCarlsonPositiveZeroWeight_nonneg index]
  · simp [actualCarlsonCapturedBoundaryTerm, actualCarlsonBoundaryTerm, hre]

theorem actualCarlsonCapturedBoundaryMass_nonneg
    {sigma beta : ℝ} (S : Finset ℂ) :
    0 ≤ actualCarlsonCapturedBoundaryMass
        (sigma := sigma) beta S := by
  unfold actualCarlsonCapturedBoundaryMass
  exact
    tsum_nonneg
      (fun index =>
        actualCarlsonCapturedBoundaryTerm_nonneg S index)

/-- Exact partition of the full indexed boundary mass into captured and
outside-cluster terms. -/
theorem actualCarlsonTotalBoundaryMass_eq_captured_add_outside
    {sigma beta : ℝ} (S : Finset ℂ)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1) :
    actualCarlsonTotalBoundaryMass (sigma := sigma) beta =
      actualCarlsonCapturedBoundaryMass (sigma := sigma) beta S +
        actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S := by
  unfold actualCarlsonTotalBoundaryMass
  unfold actualCarlsonCapturedBoundaryMass
  unfold actualCarlsonOutsideClusterBoundaryMass weightedPowerBoundaryMass
  rw [← (summable_actualCarlsonCapturedBoundaryTerm S hhalf hone).tsum_add
    (summable_actualCarlsonOutsideClusterBoundaryTerm S hhalf hone)]
  apply tsum_congr
  intro index
  by_cases hre : actualCarlsonPositiveZeroRealPart index = beta
  · by_cases hmem : actualCarlsonPositiveZero index ∈ S
    · simp [actualCarlsonBoundaryTerm, actualCarlsonCapturedBoundaryTerm,
        actualCarlsonOutsideClusterWeight,
        actualCarlsonOutsideClusterRealPart, hre, hmem]
    · simp [actualCarlsonBoundaryTerm, actualCarlsonCapturedBoundaryTerm,
        actualCarlsonOutsideClusterWeight,
        actualCarlsonOutsideClusterRealPart, hre, hmem]
  · by_cases hmem : actualCarlsonPositiveZero index ∈ S
    · simp [actualCarlsonBoundaryTerm, actualCarlsonCapturedBoundaryTerm,
        actualCarlsonOutsideClusterWeight,
        actualCarlsonOutsideClusterRealPart, hre, hmem]
    · simp [actualCarlsonBoundaryTerm, actualCarlsonCapturedBoundaryTerm,
        actualCarlsonOutsideClusterWeight,
        actualCarlsonOutsideClusterRealPart, hre, hmem]

/-- Any simultaneous strict budgets on captured and outside boundary mass
force the corresponding strict budget on the total boundary layer. -/
theorem actualCarlsonTotalBoundaryMass_lt_add_of_captured_lt_of_outside_lt
    {sigma beta capturedAllowance outsideAllowance : ℝ}
    (S : Finset ℂ)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hcaptured :
      actualCarlsonCapturedBoundaryMass
          (sigma := sigma) beta S < capturedAllowance)
    (houtside :
      actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S < outsideAllowance) :
    actualCarlsonTotalBoundaryMass (sigma := sigma) beta <
      capturedAllowance + outsideAllowance := by
  rw [actualCarlsonTotalBoundaryMass_eq_captured_add_outside S hhalf hone]
  exact add_lt_add hcaptured houtside

end

end PrimeNumberTheorem
