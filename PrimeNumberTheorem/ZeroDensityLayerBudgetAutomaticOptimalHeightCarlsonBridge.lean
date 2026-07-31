import PrimeNumberTheorem.ZeroDensityLayerBudgetAutomaticOptimalStrictMarginPNTGrid
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualClassicalDyadicCarlsonGap

/-!
# Bridge from the automatic optimal actual grid to classical Carlson heights

The automatic actual candidate and the existing classical admissible selected
height use the same selector and base. They therefore agree after the actual
candidate's finite fallback range, allowing the existing dyadic Carlson chain
to be reused without duplicating its analytic proofs.
-/

namespace PrimeNumberTheorem

open Filter Topology

/-- A dynamic selected-height zero-free property is invariant under eventual
equality of the height schedules on natural samples. -/
theorem IsSelectedHeightDynamicZeroFree.congr_eventually
    {H K : ℝ → ℝ} {delta : ℕ → ℝ}
    (hHK : ∀ᶠ m : ℕ in atTop, H (m : ℝ) = K (m : ℝ))
    (hzeroFree : IsSelectedHeightDynamicZeroFree H delta) :
    IsSelectedHeightDynamicZeroFree K delta := by
  unfold IsSelectedHeightDynamicZeroFree at hzeroFree ⊢
  filter_upwards [hHK, hzeroFree] with m hmEq hm
  intro rho hzero him himHeight
  apply hm rho hzero him
  simpa [hmEq] using himHeight

/-- Eventually the actual candidate in the automatic optimal singleton grid
is exactly the classical admissible selected good height at parameter
`theta * b`. -/
theorem eventually_actualStrictMarginOptimalCandidateHeight_eq_selectedClassical
    {theta b : ℝ} (htheta : 0 < theta) (hb : 0 < b)
    (selection : UniformNaturalPointGoodHeightSelection) :
    ∀ᶠ x : ℝ in atTop,
      actualPintzCarlsonRateCandidateHeight
          (actualStrictMarginOptimalSingletonGrid
            theta b htheta hb selection)
          (classicalAdmissibleBalancedRate (theta * b)) x =
        selectedClassicalAdmissibleGoodHeight
          (theta * b) selection x := by
  have hrate : 0 < classicalAdmissibleBalancedRate (theta * b) :=
    classicalAdmissibleBalancedRate_pos (mul_pos htheta hb)
  have hlarge :
      ∀ᶠ x : ℝ in atTop,
        9 ≤ pintzCarlsonHeight
          (classicalAdmissibleBalancedRate (theta * b)) x :=
    (tendsto_atTop.1 (tendsto_pintzCarlsonHeight_atTop hrate)) 9
  filter_upwards [hlarge] with x hx
  simp [actualPintzCarlsonRateCandidateHeight,
    actualStrictMarginOptimalSingletonGrid,
    selectedClassicalAdmissibleGoodHeight, hx]

/-- Natural-point form of the automatic/classical selected-height identity. -/
theorem eventually_nat_actualStrictMarginOptimalCandidateHeight_eq_selectedClassical
    {theta b : ℝ} (htheta : 0 < theta) (hb : 0 < b)
    (selection : UniformNaturalPointGoodHeightSelection) :
    ∀ᶠ m : ℕ in atTop,
      actualPintzCarlsonRateCandidateHeight
          (actualStrictMarginOptimalSingletonGrid
            theta b htheta hb selection)
          (classicalAdmissibleBalancedRate (theta * b)) (m : ℝ) =
        selectedClassicalAdmissibleGoodHeight
          (theta * b) selection (m : ℝ) :=
  tendsto_natCast_atTop_atTop.eventually
    (eventually_actualStrictMarginOptimalCandidateHeight_eq_selectedClassical
      htheta hb selection)

/-- The finite multiplicity-weighted zero sum is therefore the same at both
height presentations. -/
theorem eventually_finiteZeroSum_actualStrictMarginOptimal_eq_selectedClassical
    {theta b : ℝ} (htheta : 0 < theta) (hb : 0 < b)
    (selection : UniformNaturalPointGoodHeightSelection) :
    ∀ᶠ m : ℕ in atTop,
      finiteNontrivialZeroSumWithMultiplicity (m : ℝ)
          (actualPintzCarlsonRateCandidateHeight
            (actualStrictMarginOptimalSingletonGrid
              theta b htheta hb selection)
            (classicalAdmissibleBalancedRate (theta * b)) (m : ℝ)) =
        finiteNontrivialZeroSumWithMultiplicity (m : ℝ)
          (selectedClassicalAdmissibleGoodHeight
            (theta * b) selection (m : ℝ)) := by
  filter_upwards
      [eventually_nat_actualStrictMarginOptimalCandidateHeight_eq_selectedClassical
        htheta hb selection] with m hm
  rw [hm]

/-- The complete actual finite zero-tail norm is invariant under the same
eventual schedule identity. -/
theorem eventually_dynamicFullPNTZeroTailNorm_actualStrictMarginOptimal_eq_selectedClassical
    {theta b : ℝ} (htheta : 0 < theta) (hb : 0 < b)
    (selection : UniformNaturalPointGoodHeightSelection) :
    ∀ᶠ m : ℕ in atTop,
      dynamicFullPNTZeroTailNorm
          (actualPintzCarlsonRateCandidateHeight
            (actualStrictMarginOptimalSingletonGrid
              theta b htheta hb selection)
            (classicalAdmissibleBalancedRate (theta * b))) (m : ℝ) =
        dynamicFullPNTZeroTailNorm
          (selectedClassicalAdmissibleGoodHeight
            (theta * b) selection) (m : ℝ) := by
  filter_upwards
      [eventually_nat_actualStrictMarginOptimalCandidateHeight_eq_selectedClassical
        htheta hb selection] with m hm
  unfold dynamicFullPNTZeroTailNorm
  rw [hm]

/-- The actual explicit-formula remainder is also evaluated at the same
eventual height. -/
theorem eventually_actualPNTExplicitFormulaRelativeRemainder_actualStrictMarginOptimal_eq_selectedClassical
    {theta b : ℝ} (htheta : 0 < theta) (hb : 0 < b)
    (selection : UniformNaturalPointGoodHeightSelection) :
    ∀ᶠ m : ℕ in atTop,
      actualPNTExplicitFormulaRelativeRemainder
          (actualPintzCarlsonRateCandidateHeight
            (actualStrictMarginOptimalSingletonGrid
              theta b htheta hb selection)
            (classicalAdmissibleBalancedRate (theta * b))) (m : ℝ) =
        actualPNTExplicitFormulaRelativeRemainder
          (selectedClassicalAdmissibleGoodHeight
            (theta * b) selection) (m : ℝ) := by
  filter_upwards
      [eventually_nat_actualStrictMarginOptimalCandidateHeight_eq_selectedClassical
        htheta hb selection] with m hm
  unfold actualPNTExplicitFormulaRelativeRemainder
  rw [hm]

/-- Every dynamic zero-free predicate proved for the classical selected height
transfers to the automatic actual singleton-grid candidate. -/
theorem isSelectedHeightDynamicZeroFree_actualStrictMarginOptimal_of_selectedClassical
    {theta b : ℝ} {delta : ℕ → ℝ}
    (htheta : 0 < theta) (hb : 0 < b)
    (selection : UniformNaturalPointGoodHeightSelection)
    (hzeroFree : IsSelectedHeightDynamicZeroFree
      (selectedClassicalAdmissibleGoodHeight (theta * b) selection) delta) :
    IsSelectedHeightDynamicZeroFree
      (actualPintzCarlsonRateCandidateHeight
        (actualStrictMarginOptimalSingletonGrid
          theta b htheta hb selection)
        (classicalAdmissibleBalancedRate (theta * b))) delta := by
  have hEq : ∀ᶠ m : ℕ in atTop,
      selectedClassicalAdmissibleGoodHeight
          (theta * b) selection (m : ℝ) =
        actualPintzCarlsonRateCandidateHeight
          (actualStrictMarginOptimalSingletonGrid
            theta b htheta hb selection)
          (classicalAdmissibleBalancedRate (theta * b)) (m : ℝ) := by
    filter_upwards
        [eventually_nat_actualStrictMarginOptimalCandidateHeight_eq_selectedClassical
          htheta hb selection] with m hm
    exact hm.symm
  exact IsSelectedHeightDynamicZeroFree.congr_eventually hEq hzeroFree

end PrimeNumberTheorem
