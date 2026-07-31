import PrimeNumberTheorem.ZeroDensityLayerBudgetAutomaticOptimalHeightCarlsonBridge
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualClassicalDyadicCarlsonBalancedClosedFormFullPNT

/-!
# Automatic actual-grid package for the balanced dyadic Carlson PNT bound

The existing selected-height Carlson theorem is transported to an actual
singleton-grid candidate with the identical balanced rate and good-height
selector.
-/

namespace PrimeNumberTheorem

open Filter Topology

/-- The balanced dyadic Carlson closed-form PNT theorem, now packaged on an
actual automatically selected singleton-grid height. -/
theorem exists_automaticActualGrid_balancedDyadicCarlsonClosedFormFullPNT :
    ∃ b gapRate D : ℝ,
      0 < b ∧
      gapRate = classicalAdmissibleBalancedRate b / 2 ∧
      0 < gapRate ∧ 0 < D ∧
      IsCarlsonMovingDyadicLogPowerGap
        (classicalAdmissibleDyadicCarlsonGapWidth gapRate) ∧
      classicalAdmissibleVerifiedPNTDecayRate b = gapRate / 4 ∧
      ∀ selection : UniformNaturalPointGoodHeightSelection,
        ∃ grid : ActualPintzCarlsonGoodHeightRateGrid,
          grid.rates = {classicalAdmissibleBalancedRate b} ∧
          grid.baseRate = classicalAdmissibleBalancedRate b ∧
          grid.selection = selection ∧
          IsSelectedHeightDynamicZeroFree
            (actualPintzCarlsonRateCandidateHeight grid
              (classicalAdmissibleBalancedRate b))
            (classicalAdmissibleDyadicCarlsonGapWidth gapRate) ∧
          ∃ E eta C kappa : ℝ,
            0 ≤ E ∧ 0 < eta ∧ 0 ≤ C ∧ 0 < kappa ∧
            Tendsto
              (classicalDyadicCarlsonClosedFormFullPNTErrorMajorant
                b selection E eta C kappa D gapRate)
              atTop (nhds 0) ∧
            ∀ᶠ m : ℕ in atTop,
              |relativeChebyshevPsi0Error (m : ℝ)| ≤
                classicalDyadicCarlsonClosedFormFullPNTErrorMajorant
                  b selection E eta C kappa D gapRate m := by
  rcases
      exists_selectedBalancedClassicalAdmissibleDyadicCarlsonClosedFormFullPNTErrorMajorant
      with ⟨b, gapRate, D, hb, hgapRateEq, hgapRate, hD, hgap,
        hverified, hselected⟩
  refine ⟨b, gapRate, D, hb, hgapRateEq, hgapRate, hD, hgap,
    hverified, ?_⟩
  intro selection
  rcases hselected selection with
    ⟨hzeroFree, E, eta, C, kappa, hE, heta, hC, hkappa,
      hmajorant, herror⟩
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hparent : 0 < 2 * b := mul_pos (by norm_num) hb
  have hprod : (1 / 2 : ℝ) * (2 * b) = b := by ring
  let grid :=
    actualStrictMarginOptimalSingletonGrid
      (1 / 2 : ℝ) (2 * b) hhalf hparent selection
  have hzeroFree' :
      IsSelectedHeightDynamicZeroFree
        (selectedClassicalAdmissibleGoodHeight
          ((1 / 2 : ℝ) * (2 * b)) selection)
        (classicalAdmissibleDyadicCarlsonGapWidth gapRate) := by
    simpa [hprod] using hzeroFree
  have hgridZeroFree :=
    isSelectedHeightDynamicZeroFree_actualStrictMarginOptimal_of_selectedClassical
      hhalf hparent selection hzeroFree'
  refine ⟨grid, ?_, ?_, ?_, ?_, E, eta, C, kappa,
    hE, heta, hC, hkappa, hmajorant, herror⟩
  · simp [grid]
  · simp [grid]
  · rfl
  · simpa [grid, hprod] using hgridZeroFree

end PrimeNumberTheorem
