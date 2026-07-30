import PrimeNumberTheorem.ZeroDensityLayerBudgetClassicalBalancedTruncationRate

open Filter Real Complex
open scoped Topology BigOperators

namespace PrimeNumberTheorem

lemma exists_selectedClassicalAdmissibleDyadicCarlsonQuantitativeMassMajorant_of_zeroFree
    {b gapRate : ℝ} (hb : 0 < b) (hgapRate : 0 < gapRate)
    (hzeroFree : ∀ selection : UniformNaturalPointGoodHeightSelection,
      IsSelectedHeightDynamicZeroFree
        (selectedClassicalAdmissibleGoodHeight b selection)
        (classicalAdmissibleDyadicCarlsonGapWidth gapRate)) :
    ∃ D : ℝ, 0 < D ∧
      Tendsto (classicalDyadicCarlsonSqrtLogMajorant D gapRate)
        atTop (nhds 0) ∧
      ∀ selection : UniformNaturalPointGoodHeightSelection,
        IsSelectedHeightDynamicZeroFree
          (selectedClassicalAdmissibleGoodHeight b selection)
          (classicalAdmissibleDyadicCarlsonGapWidth gapRate) ∧
        ∀ᶠ m : ℕ in atTop,
          actualSelectedHeightMovingCarlsonMiddleMass
              (selectedClassicalAdmissibleGoodHeight b selection)
              (classicalAdmissibleDyadicCarlsonGapWidth gapRate) m ≤
            actualSelectedHeightSevenEighthsLowMass
                (selectedClassicalAdmissibleGoodHeight b selection) m +
              classicalDyadicCarlsonSqrtLogMajorant D gapRate m ∧
          actualSelectedHeightMovingCarlsonStripMass
              (selectedClassicalAdmissibleGoodHeight b selection)
              (classicalAdmissibleDyadicCarlsonGapWidth gapRate) m ≤
            classicalDyadicCarlsonSqrtLogMajorant D gapRate m := by
  rcases exists_classicalAdmissibleDyadicCarlsonQuantitativeFixedAnchorMajorant
      hgapRate with ⟨D, hD, hfixed, hDzero⟩
  refine ⟨D, hD, hDzero, ?_⟩
  intro selection
  let H := selectedClassicalAdmissibleGoodHeight b selection
  have hheightToUniform :=
    eventually_selectedClassicalAdmissibleGoodHeight_le_selectedUniformGoodHeight
      hb (show (0 : ℝ) < 1 / 64 by norm_num) selection
  have huniform := tendsto_natCast_atTop_atTop.eventually
    (eventually_selectedUniformGoodHeight_mem
      (show (0 : ℝ) < 1 / 64 by norm_num) selection)
  have hheight : ∀ᶠ m : ℕ in atTop,
      H (m : ℝ) ≤ carlsonPolynomialHeight (1 / 64) (m : ℝ) := by
    filter_upwards [hheightToUniform, huniform] with m hCU hU
    exact hCU.trans hU.2
  have hdeltaLe :=
    eventually_classicalAdmissibleDyadicCarlsonGapWidth_le_sixteenth
      (rate := gapRate)
  refine ⟨hzeroFree selection, ?_⟩
  filter_upwards [hheight, hfixed, hdeltaLe] with
      m hheightM hfixedM hdeltaLeM
  have hdeltaPos :=
    classicalAdmissibleDyadicCarlsonGapWidth_pos hgapRate m
  constructor
  · calc
      actualSelectedHeightMovingCarlsonMiddleMass H
          (classicalAdmissibleDyadicCarlsonGapWidth gapRate) m ≤
        actualSelectedHeightSevenEighthsLowMass H m +
          actualDyadicCarlsonFixedAnchorMass (1 / 64)
            (classicalAdmissibleDyadicCarlsonGapWidth gapRate)
            (dyadicCarlsonLayerSchedule
              (classicalAdmissibleDyadicCarlsonGapWidth gapRate)) m :=
        actualSelectedHeightMovingCarlsonMiddleMass_le_low_add_dyadicFixedAnchor
          hheightM hdeltaPos
      _ ≤ actualSelectedHeightSevenEighthsLowMass H m +
          classicalDyadicCarlsonSqrtLogMajorant D gapRate m :=
        add_le_add le_rfl hfixedM
  · exact
      (actualSelectedHeightMovingCarlsonStripMass_le_dyadicFixedAnchor
        hheightM hdeltaPos hdeltaLeM).trans hfixedM

lemma exists_selectedBalancedClassicalAdmissibleDyadicCarlsonQuantitativeMassMajorant :
    ∃ b gapRate D : ℝ,
      0 < b ∧
      gapRate = classicalAdmissibleBalancedRate b / 2 ∧
      0 < gapRate ∧ 0 < D ∧
      IsCarlsonMovingDyadicLogPowerGap
        (classicalAdmissibleDyadicCarlsonGapWidth gapRate) ∧
      classicalAdmissibleVerifiedPNTDecayRate b = gapRate / 4 ∧
      Tendsto (classicalDyadicCarlsonSqrtLogMajorant D gapRate)
        atTop (nhds 0) ∧
      ∀ selection : UniformNaturalPointGoodHeightSelection,
        IsSelectedHeightDynamicZeroFree
          (selectedClassicalAdmissibleGoodHeight b selection)
          (classicalAdmissibleDyadicCarlsonGapWidth gapRate) ∧
        ∀ᶠ m : ℕ in atTop,
          actualSelectedHeightMovingCarlsonMiddleMass
              (selectedClassicalAdmissibleGoodHeight b selection)
              (classicalAdmissibleDyadicCarlsonGapWidth gapRate) m ≤
            actualSelectedHeightSevenEighthsLowMass
                (selectedClassicalAdmissibleGoodHeight b selection) m +
              classicalDyadicCarlsonSqrtLogMajorant D gapRate m ∧
          actualSelectedHeightMovingCarlsonStripMass
              (selectedClassicalAdmissibleGoodHeight b selection)
              (classicalAdmissibleDyadicCarlsonGapWidth gapRate) m ≤
            classicalDyadicCarlsonSqrtLogMajorant D gapRate m := by
  rcases exists_balancedClassicalTruncationWithVerifiedBottleneck with
    ⟨b, gapRate, hb, hgapRateEq, hverifiedEq, hverifiedPos,
      hverifiedLe, hgap, hzeroFree⟩
  have hgapRate : 0 < gapRate := by
    rw [hgapRateEq]
    exact div_pos (classicalAdmissibleBalancedRate_pos hb) (by norm_num)
  rcases
      exists_selectedClassicalAdmissibleDyadicCarlsonQuantitativeMassMajorant_of_zeroFree
        hb hgapRate hzeroFree with
    ⟨D, hD, hDzero, hselected⟩
  exact ⟨b, gapRate, D, hb, hgapRateEq,
    hgapRate, hD, hgap, hverifiedEq, hDzero, hselected⟩

end PrimeNumberTheorem
