import PrimeNumberTheorem.ZeroDensityLayerBudgetActualClassicalDyadicCarlsonClosedFormFullPNT

open Filter Real Complex
open scoped Topology BigOperators

namespace PrimeNumberTheorem

noncomputable def classicalAdmissibleVerifiedPNTDecayRate (b : ℝ) : ℝ :=
  classicalAdmissibleBalancedRate b / 8

lemma classicalAdmissibleVerifiedPNTDecayRate_pos
    {b : ℝ} (hb : 0 < b) :
    0 < classicalAdmissibleVerifiedPNTDecayRate b := by
  unfold classicalAdmissibleVerifiedPNTDecayRate
  exact div_pos (classicalAdmissibleBalancedRate_pos hb) (by norm_num)

lemma classicalAdmissibleVerifiedPNTDecayRate_eq_gapRate_div_four
    (b : ℝ) :
    classicalAdmissibleVerifiedPNTDecayRate b =
      (classicalAdmissibleBalancedRate b / 2) / 4 := by
  unfold classicalAdmissibleVerifiedPNTDecayRate
  ring

lemma classicalAdmissibleVerifiedPNTDecayRate_le_contourRate
    {b : ℝ} (hb : 0 < b) :
    classicalAdmissibleVerifiedPNTDecayRate b ≤
      classicalAdmissibleBalancedRate b := by
  unfold classicalAdmissibleVerifiedPNTDecayRate
  have hrate := (classicalAdmissibleBalancedRate_pos hb).le
  linarith

lemma classicalAdmissibleVerifiedPNTDecayRate_isOptimal
    {b : ℝ} (hb : 0 < b) :
    ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 →
      classicalDynamicBalancedRate b alpha / 8 ≤
        classicalAdmissibleVerifiedPNTDecayRate b := by
  intro alpha halpha halphaOne
  unfold classicalAdmissibleVerifiedPNTDecayRate
  have h := classicalDynamicBalancedRate_le_admissible
    hb halpha halphaOne
  linarith

lemma exists_selectedClassicalAdmissibleDyadicCarlsonBalancedZeroFreeGap :
    ∃ b gapRate : ℝ,
      0 < b ∧
      gapRate = classicalAdmissibleBalancedRate b / 2 ∧
      0 < gapRate ∧
      IsCarlsonMovingDyadicLogPowerGap
        (classicalAdmissibleDyadicCarlsonGapWidth gapRate) ∧
      ∀ selection : UniformNaturalPointGoodHeightSelection,
        IsSelectedHeightDynamicZeroFree
          (selectedClassicalAdmissibleGoodHeight b selection)
          (classicalAdmissibleDyadicCarlsonGapWidth gapRate) := by
  rcases exists_classicalTruncationRightEdge_nontrivialZerosFinset with
    ⟨b, hb, hzeros⟩
  let alpha : ℝ := classicalAdmissibleBalancedRate b
  let gapRate : ℝ := alpha / 2
  have halpha : 0 < alpha := classicalAdmissibleBalancedRate_pos hb
  have hgapRate : 0 < gapRate := by
    dsimp [gapRate]
    linarith
  have halphaSquare : alpha ^ 2 ≤ b := by
    have hzeroFree := classicalAdmissibleBalancedRate_le_zeroFreeRate hb
    have hmul := (le_div_iff₀ halpha).mp hzeroFree
    nlinarith
  have hmargin : gapRate * alpha < b := by
    dsimp [gapRate]
    nlinarith [sq_pos_of_pos halpha]
  refine ⟨b, gapRate, hb, ?_, hgapRate,
    isCarlsonMovingDyadicLogPowerGap_classicalAdmissible hgapRate, ?_⟩
  · rfl
  · intro selection
    exact isSelectedHeightDynamicZeroFree_selectedClassicalAdmissible
      hb hgapRate hmargin hzeros selection

lemma exists_balancedClassicalTruncationWithVerifiedBottleneck :
    ∃ b gapRate : ℝ,
      0 < b ∧
      gapRate = classicalAdmissibleBalancedRate b / 2 ∧
      classicalAdmissibleVerifiedPNTDecayRate b = gapRate / 4 ∧
      0 < classicalAdmissibleVerifiedPNTDecayRate b ∧
      classicalAdmissibleVerifiedPNTDecayRate b ≤
        classicalAdmissibleBalancedRate b ∧
      IsCarlsonMovingDyadicLogPowerGap
        (classicalAdmissibleDyadicCarlsonGapWidth gapRate) ∧
      ∀ selection : UniformNaturalPointGoodHeightSelection,
        IsSelectedHeightDynamicZeroFree
          (selectedClassicalAdmissibleGoodHeight b selection)
          (classicalAdmissibleDyadicCarlsonGapWidth gapRate) := by
  rcases exists_selectedClassicalAdmissibleDyadicCarlsonBalancedZeroFreeGap with
    ⟨b, gapRate, hb, hgapRate, hpositive, hgap, hzeroFree⟩
  refine ⟨b, gapRate, hb, hgapRate, ?_,
    classicalAdmissibleVerifiedPNTDecayRate_pos hb,
    classicalAdmissibleVerifiedPNTDecayRate_le_contourRate hb,
    hgap, hzeroFree⟩
  rw [hgapRate]
  exact classicalAdmissibleVerifiedPNTDecayRate_eq_gapRate_div_four b

end PrimeNumberTheorem
