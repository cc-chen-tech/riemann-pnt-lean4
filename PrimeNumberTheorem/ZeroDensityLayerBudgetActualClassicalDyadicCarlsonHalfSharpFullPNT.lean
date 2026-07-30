import PrimeNumberTheorem.ZeroDensityLayerBudgetActualClassicalDyadicCarlsonThetaSharpFullPNT
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualClassicalDyadicCarlsonHalfSharpRate

open Filter Real Complex
open scoped Topology BigOperators

namespace PrimeNumberTheorem

noncomputable def classicalDyadicCarlsonHalfClosedFormFullPNTErrorMajorant
    (b : ℝ) (selection : UniformNaturalPointGoodHeightSelection)
    (E eta C kappa D rate : ℝ) (m : ℕ) : ℝ :=
  classicalDyadicCarlsonThetaClosedFormFullPNTErrorMajorant
    b selection E eta C kappa D rate (1 / 2) m

lemma tendsto_classicalDyadicCarlsonHalfClosedFormFullPNTErrorMajorant_zero
    {b E eta C kappa D rate : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hb : 0 < b) (hE : 0 ≤ E) (heta : 0 < eta)
    (hC : 0 ≤ C) (hkappa : 0 < kappa) (hrate : 0 < rate) :
    Tendsto
      (classicalDyadicCarlsonHalfClosedFormFullPNTErrorMajorant
        b selection E eta C kappa D rate) atTop (nhds 0) := by
  unfold classicalDyadicCarlsonHalfClosedFormFullPNTErrorMajorant
  exact
    tendsto_classicalDyadicCarlsonThetaClosedFormFullPNTErrorMajorant_zero
      selection hb hE heta hC hkappa hrate (by norm_num)

lemma exists_selectedClassicalAdmissibleDyadicCarlsonHalfQuantitativeMassMajorant_of_zeroFree
    {b gapRate : ℝ} (hb : 0 < b) (hgapRate : 0 < gapRate)
    (hzeroFree : ∀ selection : UniformNaturalPointGoodHeightSelection,
      IsSelectedHeightDynamicZeroFree
        (selectedClassicalAdmissibleGoodHeight b selection)
        (classicalAdmissibleDyadicCarlsonGapWidth gapRate)) :
    ∃ D : ℝ, 0 < D ∧
      Tendsto
        (classicalDyadicCarlsonThetaSqrtLogMajorant D gapRate (1 / 2))
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
              classicalDyadicCarlsonThetaSqrtLogMajorant
                D gapRate (1 / 2) m ∧
          actualSelectedHeightMovingCarlsonStripMass
              (selectedClassicalAdmissibleGoodHeight b selection)
              (classicalAdmissibleDyadicCarlsonGapWidth gapRate) m ≤
            classicalDyadicCarlsonThetaSqrtLogMajorant
              D gapRate (1 / 2) m := by
  rcases
      exists_classicalAdmissibleDyadicCarlsonHalfQuantitativeFixedAnchorMajorant
        hgapRate with
    ⟨C, hC, hfixed, hCzero⟩
  let D := C * Real.exp (gapRate / 2)
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hfixed' : ∀ᶠ m : ℕ in atTop,
      actualDyadicCarlsonFixedAnchorMass (1 / 64)
          (classicalAdmissibleDyadicCarlsonGapWidth gapRate)
          (dyadicCarlsonLayerSchedule
            (classicalAdmissibleDyadicCarlsonGapWidth gapRate)) m ≤
        classicalDyadicCarlsonThetaSqrtLogMajorant
          D gapRate (1 / 2) m := by
    simpa [D, classicalDyadicCarlsonHalfSqrtLogMajorant] using hfixed
  have hDzero : Tendsto
      (classicalDyadicCarlsonThetaSqrtLogMajorant D gapRate (1 / 2))
      atTop (nhds 0) := by
    exact tendsto_classicalDyadicCarlsonThetaSqrtLogMajorant_zero
      D hgapRate (by norm_num)
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
  filter_upwards [hheight, hfixed', hdeltaLe] with
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
          classicalDyadicCarlsonThetaSqrtLogMajorant
            D gapRate (1 / 2) m :=
        add_le_add le_rfl hfixedM
  · exact
      (actualSelectedHeightMovingCarlsonStripMass_le_dyadicFixedAnchor
        hheightM hdeltaPos hdeltaLeM).trans hfixedM

lemma exists_selectedBalancedClassicalAdmissibleDyadicCarlsonHalfClosedFormFullPNTErrorMajorant :
    ∃ b gapRate D : ℝ,
      0 < b ∧
      gapRate = classicalAdmissibleBalancedRate b / 2 ∧
      0 < gapRate ∧ 0 < D ∧
      IsCarlsonMovingDyadicLogPowerGap
        (classicalAdmissibleDyadicCarlsonGapWidth gapRate) ∧
      classicalAdmissibleThetaVerifiedPNTDecayRate b (1 / 2) =
        gapRate / 2 ∧
      classicalAdmissibleThetaVerifiedPNTDecayRate b (1 / 2) =
        classicalAdmissibleBalancedRate b / 4 ∧
      classicalAdmissibleVerifiedPNTDecayRate b <
        classicalAdmissibleThetaVerifiedPNTDecayRate b (1 / 2) ∧
      ∀ selection : UniformNaturalPointGoodHeightSelection,
        IsSelectedHeightDynamicZeroFree
          (selectedClassicalAdmissibleGoodHeight b selection)
          (classicalAdmissibleDyadicCarlsonGapWidth gapRate) ∧
        ∃ E eta C kappa : ℝ,
          0 ≤ E ∧ 0 < eta ∧ 0 ≤ C ∧ 0 < kappa ∧
          Tendsto
            (classicalDyadicCarlsonHalfClosedFormFullPNTErrorMajorant
              b selection E eta C kappa D gapRate)
            atTop (nhds 0) ∧
          ∀ᶠ m : ℕ in atTop,
            |relativeChebyshevPsi0Error (m : ℝ)| ≤
              classicalDyadicCarlsonHalfClosedFormFullPNTErrorMajorant
                b selection E eta C kappa D gapRate m := by
  rcases exists_balancedClassicalTruncationWithVerifiedBottleneck with
    ⟨b, gapRate, hb, hgapRateEq, _, _, _, hgap, hzeroFree⟩
  have hgapRate : 0 < gapRate := by
    rw [hgapRateEq]
    exact div_pos (classicalAdmissibleBalancedRate_pos hb) (by norm_num)
  rcases
      exists_selectedClassicalAdmissibleDyadicCarlsonHalfQuantitativeMassMajorant_of_zeroFree
        hb hgapRate hzeroFree with
    ⟨D, hD, _, hselected⟩
  have hhalfGap :
      classicalAdmissibleThetaVerifiedPNTDecayRate b (1 / 2) =
        gapRate / 2 := by
    rw [classicalAdmissibleHalfVerifiedPNTDecayRate_eq, hgapRateEq]
    ring
  refine ⟨b, gapRate, D, hb, hgapRateEq, hgapRate, hD, hgap,
    hhalfGap, classicalAdmissibleHalfVerifiedPNTDecayRate_eq b,
    classicalAdmissibleVerifiedPNTDecayRate_lt_halfRate hb, ?_⟩
  intro selection
  let H := selectedClassicalAdmissibleGoodHeight b selection
  have hselection := hselected selection
  rcases
      exists_eventually_actualSelectedClassicalAdmissibleCriticalHalfPNTLayerNorm_le_majorant
        hb selection with
    ⟨E, eta, hE, heta, hcritical⟩
  rcases
      exists_eventually_actualSelectedClassicalAdmissibleSevenEighthsLowMass_le_majorant
        hb selection with
    ⟨C, kappa, hC, hkappa, hlow⟩
  have hcap :=
    eventually_actualSelectedHeightMovingPositiveRightEdgeCap_of_dynamicZeroFree
      hselection.1
  have hpositive : ∀ᶠ m : ℕ in atTop,
      dynamicPositivePNTTailNorm H (m : ℝ) ≤
        classicalDyadicCarlsonThetaPositiveZeroTailMajorant
          E eta C kappa D gapRate (1 / 2) m := by
    filter_upwards [hcritical, hlow, hselection.2, hcap] with
        m hcriticalM hlowM hmasses hcapM
    have hlowM' :
        actualSelectedHeightSevenEighthsLowMass H m ≤
          classicalSevenEighthsLowMajorant C kappa m := by
      simpa [H, classicalSevenEighthsLowMajorant] using hlowM
    have hmiddle :
        actualSelectedHeightMovingCarlsonMiddleMass H
            (classicalAdmissibleDyadicCarlsonGapWidth gapRate) m ≤
          classicalDyadicCarlsonThetaMiddleMajorant
            C kappa D gapRate (1 / 2) m := by
      calc
        actualSelectedHeightMovingCarlsonMiddleMass H
            (classicalAdmissibleDyadicCarlsonGapWidth gapRate) m ≤
          actualSelectedHeightSevenEighthsLowMass H m +
            classicalDyadicCarlsonThetaSqrtLogMajorant
              D gapRate (1 / 2) m := hmasses.1
        _ ≤ classicalSevenEighthsLowMajorant C kappa m +
            classicalDyadicCarlsonThetaSqrtLogMajorant
              D gapRate (1 / 2) m :=
          add_le_add hlowM' le_rfl
        _ = classicalDyadicCarlsonThetaMiddleMajorant
            C kappa D gapRate (1 / 2) m := rfl
    calc
      dynamicPositivePNTTailNorm H (m : ℝ) ≤
          (dynamicPositiveOutsideClusterPNTLayerNorm H ∅
              (actualSelectedHeightCriticalHalfCanonicalInput H)
              0 (m : ℝ) +
            actualSelectedHeightMovingCarlsonMiddleMass H
              (classicalAdmissibleDyadicCarlsonGapWidth gapRate) m) +
          actualSelectedHeightMovingCarlsonStripMass H
            (classicalAdmissibleDyadicCarlsonGapWidth gapRate) m :=
        dynamicPositivePNTTailNorm_le_selectedCriticalHalf_add_movingMasses
          hcapM
      _ ≤ (classicalCriticalHalfMajorant E eta m +
            classicalDyadicCarlsonThetaMiddleMajorant
              C kappa D gapRate (1 / 2) m) +
          classicalDyadicCarlsonThetaSqrtLogMajorant
            D gapRate (1 / 2) m :=
        add_le_add (add_le_add hcriticalM hmiddle) hmasses.2
      _ = classicalDyadicCarlsonThetaPositiveZeroTailMajorant
          E eta C kappa D gapRate (1 / 2) m := rfl
  have hreal :=
    eventually_dynamicRealOrdinatePNTZeroTailNorm_le_classicalFixedMajorant
      (tendsto_selectedClassicalAdmissibleGoodHeight_atTop hb selection)
  have hfull : ∀ᶠ m : ℕ in atTop,
      dynamicFullPNTZeroTailNorm H (m : ℝ) ≤
        classicalDyadicCarlsonThetaFullZeroTailMajorant
          E eta C kappa D gapRate (1 / 2) m := by
    filter_upwards [eventually_ge_atTop (1 : ℕ), hpositive, hreal] with
        m hm hpositiveM hrealM
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
    calc
      dynamicFullPNTZeroTailNorm H (m : ℝ) ≤
          dynamicPositivePNTTailNorm H (m : ℝ) +
            dynamicPositivePNTTailNorm H (m : ℝ) +
              dynamicRealOrdinatePNTZeroTailNorm H (m : ℝ) :=
        dynamicFullPNTZeroTailNorm_le_two_positive_add_real hmR
      _ ≤ classicalDyadicCarlsonThetaPositiveZeroTailMajorant
              E eta C kappa D gapRate (1 / 2) m +
            classicalDyadicCarlsonThetaPositiveZeroTailMajorant
              E eta C kappa D gapRate (1 / 2) m +
            classicalRealOrdinateFixedMajorant m :=
        add_le_add (add_le_add hpositiveM hpositiveM) hrealM
      _ = classicalDyadicCarlsonThetaFullZeroTailMajorant
          E eta C kappa D gapRate (1 / 2) m := rfl
  have hremainder :=
    eventually_abs_selectedClassicalAdmissibleGoodHeight_actualRemainder_le
      hb selection
  have hremainderClosed :=
    eventually_selectedClassicalNaturalRemainderUpperBound_le_closedForm
      hb selection
  have herror :=
    eventually_abs_relativeChebyshevPsi0Error_le_thetaClosedFormFullPNTMajorant
      selection hfull hremainder hremainderClosed
  refine ⟨hselection.1, E, eta, C, kappa, hE, heta, hC, hkappa,
    tendsto_classicalDyadicCarlsonHalfClosedFormFullPNTErrorMajorant_zero
      selection hb hE heta hC hkappa hgapRate, ?_⟩
  simpa [classicalDyadicCarlsonHalfClosedFormFullPNTErrorMajorant] using herror

end PrimeNumberTheorem
