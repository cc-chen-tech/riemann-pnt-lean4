import PrimeNumberTheorem.ZeroDensityLayerBudgetActualClassicalDyadicCarlsonThetaSharpRate

open Filter Real Complex
open scoped Topology BigOperators

namespace PrimeNumberTheorem

noncomputable def classicalDyadicCarlsonThetaMiddleMajorant
    (C kappa D rate theta : ℝ) (m : ℕ) : ℝ :=
  classicalSevenEighthsLowMajorant C kappa m +
    classicalDyadicCarlsonThetaSqrtLogMajorant D rate theta m

lemma tendsto_classicalDyadicCarlsonThetaMiddleMajorant_zero
    {C kappa D rate theta : ℝ}
    (hC : 0 ≤ C) (hkappa : 0 < kappa)
    (hrate : 0 < rate) (htheta : 0 < theta) :
    Tendsto
      (classicalDyadicCarlsonThetaMiddleMajorant C kappa D rate theta)
      atTop (nhds 0) := by
  change Tendsto
    (fun m : ℕ =>
      classicalSevenEighthsLowMajorant C kappa m +
        classicalDyadicCarlsonThetaSqrtLogMajorant D rate theta m)
    atTop (nhds 0)
  simpa only [add_zero] using
    (tendsto_classicalSevenEighthsLowMajorant_zero hC hkappa).add
      (tendsto_classicalDyadicCarlsonThetaSqrtLogMajorant_zero
        D hrate htheta)

noncomputable def classicalDyadicCarlsonThetaPositiveZeroTailMajorant
    (E eta C kappa D rate theta : ℝ) (m : ℕ) : ℝ :=
  (classicalCriticalHalfMajorant E eta m +
    classicalDyadicCarlsonThetaMiddleMajorant
      C kappa D rate theta m) +
  classicalDyadicCarlsonThetaSqrtLogMajorant D rate theta m

lemma tendsto_classicalDyadicCarlsonThetaPositiveZeroTailMajorant_zero
    {E eta C kappa D rate theta : ℝ}
    (hE : 0 ≤ E) (heta : 0 < eta)
    (hC : 0 ≤ C) (hkappa : 0 < kappa)
    (hrate : 0 < rate) (htheta : 0 < theta) :
    Tendsto
      (classicalDyadicCarlsonThetaPositiveZeroTailMajorant
        E eta C kappa D rate theta) atTop (nhds 0) := by
  change Tendsto
    (fun m : ℕ =>
      (classicalCriticalHalfMajorant E eta m +
        classicalDyadicCarlsonThetaMiddleMajorant
          C kappa D rate theta m) +
      classicalDyadicCarlsonThetaSqrtLogMajorant D rate theta m)
    atTop (nhds 0)
  simpa only [add_zero] using
    ((tendsto_classicalCriticalHalfMajorant_zero hE heta).add
      (tendsto_classicalDyadicCarlsonThetaMiddleMajorant_zero
        hC hkappa hrate htheta)).add
      (tendsto_classicalDyadicCarlsonThetaSqrtLogMajorant_zero
        D hrate htheta)

noncomputable def classicalDyadicCarlsonThetaFullZeroTailMajorant
    (E eta C kappa D rate theta : ℝ) (m : ℕ) : ℝ :=
  classicalDyadicCarlsonThetaPositiveZeroTailMajorant
      E eta C kappa D rate theta m +
    classicalDyadicCarlsonThetaPositiveZeroTailMajorant
      E eta C kappa D rate theta m +
    classicalRealOrdinateFixedMajorant m

lemma tendsto_classicalDyadicCarlsonThetaFullZeroTailMajorant_zero
    {E eta C kappa D rate theta : ℝ}
    (hE : 0 ≤ E) (heta : 0 < eta)
    (hC : 0 ≤ C) (hkappa : 0 < kappa)
    (hrate : 0 < rate) (htheta : 0 < theta) :
    Tendsto
      (classicalDyadicCarlsonThetaFullZeroTailMajorant
        E eta C kappa D rate theta) atTop (nhds 0) := by
  have hpositive :=
    tendsto_classicalDyadicCarlsonThetaPositiveZeroTailMajorant_zero
      (D := D) hE heta hC hkappa hrate htheta
  change Tendsto
    (fun m : ℕ =>
      classicalDyadicCarlsonThetaPositiveZeroTailMajorant
          E eta C kappa D rate theta m +
        classicalDyadicCarlsonThetaPositiveZeroTailMajorant
          E eta C kappa D rate theta m +
        classicalRealOrdinateFixedMajorant m)
    atTop (nhds 0)
  simpa only [add_zero] using
    (hpositive.add hpositive).add
      tendsto_classicalRealOrdinateFixedMajorant_zero

noncomputable def classicalDyadicCarlsonThetaClosedFormFullPNTErrorMajorant
    (b : ℝ) (selection : UniformNaturalPointGoodHeightSelection)
    (E eta C kappa D rate theta : ℝ) (m : ℕ) : ℝ :=
  classicalDyadicCarlsonThetaFullZeroTailMajorant
      E eta C kappa D rate theta m +
    |actualPNTClosedRealAxisRelativeTerm (m : ℝ)| +
    classicalAdmissibleClosedFormNaturalRemainderMajorant b selection m

lemma tendsto_classicalDyadicCarlsonThetaClosedFormFullPNTErrorMajorant_zero
    {b E eta C kappa D rate theta : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hb : 0 < b) (hE : 0 ≤ E) (heta : 0 < eta)
    (hC : 0 ≤ C) (hkappa : 0 < kappa)
    (hrate : 0 < rate) (htheta : 0 < theta) :
    Tendsto
      (classicalDyadicCarlsonThetaClosedFormFullPNTErrorMajorant
        b selection E eta C kappa D rate theta) atTop (nhds 0) := by
  have hzeros :=
    tendsto_classicalDyadicCarlsonThetaFullZeroTailMajorant_zero
      (D := D) hE heta hC hkappa hrate htheta
  have hcontour := cofinalPNTZeroDepthRelativeRemainderMajorant_tendsto
    (C := selection.constant) (classicalAdmissibleBalancedRate_pos hb)
  have hremainder : Tendsto
      (classicalAdmissibleClosedFormNaturalRemainderMajorant b selection)
      atTop (nhds 0) := by
    change Tendsto
      (fun m : ℕ =>
        cofinalPNTZeroDepthRelativeRemainderMajorant selection.constant
            (classicalAdmissibleBalancedRate b) m +
          classicalClosedLogRelativeMajorant m)
      atTop (nhds 0)
    simpa only [add_zero] using
      hcontour.add tendsto_classicalClosedLogRelativeMajorant_zero
  change Tendsto
    (fun m : ℕ =>
      classicalDyadicCarlsonThetaFullZeroTailMajorant
          E eta C kappa D rate theta m +
        |actualPNTClosedRealAxisRelativeTerm (m : ℝ)| +
        classicalAdmissibleClosedFormNaturalRemainderMajorant
          b selection m)
    atTop (nhds 0)
  simpa only [add_zero] using
    (hzeros.add
      tendsto_abs_actualPNTClosedRealAxisRelativeTerm_natural_zero).add
      hremainder

lemma eventually_abs_relativeChebyshevPsi0Error_le_thetaClosedFormFullPNTMajorant
    {b E eta C kappa D rate theta : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hfull : ∀ᶠ m : ℕ in atTop,
      dynamicFullPNTZeroTailNorm
          (selectedClassicalAdmissibleGoodHeight b selection) (m : ℝ) ≤
        classicalDyadicCarlsonThetaFullZeroTailMajorant
          E eta C kappa D rate theta m)
    (hremainder : ∀ᶠ m : ℕ in atTop,
      |actualPNTExplicitFormulaRelativeRemainder
          (selectedClassicalAdmissibleGoodHeight b selection) (m : ℝ)| ≤
        selectedClassicalAdmissibleNaturalRemainderUpperBound b selection m)
    (hremainderClosed : ∀ᶠ m : ℕ in atTop,
      selectedClassicalAdmissibleNaturalRemainderUpperBound b selection m ≤
        classicalAdmissibleClosedFormNaturalRemainderMajorant
          b selection m) :
    ∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ)| ≤
        classicalDyadicCarlsonThetaClosedFormFullPNTErrorMajorant
          b selection E eta C kappa D rate theta m := by
  let H := selectedClassicalAdmissibleGoodHeight b selection
  filter_upwards [hfull, hremainder, hremainderClosed] with
      m hfullM hremainderM hremainderClosedM
  have hfinite :
      |(dynamicFinitePNTZeroSum H (m : ℝ)).re| ≤
        dynamicFullPNTZeroTailNorm H (m : ℝ) := by
    calc
      |(dynamicFinitePNTZeroSum H (m : ℝ)).re| ≤
          ‖dynamicFinitePNTZeroSum H (m : ℝ)‖ := abs_re_le_norm _
      _ = dynamicFullPNTZeroTailNorm H (m : ℝ) := rfl
  rw [relativeChebyshevPsi0Error_eq_dynamicFinite_add_closed_add_remainder
    H (m : ℝ)]
  calc
    |(dynamicFinitePNTZeroSum H (m : ℝ)).re +
        (actualPNTClosedRealAxisRelativeTerm (m : ℝ) +
          actualPNTExplicitFormulaRelativeRemainder H (m : ℝ))| ≤
      |(dynamicFinitePNTZeroSum H (m : ℝ)).re| +
        |actualPNTClosedRealAxisRelativeTerm (m : ℝ) +
          actualPNTExplicitFormulaRelativeRemainder H (m : ℝ)| :=
      abs_add_le _ _
    _ ≤ |(dynamicFinitePNTZeroSum H (m : ℝ)).re| +
        (|actualPNTClosedRealAxisRelativeTerm (m : ℝ)| +
          |actualPNTExplicitFormulaRelativeRemainder H (m : ℝ)|) :=
      add_le_add le_rfl (abs_add_le _ _)
    _ ≤ dynamicFullPNTZeroTailNorm H (m : ℝ) +
        (|actualPNTClosedRealAxisRelativeTerm (m : ℝ)| +
          |actualPNTExplicitFormulaRelativeRemainder H (m : ℝ)|) :=
      add_le_add hfinite le_rfl
    _ ≤ classicalDyadicCarlsonThetaFullZeroTailMajorant
            E eta C kappa D rate theta m +
        (|actualPNTClosedRealAxisRelativeTerm (m : ℝ)| +
          classicalAdmissibleClosedFormNaturalRemainderMajorant
            b selection m) :=
      add_le_add hfullM
        (add_le_add le_rfl (hremainderM.trans hremainderClosedM))
    _ = classicalDyadicCarlsonThetaClosedFormFullPNTErrorMajorant
        b selection E eta C kappa D rate theta m := by
      unfold classicalDyadicCarlsonThetaClosedFormFullPNTErrorMajorant
      ring

lemma exists_selectedClassicalAdmissibleDyadicCarlsonThetaQuantitativeMassMajorant_of_zeroFree
    {b gapRate theta : ℝ}
    (hb : 0 < b) (hgapRate : 0 < gapRate)
    (htheta : 0 < theta) (hthetaHalf : theta < 1 / 2)
    (hzeroFree : ∀ selection : UniformNaturalPointGoodHeightSelection,
      IsSelectedHeightDynamicZeroFree
        (selectedClassicalAdmissibleGoodHeight b selection)
        (classicalAdmissibleDyadicCarlsonGapWidth gapRate)) :
    ∃ D : ℝ, 0 < D ∧
      Tendsto
        (classicalDyadicCarlsonThetaSqrtLogMajorant D gapRate theta)
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
                D gapRate theta m ∧
          actualSelectedHeightMovingCarlsonStripMass
              (selectedClassicalAdmissibleGoodHeight b selection)
              (classicalAdmissibleDyadicCarlsonGapWidth gapRate) m ≤
            classicalDyadicCarlsonThetaSqrtLogMajorant
              D gapRate theta m := by
  rcases
      exists_classicalAdmissibleDyadicCarlsonThetaQuantitativeFixedAnchorMajorant
        hgapRate htheta hthetaHalf with
    ⟨D, hD, hfixed, hDzero⟩
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
          classicalDyadicCarlsonThetaSqrtLogMajorant
            D gapRate theta m :=
        add_le_add le_rfl hfixedM
  · exact
      (actualSelectedHeightMovingCarlsonStripMass_le_dyadicFixedAnchor
        hheightM hdeltaPos hdeltaLeM).trans hfixedM

lemma exists_selectedBalancedClassicalAdmissibleDyadicCarlsonThetaClosedFormFullPNTErrorMajorant
    {theta : ℝ} (hthetaQuarter : 1 / 4 < theta)
    (hthetaHalf : theta < 1 / 2) :
    ∃ b gapRate D : ℝ,
      0 < b ∧
      gapRate = classicalAdmissibleBalancedRate b / 2 ∧
      0 < gapRate ∧ 0 < D ∧
      IsCarlsonMovingDyadicLogPowerGap
        (classicalAdmissibleDyadicCarlsonGapWidth gapRate) ∧
      classicalAdmissibleThetaVerifiedPNTDecayRate b theta =
        theta * gapRate ∧
      classicalAdmissibleVerifiedPNTDecayRate b <
        classicalAdmissibleThetaVerifiedPNTDecayRate b theta ∧
      classicalAdmissibleThetaVerifiedPNTDecayRate b theta <
        classicalAdmissibleBalancedRate b / 4 ∧
      ∀ selection : UniformNaturalPointGoodHeightSelection,
        IsSelectedHeightDynamicZeroFree
          (selectedClassicalAdmissibleGoodHeight b selection)
          (classicalAdmissibleDyadicCarlsonGapWidth gapRate) ∧
        ∃ E eta C kappa : ℝ,
          0 ≤ E ∧ 0 < eta ∧ 0 ≤ C ∧ 0 < kappa ∧
          Tendsto
            (classicalDyadicCarlsonThetaClosedFormFullPNTErrorMajorant
              b selection E eta C kappa D gapRate theta)
            atTop (nhds 0) ∧
          ∀ᶠ m : ℕ in atTop,
            |relativeChebyshevPsi0Error (m : ℝ)| ≤
              classicalDyadicCarlsonThetaClosedFormFullPNTErrorMajorant
                b selection E eta C kappa D gapRate theta m := by
  have htheta : 0 < theta := by linarith
  rcases exists_balancedClassicalTruncationWithVerifiedBottleneck with
    ⟨b, gapRate, hb, hgapRateEq, _, _, _, hgap, hzeroFree⟩
  have hgapRate : 0 < gapRate := by
    rw [hgapRateEq]
    exact div_pos (classicalAdmissibleBalancedRate_pos hb) (by norm_num)
  rcases
      exists_selectedClassicalAdmissibleDyadicCarlsonThetaQuantitativeMassMajorant_of_zeroFree
        hb hgapRate htheta hthetaHalf hzeroFree with
    ⟨D, hD, _, hselected⟩
  have hthetaRateEq :
      classicalAdmissibleThetaVerifiedPNTDecayRate b theta =
        theta * gapRate := by
    unfold classicalAdmissibleThetaVerifiedPNTDecayRate
    rw [hgapRateEq]
  refine ⟨b, gapRate, D, hb, hgapRateEq, hgapRate, hD, hgap,
    hthetaRateEq,
    classicalAdmissibleVerifiedPNTDecayRate_lt_thetaRate
      hb hthetaQuarter,
    classicalAdmissibleThetaVerifiedPNTDecayRate_lt_quarterHeightRate
      hb hthetaHalf, ?_⟩
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
          E eta C kappa D gapRate theta m := by
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
            C kappa D gapRate theta m := by
      calc
        actualSelectedHeightMovingCarlsonMiddleMass H
            (classicalAdmissibleDyadicCarlsonGapWidth gapRate) m ≤
          actualSelectedHeightSevenEighthsLowMass H m +
            classicalDyadicCarlsonThetaSqrtLogMajorant
              D gapRate theta m := hmasses.1
        _ ≤ classicalSevenEighthsLowMajorant C kappa m +
            classicalDyadicCarlsonThetaSqrtLogMajorant
              D gapRate theta m :=
          add_le_add hlowM' le_rfl
        _ = classicalDyadicCarlsonThetaMiddleMajorant
            C kappa D gapRate theta m := rfl
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
              C kappa D gapRate theta m) +
          classicalDyadicCarlsonThetaSqrtLogMajorant
            D gapRate theta m :=
        add_le_add (add_le_add hcriticalM hmiddle) hmasses.2
      _ = classicalDyadicCarlsonThetaPositiveZeroTailMajorant
          E eta C kappa D gapRate theta m := rfl
  have hreal :=
    eventually_dynamicRealOrdinatePNTZeroTailNorm_le_classicalFixedMajorant
      (tendsto_selectedClassicalAdmissibleGoodHeight_atTop hb selection)
  have hfull : ∀ᶠ m : ℕ in atTop,
      dynamicFullPNTZeroTailNorm H (m : ℝ) ≤
        classicalDyadicCarlsonThetaFullZeroTailMajorant
          E eta C kappa D gapRate theta m := by
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
              E eta C kappa D gapRate theta m +
            classicalDyadicCarlsonThetaPositiveZeroTailMajorant
              E eta C kappa D gapRate theta m +
            classicalRealOrdinateFixedMajorant m :=
        add_le_add (add_le_add hpositiveM hpositiveM) hrealM
      _ = classicalDyadicCarlsonThetaFullZeroTailMajorant
          E eta C kappa D gapRate theta m := rfl
  have hremainder :=
    eventually_abs_selectedClassicalAdmissibleGoodHeight_actualRemainder_le
      hb selection
  have hremainderClosed :=
    eventually_selectedClassicalNaturalRemainderUpperBound_le_closedForm
      hb selection
  refine ⟨hselection.1, E, eta, C, kappa, hE, heta, hC, hkappa,
    tendsto_classicalDyadicCarlsonThetaClosedFormFullPNTErrorMajorant_zero
      selection hb hE heta hC hkappa hgapRate htheta, ?_⟩
  exact
    eventually_abs_relativeChebyshevPsi0Error_le_thetaClosedFormFullPNTMajorant
      selection hfull hremainder hremainderClosed

end PrimeNumberTheorem
