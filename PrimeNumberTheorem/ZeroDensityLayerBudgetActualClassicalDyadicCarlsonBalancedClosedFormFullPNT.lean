import PrimeNumberTheorem.ZeroDensityLayerBudgetActualClassicalDyadicCarlsonBalancedQuantitativeMass

open Filter Real Complex
open scoped Topology BigOperators

namespace PrimeNumberTheorem

lemma exists_selectedBalancedClassicalAdmissibleDyadicCarlsonClosedFormFullPNTErrorMajorant :
    ∃ b gapRate D : ℝ,
      0 < b ∧
      gapRate = classicalAdmissibleBalancedRate b / 2 ∧
      0 < gapRate ∧ 0 < D ∧
      IsCarlsonMovingDyadicLogPowerGap
        (classicalAdmissibleDyadicCarlsonGapWidth gapRate) ∧
      classicalAdmissibleVerifiedPNTDecayRate b = gapRate / 4 ∧
      ∀ selection : UniformNaturalPointGoodHeightSelection,
        IsSelectedHeightDynamicZeroFree
          (selectedClassicalAdmissibleGoodHeight b selection)
          (classicalAdmissibleDyadicCarlsonGapWidth gapRate) ∧
        ∃ E eta C kappa : ℝ,
          0 ≤ E ∧ 0 < eta ∧ 0 ≤ C ∧ 0 < kappa ∧
          Tendsto
            (classicalDyadicCarlsonClosedFormFullPNTErrorMajorant
              b selection E eta C kappa D gapRate) atTop (nhds 0) ∧
          ∀ᶠ m : ℕ in atTop,
            |relativeChebyshevPsi0Error (m : ℝ)| ≤
              classicalDyadicCarlsonClosedFormFullPNTErrorMajorant
                b selection E eta C kappa D gapRate m := by
  rcases
      exists_selectedBalancedClassicalAdmissibleDyadicCarlsonQuantitativeMassMajorant with
    ⟨b, gapRate, D, hb, hgapRateEq, hgapRate, hD, hgap,
      hverifiedEq, hDzero, hselected⟩
  refine ⟨b, gapRate, D, hb, hgapRateEq, hgapRate, hD,
    hgap, hverifiedEq, ?_⟩
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
        classicalDyadicCarlsonPositiveZeroTailMajorant
          E eta C kappa D gapRate m := by
    filter_upwards [hcritical, hlow, hselection.2, hcap] with
        m hcriticalM hlowM hmasses hcapM
    have hlowM' :
        actualSelectedHeightSevenEighthsLowMass H m ≤
          classicalSevenEighthsLowMajorant C kappa m := by
      simpa [H, classicalSevenEighthsLowMajorant] using hlowM
    have hmiddle :
        actualSelectedHeightMovingCarlsonMiddleMass H
            (classicalAdmissibleDyadicCarlsonGapWidth gapRate) m ≤
          classicalDyadicCarlsonMiddleMajorant C kappa D gapRate m := by
      calc
        actualSelectedHeightMovingCarlsonMiddleMass H
            (classicalAdmissibleDyadicCarlsonGapWidth gapRate) m ≤
          actualSelectedHeightSevenEighthsLowMass H m +
            classicalDyadicCarlsonSqrtLogMajorant D gapRate m := hmasses.1
        _ ≤ classicalSevenEighthsLowMajorant C kappa m +
            classicalDyadicCarlsonSqrtLogMajorant D gapRate m :=
          add_le_add hlowM' le_rfl
        _ = classicalDyadicCarlsonMiddleMajorant C kappa D gapRate m := rfl
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
            classicalDyadicCarlsonMiddleMajorant C kappa D gapRate m) +
          classicalDyadicCarlsonSqrtLogMajorant D gapRate m :=
        add_le_add (add_le_add hcriticalM hmiddle) hmasses.2
      _ = classicalDyadicCarlsonPositiveZeroTailMajorant
          E eta C kappa D gapRate m := rfl
  have hreal :=
    eventually_dynamicRealOrdinatePNTZeroTailNorm_le_classicalFixedMajorant
      (tendsto_selectedClassicalAdmissibleGoodHeight_atTop hb selection)
  have hfull : ∀ᶠ m : ℕ in atTop,
      dynamicFullPNTZeroTailNorm H (m : ℝ) ≤
        classicalDyadicCarlsonFullZeroTailMajorant
          E eta C kappa D gapRate m := by
    filter_upwards [eventually_ge_atTop (1 : ℕ), hpositive, hreal] with
        m hm hpositiveM hrealM
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
    calc
      dynamicFullPNTZeroTailNorm H (m : ℝ) ≤
          dynamicPositivePNTTailNorm H (m : ℝ) +
            dynamicPositivePNTTailNorm H (m : ℝ) +
              dynamicRealOrdinatePNTZeroTailNorm H (m : ℝ) :=
        dynamicFullPNTZeroTailNorm_le_two_positive_add_real hmR
      _ ≤ classicalDyadicCarlsonPositiveZeroTailMajorant
              E eta C kappa D gapRate m +
            classicalDyadicCarlsonPositiveZeroTailMajorant
              E eta C kappa D gapRate m +
            classicalRealOrdinateFixedMajorant m :=
        add_le_add (add_le_add hpositiveM hpositiveM) hrealM
      _ = classicalDyadicCarlsonFullZeroTailMajorant
          E eta C kappa D gapRate m := rfl
  have hremainder :=
    eventually_abs_selectedClassicalAdmissibleGoodHeight_actualRemainder_le
      hb selection
  have herror :=
    eventually_abs_relativeChebyshevPsi0Error_le_classicalFullPNTMajorant
      (E := E) (eta := eta) (C := C) (kappa := kappa)
      (D := D) (rate := gapRate) selection hfull hremainder
  have hremainderClosed :=
    eventually_selectedClassicalNaturalRemainderUpperBound_le_closedForm
      hb selection
  have hmajorantLe :=
    eventually_classicalFullPNTMajorant_le_closedForm
      (E := E) (eta := eta) (C := C) (kappa := kappa)
      (D := D) (rate := gapRate) selection hremainderClosed
  refine ⟨hselection.1, E, eta, C, kappa, hE, heta, hC, hkappa,
    tendsto_classicalDyadicCarlsonClosedFormFullPNTErrorMajorant_zero
      selection hb hE heta hC hkappa hgapRate, ?_⟩
  filter_upwards [herror, hmajorantLe] with m herrorM hmajorantM
  exact herrorM.trans hmajorantM

end PrimeNumberTheorem
