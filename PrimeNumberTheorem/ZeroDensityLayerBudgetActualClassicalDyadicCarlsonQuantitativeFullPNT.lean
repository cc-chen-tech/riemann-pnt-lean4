import PrimeNumberTheorem.ZeroDensityLayerBudgetActualClassicalDyadicCarlsonQuantitativeFullZeroTail

open Filter Real Complex
open scoped Topology BigOperators

namespace PrimeNumberTheorem

noncomputable def classicalDyadicCarlsonFullPNTErrorMajorant
    (b : ℝ) (selection : UniformNaturalPointGoodHeightSelection)
    (E eta C kappa D rate : ℝ) (m : ℕ) : ℝ :=
  classicalDyadicCarlsonFullZeroTailMajorant E eta C kappa D rate m +
    |actualPNTClosedRealAxisRelativeTerm (m : ℝ)| +
    selectedClassicalAdmissibleNaturalRemainderUpperBound b selection m

lemma tendsto_abs_actualPNTClosedRealAxisRelativeTerm_natural_zero :
    Tendsto (fun m : ℕ =>
      |actualPNTClosedRealAxisRelativeTerm (m : ℝ)|) atTop (nhds 0) := by
  have h := actualPNTClosedRealAxisRelativeTerm_targetAmplitudeNegligible
    (show (0 : ℝ) < 1 by norm_num)
  unfold TargetAmplitudeNegligible at h
  have hreal : Tendsto
      (fun x : ℝ => |actualPNTClosedRealAxisRelativeTerm x|)
      atTop (nhds 0) := by
    simpa [targetZeroPowerAmplitude] using h
  exact hreal.comp tendsto_natCast_atTop_atTop

lemma tendsto_classicalDyadicCarlsonFullPNTErrorMajorant_zero
    {b E eta C kappa D rate : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hb : 0 < b) (hE : 0 ≤ E) (heta : 0 < eta)
    (hC : 0 ≤ C) (hkappa : 0 < kappa) (hrate : 0 < rate) :
    Tendsto
      (classicalDyadicCarlsonFullPNTErrorMajorant
        b selection E eta C kappa D rate) atTop (nhds 0) := by
  have hzeros := tendsto_classicalDyadicCarlsonFullZeroTailMajorant_zero
    (D := D) hE heta hC hkappa hrate
  have hremainder :=
    tendsto_selectedClassicalAdmissibleNaturalRemainderUpperBound_zero
      hb selection
  change Tendsto
    (fun m : ℕ =>
      classicalDyadicCarlsonFullZeroTailMajorant
          E eta C kappa D rate m +
        |actualPNTClosedRealAxisRelativeTerm (m : ℝ)| +
        selectedClassicalAdmissibleNaturalRemainderUpperBound
          b selection m)
    atTop (nhds 0)
  simpa only [add_zero] using
    (hzeros.add tendsto_abs_actualPNTClosedRealAxisRelativeTerm_natural_zero).add
      hremainder

lemma eventually_abs_relativeChebyshevPsi0Error_le_classicalFullPNTMajorant
    {b E eta C kappa D rate : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hfull : ∀ᶠ m : ℕ in atTop,
      dynamicFullPNTZeroTailNorm
          (selectedClassicalAdmissibleGoodHeight b selection) (m : ℝ) ≤
        classicalDyadicCarlsonFullZeroTailMajorant
          E eta C kappa D rate m)
    (hremainder : ∀ᶠ m : ℕ in atTop,
      |actualPNTExplicitFormulaRelativeRemainder
          (selectedClassicalAdmissibleGoodHeight b selection) (m : ℝ)| ≤
        selectedClassicalAdmissibleNaturalRemainderUpperBound b selection m) :
    ∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ)| ≤
        classicalDyadicCarlsonFullPNTErrorMajorant
          b selection E eta C kappa D rate m := by
  let H := selectedClassicalAdmissibleGoodHeight b selection
  filter_upwards [hfull, hremainder] with m hfullm hremainderM
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
          actualPNTExplicitFormulaRelativeRemainder H (m : ℝ)| := abs_add_le _ _
    _ ≤ |(dynamicFinitePNTZeroSum H (m : ℝ)).re| +
        (|actualPNTClosedRealAxisRelativeTerm (m : ℝ)| +
          |actualPNTExplicitFormulaRelativeRemainder H (m : ℝ)|) :=
      add_le_add le_rfl (abs_add_le _ _)
    _ ≤ dynamicFullPNTZeroTailNorm H (m : ℝ) +
        (|actualPNTClosedRealAxisRelativeTerm (m : ℝ)| +
          |actualPNTExplicitFormulaRelativeRemainder H (m : ℝ)|) :=
      add_le_add hfinite le_rfl
    _ ≤ classicalDyadicCarlsonFullZeroTailMajorant
            E eta C kappa D rate m +
        (|actualPNTClosedRealAxisRelativeTerm (m : ℝ)| +
          selectedClassicalAdmissibleNaturalRemainderUpperBound
            b selection m) :=
      add_le_add hfullm (add_le_add le_rfl hremainderM)
    _ = classicalDyadicCarlsonFullPNTErrorMajorant
        b selection E eta C kappa D rate m := by
      unfold classicalDyadicCarlsonFullPNTErrorMajorant
      ring

lemma exists_selectedClassicalAdmissibleDyadicCarlsonQuantitativeFullPNTErrorMajorant :
    ∃ b rate D : ℝ,
      0 < b ∧ 0 < rate ∧ 0 < D ∧
      IsCarlsonMovingDyadicLogPowerGap
        (classicalAdmissibleDyadicCarlsonGapWidth rate) ∧
      ∀ selection : UniformNaturalPointGoodHeightSelection,
        IsSelectedHeightDynamicZeroFree
          (selectedClassicalAdmissibleGoodHeight b selection)
          (classicalAdmissibleDyadicCarlsonGapWidth rate) ∧
        ∃ E eta C kappa : ℝ,
          0 ≤ E ∧ 0 < eta ∧ 0 ≤ C ∧ 0 < kappa ∧
          Tendsto
            (classicalDyadicCarlsonFullPNTErrorMajorant
              b selection E eta C kappa D rate) atTop (nhds 0) ∧
          ∀ᶠ m : ℕ in atTop,
            |relativeChebyshevPsi0Error (m : ℝ)| ≤
              classicalDyadicCarlsonFullPNTErrorMajorant
                b selection E eta C kappa D rate m := by
  rcases
      exists_selectedClassicalAdmissibleDyadicCarlsonQuantitativeFullZeroTailMajorant with
    ⟨b, rate, D, hb, hrate, hD, hgap, hselected⟩
  refine ⟨b, rate, D, hb, hrate, hD, hgap, ?_⟩
  intro selection
  rcases hselected selection with
    ⟨hzeroFree, E, eta, C, kappa, hE, heta, hC, hkappa,
      hzeroMajorant, hfull⟩
  have hremainder :=
    eventually_abs_selectedClassicalAdmissibleGoodHeight_actualRemainder_le
      hb selection
  refine ⟨hzeroFree, E, eta, C, kappa, hE, heta, hC, hkappa,
    tendsto_classicalDyadicCarlsonFullPNTErrorMajorant_zero
      selection hb hE heta hC hkappa hrate, ?_⟩
  exact eventually_abs_relativeChebyshevPsi0Error_le_classicalFullPNTMajorant
    selection hfull hremainder

end PrimeNumberTheorem
