import PrimeNumberTheorem.ZeroDensityLayerBudgetActualClassicalDyadicCarlsonQuantitativeFullPNT

open Filter Real Complex
open scoped Topology BigOperators

namespace PrimeNumberTheorem

noncomputable def classicalClosedLogRelativeMajorant (m : ℕ) : ℝ :=
  ‖(1 / 2 : ℂ) *
    (Real.log (1 - (m : ℝ) ^ (-2 : ℝ)) : ℂ)‖ / (m : ℝ)

lemma tendsto_classicalClosedLogRelativeMajorant_zero :
    Tendsto classicalClosedLogRelativeMajorant atTop (nhds 0) := by
  have h := selectedNaturalClosedLogRelative_targetNegligible
    (show (0 : ℝ) < 1 by norm_num)
  unfold NaturalPointTargetAmplitudeNegligible at h
  have habs : Tendsto
      (fun m : ℕ => |classicalClosedLogRelativeMajorant m|)
      atTop (nhds 0) := by
    simpa [classicalClosedLogRelativeMajorant, targetZeroPowerAmplitude] using h
  apply habs.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  exact abs_of_nonneg (by
    unfold classicalClosedLogRelativeMajorant
    exact div_nonneg (norm_nonneg _) hmR.le)

noncomputable def classicalAdmissibleClosedFormNaturalRemainderMajorant
    (b : ℝ) (selection : UniformNaturalPointGoodHeightSelection)
    (m : ℕ) : ℝ :=
  cofinalPNTZeroDepthRelativeRemainderMajorant selection.constant
      (classicalAdmissibleBalancedRate b) m +
    classicalClosedLogRelativeMajorant m

lemma eventually_selectedClassicalNaturalRemainderUpperBound_le_closedForm
    {b : ℝ} (hb : 0 < b)
    (selection : UniformNaturalPointGoodHeightSelection) :
    ∀ᶠ m : ℕ in atTop,
      selectedClassicalAdmissibleNaturalRemainderUpperBound b selection m ≤
        classicalAdmissibleClosedFormNaturalRemainderMajorant b selection m := by
  have hrate := classicalAdmissibleBalancedRate_pos hb
  have hheight := tendsto_natCast_atTop_atTop.eventually
    (eventually_selectedClassicalAdmissibleGoodHeight_mem hb selection)
  filter_upwards [eventually_ge_atTop (3 : ℕ),
      tendsto_pntSqrtLog_atTop.eventually
        (eventually_ge_atTop
          (max 1 (Real.log 6 / classicalAdmissibleBalancedRate b))),
      hheight] with m hm hscale hmT
  have hcontour :=
    cofinalPNTFormulaRemainderBound_zero_relative_le_majorant
      selection.constant_nonneg hrate
      (classicalAdmissibleBalancedRate_le_one b)
      hm hscale hmT
  unfold selectedClassicalAdmissibleNaturalRemainderUpperBound
    classicalAdmissibleClosedFormNaturalRemainderMajorant
    classicalClosedLogRelativeMajorant
  rw [add_div]
  exact add_le_add hcontour le_rfl

noncomputable def classicalDyadicCarlsonClosedFormFullPNTErrorMajorant
    (b : ℝ) (selection : UniformNaturalPointGoodHeightSelection)
    (E eta C kappa D rate : ℝ) (m : ℕ) : ℝ :=
  classicalDyadicCarlsonFullZeroTailMajorant E eta C kappa D rate m +
    |actualPNTClosedRealAxisRelativeTerm (m : ℝ)| +
    classicalAdmissibleClosedFormNaturalRemainderMajorant b selection m

lemma tendsto_classicalDyadicCarlsonClosedFormFullPNTErrorMajorant_zero
    {b E eta C kappa D rate : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hb : 0 < b) (hE : 0 ≤ E) (heta : 0 < eta)
    (hC : 0 ≤ C) (hkappa : 0 < kappa) (hrate : 0 < rate) :
    Tendsto
      (classicalDyadicCarlsonClosedFormFullPNTErrorMajorant
        b selection E eta C kappa D rate) atTop (nhds 0) := by
  have hzeros := tendsto_classicalDyadicCarlsonFullZeroTailMajorant_zero
    (D := D) hE heta hC hkappa hrate
  have hcontour := cofinalPNTZeroDepthRelativeRemainderMajorant_tendsto
    (C := selection.constant) (classicalAdmissibleBalancedRate_pos hb)
  have hremainder : Tendsto
      (classicalAdmissibleClosedFormNaturalRemainderMajorant b selection)
      atTop (nhds 0) := by
    simpa [classicalAdmissibleClosedFormNaturalRemainderMajorant] using
      hcontour.add tendsto_classicalClosedLogRelativeMajorant_zero
  simpa [classicalDyadicCarlsonClosedFormFullPNTErrorMajorant] using
    (hzeros.add tendsto_abs_actualPNTClosedRealAxisRelativeTerm_natural_zero).add
      hremainder

lemma eventually_classicalFullPNTMajorant_le_closedForm
    {b E eta C kappa D rate : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hremainder : ∀ᶠ m : ℕ in atTop,
      selectedClassicalAdmissibleNaturalRemainderUpperBound b selection m ≤
        classicalAdmissibleClosedFormNaturalRemainderMajorant b selection m) :
    ∀ᶠ m : ℕ in atTop,
      classicalDyadicCarlsonFullPNTErrorMajorant
          b selection E eta C kappa D rate m ≤
        classicalDyadicCarlsonClosedFormFullPNTErrorMajorant
          b selection E eta C kappa D rate m := by
  filter_upwards [hremainder] with m hm
  unfold classicalDyadicCarlsonFullPNTErrorMajorant
    classicalDyadicCarlsonClosedFormFullPNTErrorMajorant
  exact add_le_add le_rfl hm

lemma exists_selectedClassicalAdmissibleDyadicCarlsonClosedFormFullPNTErrorMajorant :
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
            (classicalDyadicCarlsonClosedFormFullPNTErrorMajorant
              b selection E eta C kappa D rate) atTop (nhds 0) ∧
          ∀ᶠ m : ℕ in atTop,
            |relativeChebyshevPsi0Error (m : ℝ)| ≤
              classicalDyadicCarlsonClosedFormFullPNTErrorMajorant
                b selection E eta C kappa D rate m := by
  rcases
      exists_selectedClassicalAdmissibleDyadicCarlsonQuantitativeFullPNTErrorMajorant with
    ⟨b, rate, D, hb, hrate, hD, hgap, hselected⟩
  refine ⟨b, rate, D, hb, hrate, hD, hgap, ?_⟩
  intro selection
  rcases hselected selection with
    ⟨hzeroFree, E, eta, C, kappa, hE, heta, hC, hkappa,
      hmajorantZero, herror⟩
  have hremainder :=
    eventually_selectedClassicalNaturalRemainderUpperBound_le_closedForm
      hb selection
  have hmajorantLe :=
    eventually_classicalFullPNTMajorant_le_closedForm
      (E := E) (eta := eta) (C := C) (kappa := kappa)
      (D := D) (rate := rate) selection hremainder
  refine ⟨hzeroFree, E, eta, C, kappa, hE, heta, hC, hkappa,
    tendsto_classicalDyadicCarlsonClosedFormFullPNTErrorMajorant_zero
      selection hb hE heta hC hkappa hrate, ?_⟩
  filter_upwards [herror, hmajorantLe] with m hm hle
  exact hm.trans hle

end PrimeNumberTheorem
