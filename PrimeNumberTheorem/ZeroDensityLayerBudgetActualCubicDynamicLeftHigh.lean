import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicContourBudget
import PrimeNumberTheorem.CentralHorizontalEdge

namespace PrimeNumberTheorem

open Complex
open ExplicitFormulaResidues

/-- The dynamic positive left boundary admits an actual high-height
logarithmic-derivative budget.  The reflected point lies in the proved inner
zero-free region, while the left point is excluded by the finite-height
two-sided zero geometry.  The fixed low-height segment is deliberately not
included in this theorem. -/
theorem exists_dynamicCubicLeftBoundary_high_logDeriv_budget :
    ∃ b C T0 : ℝ, 0 < b ∧ 0 ≤ C ∧ 4 ≤ T0 ∧
      ∀ H : ℝ, T0 ≤ H →
        let a := dynamicCubicLeftBoundary b H
        0 < a ∧ a ≤ 1 / 2 ∧
          ∀ t : ℝ, T0 ≤ |t| → |t| ≤ H →
            let s : ℂ := (a : ℂ) + I * t
            riemannZeta s ≠ 0 ∧ riemannZeta (1 - s) ≠ 0 ∧
              ‖logDeriv riemannZeta s‖ ≤
                C * (Real.log |t|) ^ 2 + ‖Complex.log Real.pi‖ +
                  (‖(Real.eulerMascheroniConstant : ℂ)‖ + 4 +
                    Real.log (‖(1 - s) / 2 + 1‖ + 1)) +
                  (‖(Real.eulerMascheroniConstant : ℂ)‖ + 4 +
                    Real.log (‖1 - s / 2 + 1‖ + 1)) + Real.pi := by
  rcases ExplicitFormulaResidues.exists_dynamicCubicLeftBoundary_nontrivialZero_re_gt with
    ⟨b0, hb0, hleft⟩
  rcases
      ZeroFreeRegion.exists_riemannZeta_ne_zero_and_norm_logDeriv_le_log_sq_on_inner_zeroFreeRegion
      with ⟨c, C, T1, hc, hC, hT1, hright⟩
  let b : ℝ := min b0 (min c (Real.log 10))
  let T0 : ℝ := max 4 T1
  have hlog10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hb : 0 < b := by
    dsimp [b]
    exact lt_min hb0 (lt_min hc hlog10)
  have hb_b0 : b ≤ b0 := by exact min_le_left _ _
  have hb_c : b ≤ c := by
    exact (min_le_right b0 _).trans (min_le_left c _)
  have hb_log10 : b ≤ Real.log 10 := by
    exact (min_le_right b0 _).trans (min_le_right c _)
  have hT0 : 4 ≤ T0 := le_max_left _ _
  have hT1T0 : T1 ≤ T0 := le_max_right _ _
  refine ⟨b, C, T0, hb, hC, hT0, ?_⟩
  intro H hH
  have hH4 : 4 ≤ H := hT0.trans hH
  have hH6 : (0 : ℝ) < H + 6 := by linarith
  have hLH : 0 < Real.log (H + 6) :=
    Real.log_pos (by linarith : (1 : ℝ) < H + 6)
  have hlog10H : Real.log 10 ≤ Real.log (H + 6) := by
    exact Real.log_le_log (by norm_num) (by linarith)
  rcases hleft H hH4 with ⟨_ha0, hzeroLeft⟩
  let a : ℝ := dynamicCubicLeftBoundary b H
  have ha : 0 < a := by
    dsimp [a, dynamicCubicLeftBoundary]
    positivity
  have ha_le_half : a ≤ 1 / 2 := by
    rw [show a = b / (2 * Real.log (H + 6)) by
      rfl, div_le_iff₀ (mul_pos (by norm_num) hLH)]
    nlinarith [hb_log10.trans hlog10H]
  have ha_le_a0 : a ≤ dynamicCubicLeftBoundary b0 H := by
    dsimp [a, dynamicCubicLeftBoundary]
    exact div_le_div_of_nonneg_right hb_b0 (mul_nonneg (by norm_num) hLH.le)
  refine ⟨ha, ha_le_half, ?_⟩
  intro t ht htH
  let s : ℂ := (a : ℂ) + I * t
  have ha_lt_one : a < 1 := lt_of_le_of_lt ha_le_half (by norm_num)
  have hzs : riemannZeta s ≠ 0 := by
    intro hzs0
    have hsZero : RiemannHypothesis.IsNontrivialZero s := by
      refine ⟨hzs0, ?_, ?_⟩
      · simpa [s] using ha
      · simpa [s] using ha_lt_one
    have hsRight := hzeroLeft s hsZero (by simpa [s] using htH)
    have : dynamicCubicLeftBoundary b0 H < a := by simpa [s] using hsRight
    exact (not_lt_of_ge ha_le_a0) this
  have hT1t : T1 ≤ |-t| := by
    simpa using hT1T0.trans ht
  have hLt : 0 < Real.log |t| := by
    have ht2 : (2 : ℝ) ≤ |t| := hT1.trans (hT1T0.trans ht)
    exact ZeroFreeRegion.log_abs_pos_of_two_le ht2
  have hlogtH : Real.log |t| ≤ Real.log (H + 6) := by
    apply Real.log_le_log
    · have ht4 : (4 : ℝ) ≤ |t| := hT0.trans ht
      linarith
    · linarith
  have ha_inner : a ≤ c / (2 * Real.log |t|) := by
    calc
      a = b / (2 * Real.log (H + 6)) := rfl
      _ ≤ c / (2 * Real.log (H + 6)) :=
        div_le_div_of_nonneg_right hb_c (mul_nonneg (by norm_num) hLH.le)
      _ ≤ c / (2 * Real.log |t|) := by
        exact div_le_div_of_nonneg_left hc.le (mul_pos (by norm_num) hLt)
          (by nlinarith)
  have hright0 := hright (1 - a) (-t) hT1t (by
    simpa [abs_neg] using (show 1 - c / (2 * Real.log |t|) ≤ 1 - a by
      linarith)) (by linarith)
  have hreflect : (((1 - a : ℝ) : ℂ) + I * (-t)) = 1 - s := by
    apply Complex.ext <;> simp [s]
  have hrightNonzero : riemannZeta (1 - s) ≠ 0 := by
    rw [← hreflect]
    simpa using hright0.1
  have hrightBound : ‖logDeriv riemannZeta (1 - s)‖ ≤
      C * (Real.log |t|) ^ 2 := by
    rw [← hreflect]
    simpa using hright0.2
  have hleftBound :=
    ExplicitFormulaResidues.norm_logDeriv_riemannZeta_central_left_le
      (K := C * (Real.log |t|) ^ 2) ha_le_half
      (by exact (show (2 : ℝ) ≤ 4 from by norm_num).trans (hT0.trans ht))
      hzs hrightNonzero hrightBound
  refine ⟨hzs, hrightNonzero, ?_⟩
  simpa [s] using hleftBound

end PrimeNumberTheorem
