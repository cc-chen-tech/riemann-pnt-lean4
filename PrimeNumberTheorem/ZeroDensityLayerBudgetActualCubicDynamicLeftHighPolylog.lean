import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicDynamicLeftHigh

namespace PrimeNumberTheorem

open Complex
open ExplicitFormulaResidues

/-- The explicit Archimedean terms in the high-height dynamic-left estimate
are absorbed into one uniform square-logarithmic budget at the outer height.
No power of `H` is lost. -/
theorem exists_dynamicCubicLeftBoundary_high_logDeriv_le_log_sq :
    ∃ b C T0 : ℝ, 0 < b ∧ 0 ≤ C ∧ 4 ≤ T0 ∧
      ∀ H : ℝ, T0 ≤ H →
        let a := dynamicCubicLeftBoundary b H
        0 < a ∧ a ≤ 1 / 2 ∧
          ∀ t : ℝ, T0 ≤ |t| → |t| ≤ H →
            let s : ℂ := (a : ℂ) + I * t
            riemannZeta s ≠ 0 ∧ riemannZeta (1 - s) ≠ 0 ∧
              ‖logDeriv riemannZeta s‖ ≤
                C * (1 + Real.log (H + 6)) ^ 2 := by
  rcases exists_dynamicCubicLeftBoundary_high_logDeriv_budget with
    ⟨b, C0, T0, hb, hC0, hT0, hbase⟩
  let A : ℝ := ‖Complex.log Real.pi‖ +
    2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 4) + Real.pi
  let C : ℝ := C0 + A + 2
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨b, C, T0, hb, hC, hT0, ?_⟩
  intro H hH
  rcases hbase H hH with ⟨ha, haHalf, hpoint⟩
  refine ⟨ha, haHalf, ?_⟩
  intro t ht htH
  rcases hpoint t ht htH with ⟨hzs, hz1s, hraw⟩
  let a : ℝ := dynamicCubicLeftBoundary b H
  let s : ℂ := (a : ℂ) + I * t
  let LH : ℝ := Real.log (H + 6)
  let L : ℝ := 1 + LH
  have hH4 : 4 ≤ H := hT0.trans hH
  have hLH : 0 ≤ LH := by
    dsimp [LH]
    exact Real.log_nonneg (by linarith)
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hLsq : 1 ≤ L ^ 2 := by nlinarith
  have hLleSq : L ≤ L ^ 2 := by nlinarith
  have htPos : 0 < |t| := lt_of_lt_of_le (by norm_num) (hT0.trans ht)
  have hlogt : Real.log |t| ≤ LH := by
    dsimp [LH]
    apply Real.log_le_log htPos
    linarith
  have hlogtNonneg : 0 ≤ Real.log |t| :=
    Real.log_nonneg (by linarith [hT0.trans ht])
  have hlogtSq : (Real.log |t|) ^ 2 ≤ L ^ 2 := by
    have : Real.log |t| ≤ L := by dsimp [L]; linarith
    nlinarith
  have hsNorm : ‖s‖ ≤ 1 / 2 + H := by
    calc
      ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ = |a| + |t| := by simp [s]
      _ = a + |t| := by rw [abs_of_pos ha]
      _ ≤ 1 / 2 + H := add_le_add haHalf htH
  have harg1 : ‖(1 - s) / 2 + 1‖ + 1 ≤ H + 6 := by
    calc
      ‖(1 - s) / 2 + 1‖ + 1 ≤
          (‖(1 - s) / 2‖ + ‖(1 : ℂ)‖) + 1 :=
        by gcongr; exact norm_add_le _ _
      _ = ‖1 - s‖ / 2 + 2 := by rw [norm_div]; norm_num; ring
      _ ≤ (1 + ‖s‖) / 2 + 2 := by
        gcongr
        simpa using (norm_sub_le (1 : ℂ) s)
      _ ≤ H + 6 := by nlinarith [hsNorm]
  have harg2 : ‖1 - s / 2 + 1‖ + 1 ≤ H + 6 := by
    calc
      ‖1 - s / 2 + 1‖ + 1 = ‖(2 : ℂ) - s / 2‖ + 1 := by ring_nf
      _ ≤ (‖(2 : ℂ)‖ + ‖s / 2‖) + 1 :=
        by gcongr; exact norm_sub_le _ _
      _ = 3 + ‖s‖ / 2 := by rw [norm_div]; norm_num; ring
      _ ≤ H + 6 := by nlinarith [hsNorm]
  have hlog1 : Real.log (‖(1 - s) / 2 + 1‖ + 1) ≤ L := by
    have hpos : 0 < ‖(1 - s) / 2 + 1‖ + 1 := by positivity
    have := Real.log_le_log hpos harg1
    dsimp [L, LH]
    linarith
  have hlog2 : Real.log (‖1 - s / 2 + 1‖ + 1) ≤ L := by
    have hpos : 0 < ‖1 - s / 2 + 1‖ + 1 := by positivity
    have := Real.log_le_log hpos harg2
    dsimp [L, LH]
    linarith
  have hmain : C0 * (Real.log |t|) ^ 2 ≤ C0 * L ^ 2 :=
    mul_le_mul_of_nonneg_left hlogtSq hC0
  have hAL : A ≤ A * L ^ 2 := by
    simpa using mul_le_mul_of_nonneg_left hLsq hA
  have htwoL : 2 * L ≤ 2 * L ^ 2 := by nlinarith
  refine ⟨hzs, hz1s, hraw.trans ?_⟩
  change
    C0 * (Real.log |t|) ^ 2 + ‖Complex.log Real.pi‖ +
          (‖(Real.eulerMascheroniConstant : ℂ)‖ + 4 +
            Real.log (‖(1 - s) / 2 + 1‖ + 1)) +
        (‖(Real.eulerMascheroniConstant : ℂ)‖ + 4 +
          Real.log (‖1 - s / 2 + 1‖ + 1)) + Real.pi
      ≤ C * L ^ 2
  dsimp [C, A]
  nlinarith

end PrimeNumberTheorem
