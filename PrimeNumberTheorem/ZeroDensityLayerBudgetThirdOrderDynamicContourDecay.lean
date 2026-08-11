import PrimeNumberTheorem.ZeroDensityLayerBudgetThirdOrderContourRemainder
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicCarlsonQuantitativeMovingTail
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTHybridActualLowLayerDecay

open Complex MeasureTheory Set Filter Topology
open scoped ArithmeticFunction BigOperators LSeries.notation

namespace PrimeNumberTheorem.ExplicitFormulaResidues

theorem exists_uniform_goodHeight_Icc_norm_thirdOrderContourRemainder_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {x c : ℝ}, 1 < x → 1 < c → c ≤ 2 →
      ∀ A : ℝ, 4 ≤ A →
        ∃ T ∈ Set.Icc A (A + 1),
          ExplicitFormulaAux.goodHeight T ∧
            ‖thirdOrderContourRemainder x (-1) c
                (T / (2 * Real.pi))‖ ≤
              thirdOrderGoodHeightContourRemainderMajorant x C A T c := by
  rcases exists_goodHeight_Icc_norm_logDeriv_central_band_le_log_sq with
    ⟨C, hC, hchoose⟩
  refine ⟨C, hC, ?_⟩
  intro x c hx hc hc2 A hA
  rcases hchoose A hA with ⟨T, hTmem, hgood, hlog⟩
  refine ⟨T, hTmem, hgood, ?_⟩
  have hTpos : 0 < T := by linarith [hTmem.1]
  have hTabs : |T| = T := abs_of_pos hTpos
  have hscale : 2 * Real.pi * (T / (2 * Real.pi)) = T := by
    field_simp [Real.pi_ne_zero]
  have hK : 0 ≤ C * (1 + Real.log (A + 6)) ^ 2 :=
    mul_nonneg hC (sq_nonneg _)
  let H : ℝ := C * x ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T ^ 3
  have hhorizontal (t : ℝ) (ht : |t| = T) :
      ‖∫ σ : ℝ in (-1)..c,
          thirdOrderExplicitFormulaIntegrand x ((σ : ℂ) + I * t)‖ ≤
        H * (c + 1) := by
    have htpos : 0 < |t| := by rw [ht]; exact hTpos
    have hbound := norm_integral_thirdOrderHorizontal_le_of_logDeriv
      (x := x) (a := -1) (c := c) (b := 2) (t := t)
      (K := C * (1 + Real.log (A + 6)) ^ 2)
      hx.le (by linarith) hc2 htpos hK (fun σ hσ => by
        rw [Set.uIoc_of_le (by linarith)] at hσ
        exact hlog t ht σ hσ.1.le (hσ.2.trans hc2))
    rw [ht] at hbound
    simpa [H, mul_comm, mul_left_comm, mul_assoc] using hbound
  have htop := hhorizontal T hTabs
  have hbottom := hhorizontal (-T) (by simpa [abs_neg] using hTabs)
  have hleft := norm_integral_thirdOrderOddVertical_le (N := 0) hx hTpos.le
  have hleft' :
      ‖∫ t : ℝ in (-T)..T,
          thirdOrderExplicitFormulaIntegrand x
            (((-1 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
        thirdOrderOddVerticalBound x 0 T * (2 * T) := by
    simpa using hleft
  have hedge := norm_thirdOrderContourRemainder_le_edges
    x (-1) c (T / (2 * Real.pi))
  rw [hscale] at hedge
  have hbottom' :
      ‖∫ σ : ℝ in (-1)..c,
          thirdOrderExplicitFormulaIntegrand x ((σ : ℂ) + (-T : ℝ) * I)‖ ≤
        H * (c + 1) := by
    simpa [mul_comm] using hbottom
  have htop' :
      ‖∫ σ : ℝ in (-1)..c,
          thirdOrderExplicitFormulaIntegrand x ((σ : ℂ) + (T : ℝ) * I)‖ ≤
        H * (c + 1) := by
    simpa [mul_comm] using htop
  apply hedge.trans
  unfold thirdOrderGoodHeightContourRemainderMajorant
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ H * (c + 1) + H * (c + 1) +
        thirdOrderOddVerticalBound x 0 T * (2 * T) := by
      exact add_le_add (add_le_add hbottom' htop') hleft'
    _ = 2 * ((C * x ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T ^ 3) *
          (c + 1)) + thirdOrderOddVerticalBound x 0 T * (2 * T) := by
      dsimp [H]
      ring

noncomputable def thirdOrderDynamicContourLogPowerMajorant
    (C alpha c x : ℝ) : ℝ :=
  let B := vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
    2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3) + Real.pi
  ((2 * (C * (c + 1) * (alpha + 2) ^ 2)) *
      (x ^ (2 - 3 * alpha) * Real.log x ^ 8) +
    (2 * (B + 2) * (alpha + 2)) *
      (x ^ (alpha - 1) * Real.log x ^ 4 +
        x ^ (-1 : ℝ) * Real.log x ^ 4)) / (2 * Real.pi)

theorem tendsto_thirdOrderDynamicContourLogPowerMajorant
    {C alpha c : ℝ} (halpha23 : 2 / 3 < alpha) (halpha1 : alpha < 1) :
    Tendsto (thirdOrderDynamicContourLogPowerMajorant C alpha c)
      atTop (nhds 0) := by
  have hfirstExp : 2 - 3 * alpha < 0 := by linarith
  have hsecondExp : alpha - 1 < 0 := by linarith
  have hfirst :
      Tendsto (fun x : ℝ => x ^ (2 - 3 * alpha) * Real.log x ^ 8)
        atTop (nhds 0) := by
    apply PrimeNumberTheorem.tendsto_rpow_mul_log_pow_atTop_nhds_zero
      (epsilon := -(2 - 3 * alpha) / 2) 8
    · linarith
    · linarith
  have hsecond :
      Tendsto (fun x : ℝ => x ^ (alpha - 1) * Real.log x ^ 4)
        atTop (nhds 0) := by
    apply PrimeNumberTheorem.tendsto_rpow_mul_log_pow_atTop_nhds_zero
      (epsilon := -(alpha - 1) / 2) 4
    · linarith
    · linarith
  have hthird :
      Tendsto (fun x : ℝ => x ^ (-1 : ℝ) * Real.log x ^ 4)
        atTop (nhds 0) := by
    apply PrimeNumberTheorem.tendsto_rpow_mul_log_pow_atTop_nhds_zero
      (epsilon := (1 : ℝ) / 2) 4
    · norm_num
    · norm_num
  unfold thirdOrderDynamicContourLogPowerMajorant
  dsimp only
  change Tendsto (fun x : ℝ =>
    (2 * (C * (c + 1) * (alpha + 2) ^ 2) *
        (x ^ (2 - 3 * alpha) * Real.log x ^ 8) +
      (2 * (vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
        2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3) +
        Real.pi + 2) * (alpha + 2)) *
        (x ^ (alpha - 1) * Real.log x ^ 4 +
          x ^ (-1 : ℝ) * Real.log x ^ 4)) / (2 * Real.pi))
    atTop (nhds 0)
  simpa only [mul_zero, add_zero, zero_div] using
    (((hfirst.const_mul
      (2 * (C * (c + 1) * (alpha + 2) ^ 2))).add
      ((hsecond.add hthird).const_mul
        (2 * (vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
          2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3) +
          Real.pi + 2) * (alpha + 2)))).div_const (2 * Real.pi))


private lemma thirdOrderOddVerticalBound_zero_eq
    (x T : ℝ) :
    thirdOrderOddVerticalBound x 0 T =
      (vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
        2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3) +
        Real.pi + 2 * Real.log (T + 4)) * x ^ (-1 : ℝ) := by
  unfold thirdOrderOddVerticalBound secondOrderOddVerticalBound
  norm_num
  left
  ring

private lemma rpow_two_div_rpow_alpha_cube
    {x alpha : ℝ} (hx : 0 < x) :
    x ^ (2 : ℝ) / (x ^ alpha) ^ 3 = x ^ (2 - 3 * alpha) := by
  rw [Real.rpow_sub hx]
  congr 1
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hx.le]
  congr 1
  ring

private lemma rpow_alpha_mul_rpow_neg_one
    {x alpha : ℝ} (hx : 0 < x) :
    x ^ alpha * x ^ (-1 : ℝ) = x ^ (alpha - 1) := by
  rw [← Real.rpow_add hx]
  ring

theorem thirdOrderGoodHeightContourRemainderMajorant_le_dynamic
    {x C alpha c T : ℝ}
    (hx : 1 < x) (hC : 0 ≤ C) (hc : 1 < c)
    (halpha : 0 < alpha)
    (hT : T ∈ Set.Icc (x ^ alpha) (x ^ alpha + 1))
    (hlog :
      1 + Real.log (x ^ alpha + 6) ≤
        (alpha + 2) * Real.log x ^ 4) :
    thirdOrderGoodHeightContourRemainderMajorant
        x C (x ^ alpha) T c ≤
      thirdOrderDynamicContourLogPowerMajorant C alpha c x := by
  let B : ℝ := vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
    2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3) + Real.pi
  have hxpos : 0 < x := lt_trans (by norm_num) hx
  have hxnonneg : 0 ≤ x := hxpos.le
  have hApos : 0 < x ^ alpha := Real.rpow_pos_of_pos hxpos _
  have hTone : 1 ≤ x ^ alpha := Real.one_le_rpow hx.le halpha.le
  have hTpos : 0 < T := hApos.trans_le hT.1
  have hT3 :
      (x ^ alpha) ^ 3 ≤ T ^ 3 :=
    pow_le_pow_left₀ hApos.le hT.1 3
  have hlogA : 0 ≤ Real.log (x ^ alpha + 6) := by
    apply Real.log_nonneg
    linarith
  have hLnonneg : 0 ≤ 1 + Real.log (x ^ alpha + 6) := by linarith
  have hDnonneg : 0 ≤ (alpha + 2) * Real.log x ^ 4 :=
    hLnonneg.trans hlog
  have hlogSq :
      (1 + Real.log (x ^ alpha + 6)) ^ 2 ≤
        ((alpha + 2) * Real.log x ^ 4) ^ 2 :=
    (sq_le_sq₀ hLnonneg hDnonneg).2 hlog
  have hhorizontal :
      (C * x ^ (2 : ℝ) *
          (1 + Real.log (x ^ alpha + 6)) ^ 2 / T ^ 3) *
          (c + 1) ≤
        C * (c + 1) * (alpha + 2) ^ 2 *
          (x ^ (2 - 3 * alpha) * Real.log x ^ 8) := by
    have hnum :
        0 ≤ C * x ^ (2 : ℝ) *
          (1 + Real.log (x ^ alpha + 6)) ^ 2 := by positivity
    calc
      _ ≤ (C * x ^ (2 : ℝ) *
          (1 + Real.log (x ^ alpha + 6)) ^ 2 /
            (x ^ alpha) ^ 3) * (c + 1) := by
        gcongr
      _ ≤ (C * x ^ (2 : ℝ) *
          ((alpha + 2) * Real.log x ^ 4) ^ 2 /
            (x ^ alpha) ^ 3) * (c + 1) := by
        gcongr
      _ = C * (c + 1) * (alpha + 2) ^ 2 *
          (x ^ (2 - 3 * alpha) * Real.log x ^ 8) := by
        rw [← rpow_two_div_rpow_alpha_cube hxpos]
        ring
  have hlogT :
      Real.log (T + 4) ≤ Real.log (x ^ alpha + 6) := by
    apply Real.strictMonoOn_log.monotoneOn
    · exact mem_Ioi.mpr (by linarith)
    · exact mem_Ioi.mpr (by linarith)
    · linarith [hT.2]
  have hseries : 0 ≤ vonMangoldtLSeriesNorm 1 :=
    tsum_nonneg (fun _ => norm_nonneg _)
  have hBnonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hQ :
      B + 2 * Real.log (T + 4) ≤
        (B + 2) * (1 + Real.log (x ^ alpha + 6)) := by
    calc
      _ ≤ B + 2 * Real.log (x ^ alpha + 6) := by linarith
      _ ≤ (B + 2) * (1 + Real.log (x ^ alpha + 6)) := by
        nlinarith [mul_nonneg hBnonneg hlogA]
  have hQnonneg : 0 ≤ B + 2 * Real.log (T + 4) := by
    have : 0 ≤ Real.log (T + 4) := Real.log_nonneg (by linarith)
    positivity
  have hleft :
      thirdOrderOddVerticalBound x 0 T * (2 * T) ≤
        (2 * (B + 2) * (alpha + 2)) *
          (x ^ (alpha - 1) * Real.log x ^ 4 +
            x ^ (-1 : ℝ) * Real.log x ^ 4) := by
    rw [thirdOrderOddVerticalBound_zero_eq]
    change (B + 2 * Real.log (T + 4)) * x ^ (-1 : ℝ) * (2 * T) ≤ _
    calc
      _ ≤ ((B + 2) * (1 + Real.log (x ^ alpha + 6))) *
          x ^ (-1 : ℝ) * (2 * T) := by
        gcongr
      _ ≤ ((B + 2) * (1 + Real.log (x ^ alpha + 6))) *
          x ^ (-1 : ℝ) * (2 * (x ^ alpha + 1)) := by
        gcongr
        exact hT.2
      _ ≤ ((B + 2) * ((alpha + 2) * Real.log x ^ 4)) *
          x ^ (-1 : ℝ) * (2 * (x ^ alpha + 1)) := by
        gcongr
      _ = (2 * (B + 2) * (alpha + 2)) *
          (x ^ (alpha - 1) * Real.log x ^ 4 +
            x ^ (-1 : ℝ) * Real.log x ^ 4) := by
        rw [← rpow_alpha_mul_rpow_neg_one hxpos]
        ring
  unfold thirdOrderGoodHeightContourRemainderMajorant
  unfold thirdOrderDynamicContourLogPowerMajorant
  dsimp only
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply add_le_add
  · nlinarith [hhorizontal]
  · exact hleft

theorem exists_uniform_eventually_goodHeight_norm_thirdOrderContourRemainder_lt
    {alpha c : ℝ}
    (halpha23 : 2 / 3 < alpha) (halpha1 : alpha < 1)
    (hc : 1 < c) (hc2 : c ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x : ℝ in atTop,
        ∃ T ∈ Set.Icc (x ^ alpha) (x ^ alpha + 1),
          ExplicitFormulaAux.goodHeight T ∧
            ‖thirdOrderContourRemainder x (-1) c
                (T / (2 * Real.pi))‖ < ε := by
  rcases exists_uniform_goodHeight_Icc_norm_thirdOrderContourRemainder_le with
    ⟨C, hC, huniform⟩
  refine ⟨C, hC, ?_⟩
  intro ε hε
  have halpha : 0 < alpha := by linarith
  have hheight :
      ∀ᶠ x : ℝ in atTop, 4 ≤ x ^ alpha :=
    (tendsto_rpow_atTop halpha).eventually (eventually_ge_atTop 4)
  have hlog :=
    PrimeNumberTheorem.eventually_one_add_log_polynomialHeight_add_six_le_log_four
      halpha
  have hmajorant :=
    tendsto_thirdOrderDynamicContourLogPowerMajorant
      (C := C) (c := c) halpha23 halpha1
  have hsmall :
      ∀ᶠ x : ℝ in atTop,
        thirdOrderDynamicContourLogPowerMajorant C alpha c x < ε :=
    (tendsto_order.1 hmajorant).2 ε hε
  filter_upwards [eventually_gt_atTop (1 : ℝ), hheight, hlog, hsmall] with
      x hx hA hxlog hxsmall
  rcases huniform hx hc hc2 (x ^ alpha) hA with
    ⟨T, hT, hgood, hremainder⟩
  refine ⟨T, hT, hgood, ?_⟩
  exact (hremainder.trans
    (thirdOrderGoodHeightContourRemainderMajorant_le_dynamic
      hx hC hc halpha hT hxlog)).trans_lt hxsmall

end PrimeNumberTheorem.ExplicitFormulaResidues
