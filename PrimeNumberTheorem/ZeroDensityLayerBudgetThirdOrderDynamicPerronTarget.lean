import PrimeNumberTheorem.ZeroDensityLayerBudgetThirdOrderLSeriesBridge
import PrimeNumberTheorem.VonMangoldtLSeriesNorm
import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonLogAbsorption

open Complex Set Filter Topology
open scoped ArithmeticFunction BigOperators LSeries.notation

namespace PrimeNumberTheorem

noncomputable def thirdOrderPerronErrorMajorant
    (x c W : ℝ) : ℝ :=
  ∑' n : ℕ, vonMangoldt n * (x / n) ^ c /
    (8 * Real.pi ^ 3 * W ^ 2)

theorem thirdOrderPerronErrorMajorant_eq
    {x c W : ℝ} (hx : 0 < x) :
    thirdOrderPerronErrorMajorant x c W =
      (x ^ c / (8 * Real.pi ^ 3 * W ^ 2)) *
        ExplicitFormulaResidues.vonMangoldtLSeriesNorm (c - 1) := by
  unfold thirdOrderPerronErrorMajorant
  unfold ExplicitFormulaResidues.vonMangoldtLSeriesNorm
  rw [show (((1 + (c - 1) : ℝ) : ℂ)) = (c : ℂ) by
    push_cast
    ring]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp [vonMangoldt_eq_mathlib]
  · have hn_pos : 0 < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    rw [LSeries.norm_term_eq]
    simp only [if_neg hn, Complex.ofReal_re]
    rw [Real.div_rpow hx.le hn_pos.le]
    rw [norm_real, Real.norm_eq_abs]
    have hv_nonneg : 0 ≤ vonMangoldt n := by
      rw [vonMangoldt_eq_mathlib]
      exact ArithmeticFunction.vonMangoldt_nonneg
    rw [← vonMangoldt_eq_mathlib, abs_of_nonneg hv_nonneg]
    ring

noncomputable def thirdOrderNormalizedDynamicPerronPowerMajorant
    (beta c x : ℝ) : ℝ :=
  (ExplicitFormulaResidues.vonMangoldtLSeriesNorm (c - 1) /
      (2 * Real.pi)) *
    x ^ (c - 3 / 2 - beta)

theorem tendsto_thirdOrderNormalizedDynamicPerronPowerMajorant
    {beta c : ℝ} (hexponent : c - 3 / 2 - beta < 0) :
    Tendsto (thirdOrderNormalizedDynamicPerronPowerMajorant beta c)
      atTop (nhds 0) := by
  simpa [thirdOrderNormalizedDynamicPerronPowerMajorant] using
    (tendsto_const_nhds.mul
      (tendsto_rpow_neg_atTop_nhds_zero hexponent))

theorem tendsto_thirdOrderNormalizedDynamicPerronPowerMajorant_of_targetRange
    {beta c : ℝ} (hbeta : 2 / 3 < beta)
    (hcTwo : c ≤ 2) :
    Tendsto (thirdOrderNormalizedDynamicPerronPowerMajorant beta c)
      atTop (nhds 0) :=
  tendsto_thirdOrderNormalizedDynamicPerronPowerMajorant
    (by linarith [hbeta, hcTwo])

private theorem rpow_normalized_thirdOrder_baseHeight
    {x beta c : ℝ} (hx : 0 < x) :
    x ^ (-beta) * x ^ c / (x ^ (3 / 4 : ℝ)) ^ 2 =
      x ^ (c - 3 / 2 - beta) := by
  have hsquare : (x ^ (3 / 4 : ℝ)) ^ 2 = x ^ (3 / 2 : ℝ) := by
    calc
      (x ^ (3 / 4 : ℝ)) ^ 2 =
          (x ^ (3 / 4 : ℝ)) ^ (2 : ℝ) := by
            rw [Real.rpow_two]
      _ = x ^ ((3 / 4 : ℝ) * 2) :=
        (Real.rpow_mul hx.le (3 / 4 : ℝ) 2).symm
      _ = x ^ (3 / 2 : ℝ) := by norm_num
  rw [hsquare, ← Real.rpow_add hx, ← Real.rpow_sub hx]
  congr 1
  ring

theorem normalized_thirdOrderPerronErrorMajorant_le_dynamic
    {beta c x T : ℝ} (hx : 1 ≤ x)
    (hT : T ∈ Icc (x ^ (3 / 4 : ℝ)) (x ^ (3 / 4 : ℝ) + 1)) :
    x ^ (-beta) *
        thirdOrderPerronErrorMajorant x c (T / (2 * Real.pi)) ≤
      thirdOrderNormalizedDynamicPerronPowerMajorant beta c x := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hbasePos : 0 < x ^ (3 / 4 : ℝ) :=
    Real.rpow_pos_of_pos hxpos _
  have hTpos : 0 < T := hbasePos.trans_le hT.1
  have hscalePos : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hWbasePos : 0 < x ^ (3 / 4 : ℝ) / (2 * Real.pi) :=
    div_pos hbasePos hscalePos
  have hWle : x ^ (3 / 4 : ℝ) / (2 * Real.pi) ≤
      T / (2 * Real.pi) :=
    div_le_div_of_nonneg_right hT.1 hscalePos.le
  have hden :
      8 * Real.pi ^ 3 * (x ^ (3 / 4 : ℝ) / (2 * Real.pi)) ^ 2 ≤
        8 * Real.pi ^ 3 * (T / (2 * Real.pi)) ^ 2 := by
    have hsq := (sq_le_sq₀ hWbasePos.le (div_nonneg hTpos.le hscalePos.le)).2 hWle
    exact mul_le_mul_of_nonneg_left hsq (by positivity)
  have hdenPos :
      0 < 8 * Real.pi ^ 3 * (x ^ (3 / 4 : ℝ) / (2 * Real.pi)) ^ 2 := by
    positivity
  have hnorm : 0 ≤ x ^ (-beta) := Real.rpow_nonneg hxpos.le _
  have hxpow : 0 ≤ x ^ c := Real.rpow_nonneg hxpos.le _
  have hseries : 0 ≤
      ExplicitFormulaResidues.vonMangoldtLSeriesNorm (c - 1) := by
    unfold ExplicitFormulaResidues.vonMangoldtLSeriesNorm
    exact tsum_nonneg fun n => norm_nonneg _
  rw [thirdOrderPerronErrorMajorant_eq hxpos]
  unfold thirdOrderNormalizedDynamicPerronPowerMajorant
  have hquot := div_le_div_of_nonneg_left
    (mul_nonneg (mul_nonneg hnorm hxpow) hseries) hdenPos hden
  calc
    x ^ (-beta) *
        (x ^ c / (8 * Real.pi ^ 3 * (T / (2 * Real.pi)) ^ 2) *
          ExplicitFormulaResidues.vonMangoldtLSeriesNorm (c - 1)) =
      (x ^ (-beta) * x ^ c *
          ExplicitFormulaResidues.vonMangoldtLSeriesNorm (c - 1)) /
        (8 * Real.pi ^ 3 * (T / (2 * Real.pi)) ^ 2) := by ring
    _ ≤ (x ^ (-beta) * x ^ c *
          ExplicitFormulaResidues.vonMangoldtLSeriesNorm (c - 1)) /
        (8 * Real.pi ^ 3 *
          (x ^ (3 / 4 : ℝ) / (2 * Real.pi)) ^ 2) := hquot
    _ = (ExplicitFormulaResidues.vonMangoldtLSeriesNorm (c - 1) /
          (2 * Real.pi)) * x ^ (c - 3 / 2 - beta) := by
      rw [← rpow_normalized_thirdOrder_baseHeight hxpos]
      field_simp [Real.pi_ne_zero]
      ring

end PrimeNumberTheorem
