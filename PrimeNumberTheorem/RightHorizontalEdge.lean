import PrimeNumberTheorem.SafeSecondOrderExplicitFormula

open Complex MeasureTheory Set Filter Topology
open scoped ArithmeticFunction BigOperators LSeries.notation Interval

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

/-- Absolute von Mangoldt Dirichlet-series majorant on the real line
`Re(s) = 1 + ε`. -/
noncomputable def vonMangoldtLSeriesNorm (ε : ℝ) : ℝ :=
  ∑' n : ℕ, ‖LSeries.term
    (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((1 + ε : ℝ) : ℂ) n‖

theorem norm_neg_logDeriv_riemannZeta_le_vonMangoldtLSeriesNorm
    {ε σ t : ℝ} (hε : 0 < ε) (hσ : 1 + ε ≤ σ) :
    ‖-logDeriv riemannZeta ((σ : ℂ) + t * I)‖ ≤
      vonMangoldtLSeriesNorm ε := by
  let coeff : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  let s : ℂ := (σ : ℂ) + t * I
  let s0 : ℂ := ((1 + ε : ℝ) : ℂ)
  have hs_re : s.re = σ := by simp [s]
  have hs : 1 < s.re := by rw [hs_re]; linarith
  have hs0 : 1 < s0.re := by simp [s0]; linarith
  have hbase := ArithmeticFunction.LSeriesSummable_vonMangoldt hs0
  have hcurrent := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hbase_norm : Summable fun n => ‖LSeries.term coeff s0 n‖ := by
    rw [LSeriesSummable, ← summable_norm_iff] at hbase
    simpa [coeff] using hbase
  have hcurrent_norm : Summable fun n => ‖LSeries.term coeff s n‖ := by
    rw [LSeriesSummable, ← summable_norm_iff] at hcurrent
    simpa [coeff] using hcurrent
  have hterm (n : ℕ) : ‖LSeries.term coeff s n‖ ≤
      ‖LSeries.term coeff s0 n‖ := by
    apply LSeries.norm_term_le_of_re_le_re
    simp [s, s0]
    exact hσ
  have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  calc
    ‖-logDeriv riemannZeta ((σ : ℂ) + t * I)‖ = ‖LSeries coeff s‖ := by
      rw [hL]
      simp only [s, logDeriv_apply]
      congr 2
      ring
    _ ≤ ∑' n, ‖LSeries.term coeff s n‖ := by
      exact norm_tsum_le_tsum_norm hcurrent_norm
    _ ≤ ∑' n, ‖LSeries.term coeff s0 n‖ :=
      hcurrent_norm.tsum_le_tsum hterm hbase_norm
    _ = vonMangoldtLSeriesNorm ε := by rfl

theorem norm_secondOrderExplicitFormulaIntegrand_horizontal_right_le
    {x ε c T σ : ℝ} (hx : 1 ≤ x) (hε : 0 < ε)
    (hσlow : 1 + ε ≤ σ) (hσhigh : σ ≤ c) (hT : T ≠ 0) :
    ‖secondOrderExplicitFormulaIntegrand x ((σ : ℂ) + T * I)‖ ≤
      vonMangoldtLSeriesNorm ε * x ^ c / T ^ 2 := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hlog := norm_neg_logDeriv_riemannZeta_le_vonMangoldtLSeriesNorm
    hε hσlow (t := T)
  have hC : 0 ≤ vonMangoldtLSeriesNorm ε := by
    exact tsum_nonneg fun n => norm_nonneg _
  have hxpow : x ^ σ ≤ x ^ c :=
    Real.rpow_le_rpow_of_exponent_le hx hσhigh
  have hline_sq : T ^ 2 ≤ ‖((σ : ℂ) + T * I)‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    nlinarith
  have hnum_nonneg :
      0 ≤ vonMangoldtLSeriesNorm ε * x ^ c :=
    mul_nonneg hC (Real.rpow_nonneg hxpos.le c)
  change ‖((-logDeriv riemannZeta ((σ : ℂ) + T * I)) *
      (x : ℂ) ^ ((σ : ℂ) + T * I) / ((σ : ℂ) + T * I)) /
        ((σ : ℂ) + T * I)‖ ≤ _
  rw [norm_div, norm_div, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
  simp only [Complex.add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    zero_mul, mul_zero, sub_zero, add_zero]
  rw [show (‖-logDeriv riemannZeta ((σ : ℂ) + T * I)‖ * x ^ σ /
      ‖(σ : ℂ) + T * I‖) / ‖(σ : ℂ) + T * I‖ =
      ‖-logDeriv riemannZeta ((σ : ℂ) + T * I)‖ * x ^ σ /
        ‖(σ : ℂ) + T * I‖ ^ 2 by ring]
  calc
    ‖-logDeriv riemannZeta ((σ : ℂ) + T * I)‖ * x ^ σ /
        ‖(σ : ℂ) + T * I‖ ^ 2 ≤
      (vonMangoldtLSeriesNorm ε * x ^ c) /
        ‖(σ : ℂ) + T * I‖ ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul hlog hxpow (Real.rpow_nonneg hxpos.le σ) hC
    _ ≤ (vonMangoldtLSeriesNorm ε * x ^ c) / T ^ 2 :=
      div_le_div_of_nonneg_left hnum_nonneg (sq_pos_of_ne_zero hT) hline_sq
    _ = vonMangoldtLSeriesNorm ε * x ^ c / T ^ 2 := rfl

theorem norm_horizontal_right_secondOrderContour_le
    {x ε c T : ℝ} (hx : 1 ≤ x) (hε : 0 < ε)
    (hc : 1 + ε ≤ c) (hT : 0 < T) :
    ‖∫ σ : ℝ in (1 + ε)..c,
        secondOrderExplicitFormulaIntegrand x ((σ : ℂ) + T * I)‖ ≤
      (vonMangoldtLSeriesNorm ε * x ^ c / T ^ 2) *
        (c - (1 + ε)) := by
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun σ : ℝ =>
      secondOrderExplicitFormulaIntegrand x ((σ : ℂ) + T * I))
    (a := 1 + ε) (b := c)
    (C := vonMangoldtLSeriesNorm ε * x ^ c / T ^ 2)
    (fun σ hσ => by
      rw [Set.uIoc_of_le hc] at hσ
      exact norm_secondOrderExplicitFormulaIntegrand_horizontal_right_le
        hx hε hσ.1.le hσ.2 hT.ne')
  rw [abs_of_nonneg (sub_nonneg.mpr hc)] at hbound
  exact hbound

theorem norm_horizontal_right_secondOrderContour_neg_height_le
    {x ε c T : ℝ} (hx : 1 ≤ x) (hε : 0 < ε)
    (hc : 1 + ε ≤ c) (hT : 0 < T) :
    ‖∫ σ : ℝ in (1 + ε)..c,
        secondOrderExplicitFormulaIntegrand x ((σ : ℂ) - T * I)‖ ≤
      (vonMangoldtLSeriesNorm ε * x ^ c / T ^ 2) *
        (c - (1 + ε)) := by
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun σ : ℝ =>
      secondOrderExplicitFormulaIntegrand x ((σ : ℂ) - T * I))
    (a := 1 + ε) (b := c)
    (C := vonMangoldtLSeriesNorm ε * x ^ c / T ^ 2)
    (fun σ hσ => by
      rw [Set.uIoc_of_le hc] at hσ
      have hpoint := norm_secondOrderExplicitFormulaIntegrand_horizontal_right_le
        (T := -T) hx hε hσ.1.le hσ.2 (neg_ne_zero.mpr hT.ne')
      simpa [sub_eq_add_neg] using hpoint)
  rw [abs_of_nonneg (sub_nonneg.mpr hc)] at hbound
  exact hbound

theorem norm_horizontal_right_secondOrderContour_difference_le
    {x ε c T : ℝ} (hx : 1 ≤ x) (hε : 0 < ε)
    (hc : 1 + ε ≤ c) (hT : 0 < T) :
    ‖(∫ σ : ℝ in (1 + ε)..c,
          secondOrderExplicitFormulaIntegrand x ((σ : ℂ) - T * I)) -
      (∫ σ : ℝ in (1 + ε)..c,
          secondOrderExplicitFormulaIntegrand x ((σ : ℂ) + T * I))‖ ≤
      2 * ((vonMangoldtLSeriesNorm ε * x ^ c / T ^ 2) *
        (c - (1 + ε))) := by
  calc
    _ ≤ ‖∫ σ : ℝ in (1 + ε)..c,
          secondOrderExplicitFormulaIntegrand x ((σ : ℂ) - T * I)‖ +
        ‖∫ σ : ℝ in (1 + ε)..c,
          secondOrderExplicitFormulaIntegrand x ((σ : ℂ) + T * I)‖ :=
      norm_sub_le _ _
    _ ≤ (vonMangoldtLSeriesNorm ε * x ^ c / T ^ 2) *
          (c - (1 + ε)) +
        (vonMangoldtLSeriesNorm ε * x ^ c / T ^ 2) *
          (c - (1 + ε)) :=
      add_le_add
        (norm_horizontal_right_secondOrderContour_neg_height_le hx hε hc hT)
        (norm_horizontal_right_secondOrderContour_le hx hε hc hT)
    _ = _ := by ring

/-- On the absolutely convergent part of a horizontal first-order contour,
the explicit-formula integrand is `O(1 / |T|)`. -/
theorem norm_firstOrderExplicitFormulaIntegrand_horizontal_right_le
    {x ε c T σ : ℝ} (hx : 1 ≤ x) (hε : 0 < ε)
    (hσlow : 1 + ε ≤ σ) (hσhigh : σ ≤ c) (hT : T ≠ 0) :
    ‖explicitFormulaIntegrand x ((σ : ℂ) + T * I)‖ ≤
      vonMangoldtLSeriesNorm ε * x ^ c / |T| := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hlog := norm_neg_logDeriv_riemannZeta_le_vonMangoldtLSeriesNorm
    hε hσlow (t := T)
  have hC : 0 ≤ vonMangoldtLSeriesNorm ε := by
    exact tsum_nonneg fun n => norm_nonneg _
  have hxpow : x ^ σ ≤ x ^ c :=
    Real.rpow_le_rpow_of_exponent_le hx hσhigh
  have hline : |T| ≤ ‖((σ : ℂ) + T * I)‖ := by
    simpa using abs_im_le_norm ((σ : ℂ) + T * I)
  have hnum_nonneg : 0 ≤ vonMangoldtLSeriesNorm ε * x ^ c :=
    mul_nonneg hC (Real.rpow_nonneg hxpos.le c)
  change ‖(-logDeriv riemannZeta ((σ : ℂ) + T * I)) *
      (x : ℂ) ^ ((σ : ℂ) + T * I) / ((σ : ℂ) + T * I)‖ ≤ _
  rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
  simp only [Complex.add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    zero_mul, mul_zero, sub_zero, add_zero]
  calc
    ‖-logDeriv riemannZeta ((σ : ℂ) + T * I)‖ * x ^ σ /
        ‖(σ : ℂ) + T * I‖ ≤
      (vonMangoldtLSeriesNorm ε * x ^ c) /
        ‖(σ : ℂ) + T * I‖ := by
      apply div_le_div_of_nonneg_right _ (norm_nonneg _)
      exact mul_le_mul hlog hxpow (Real.rpow_nonneg hxpos.le σ) hC
    _ ≤ (vonMangoldtLSeriesNorm ε * x ^ c) / |T| :=
      div_le_div_of_nonneg_left hnum_nonneg (abs_pos.mpr hT) hline
    _ = vonMangoldtLSeriesNorm ε * x ^ c / |T| := rfl

theorem norm_horizontal_right_firstOrderContour_le
    {x ε c T : ℝ} (hx : 1 ≤ x) (hε : 0 < ε)
    (hc : 1 + ε ≤ c) (hT : 0 < T) :
    ‖∫ σ : ℝ in (1 + ε)..c,
        explicitFormulaIntegrand x ((σ : ℂ) + T * I)‖ ≤
      (vonMangoldtLSeriesNorm ε * x ^ c / T) *
        (c - (1 + ε)) := by
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun σ : ℝ => explicitFormulaIntegrand x ((σ : ℂ) + T * I))
    (a := 1 + ε) (b := c)
    (C := vonMangoldtLSeriesNorm ε * x ^ c / T)
    (fun σ hσ => by
      rw [Set.uIoc_of_le hc] at hσ
      simpa [abs_of_pos hT] using
        norm_firstOrderExplicitFormulaIntegrand_horizontal_right_le
          hx hε hσ.1.le hσ.2 hT.ne')
  rw [abs_of_nonneg (sub_nonneg.mpr hc)] at hbound
  exact hbound

theorem norm_horizontal_right_firstOrderContour_neg_height_le
    {x ε c T : ℝ} (hx : 1 ≤ x) (hε : 0 < ε)
    (hc : 1 + ε ≤ c) (hT : 0 < T) :
    ‖∫ σ : ℝ in (1 + ε)..c,
        explicitFormulaIntegrand x ((σ : ℂ) - T * I)‖ ≤
      (vonMangoldtLSeriesNorm ε * x ^ c / T) *
        (c - (1 + ε)) := by
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun σ : ℝ => explicitFormulaIntegrand x ((σ : ℂ) - T * I))
    (a := 1 + ε) (b := c)
    (C := vonMangoldtLSeriesNorm ε * x ^ c / T)
    (fun σ hσ => by
      rw [Set.uIoc_of_le hc] at hσ
      have hpoint := norm_firstOrderExplicitFormulaIntegrand_horizontal_right_le
        (T := -T) hx hε hσ.1.le hσ.2 (neg_ne_zero.mpr hT.ne')
      simpa [sub_eq_add_neg, abs_of_pos hT] using hpoint)
  rw [abs_of_nonneg (sub_nonneg.mpr hc)] at hbound
  exact hbound

theorem norm_horizontal_right_firstOrderContour_difference_le
    {x ε c T : ℝ} (hx : 1 ≤ x) (hε : 0 < ε)
    (hc : 1 + ε ≤ c) (hT : 0 < T) :
    ‖(∫ σ : ℝ in (1 + ε)..c,
          explicitFormulaIntegrand x ((σ : ℂ) - T * I)) -
      (∫ σ : ℝ in (1 + ε)..c,
          explicitFormulaIntegrand x ((σ : ℂ) + T * I))‖ ≤
      2 * ((vonMangoldtLSeriesNorm ε * x ^ c / T) *
        (c - (1 + ε))) := by
  calc
    _ ≤ ‖∫ σ : ℝ in (1 + ε)..c,
          explicitFormulaIntegrand x ((σ : ℂ) - T * I)‖ +
        ‖∫ σ : ℝ in (1 + ε)..c,
          explicitFormulaIntegrand x ((σ : ℂ) + T * I)‖ :=
      norm_sub_le _ _
    _ ≤ (vonMangoldtLSeriesNorm ε * x ^ c / T) *
          (c - (1 + ε)) +
        (vonMangoldtLSeriesNorm ε * x ^ c / T) *
          (c - (1 + ε)) :=
      add_le_add
        (norm_horizontal_right_firstOrderContour_neg_height_le hx hε hc hT)
        (norm_horizontal_right_firstOrderContour_le hx hε hc hT)
    _ = _ := by ring

/-- The portions of the first-order top and bottom edges in the absolute-
convergence half-plane make a vanishing contribution as the height grows. -/
theorem tendsto_horizontal_right_firstOrderContour_difference_atTop
    {x ε c : ℝ} (hx : 1 ≤ x) (hε : 0 < ε)
    (hc : 1 + ε ≤ c) :
    Tendsto
      (fun T : ℝ =>
        (∫ σ : ℝ in (1 + ε)..c,
          explicitFormulaIntegrand x ((σ : ℂ) - T * I)) -
        (∫ σ : ℝ in (1 + ε)..c,
          explicitFormulaIntegrand x ((σ : ℂ) + T * I)))
      atTop (nhds 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  simp only [sub_zero]
  let A : ℝ := 2 * (vonMangoldtLSeriesNorm ε * x ^ c) *
    (c - (1 + ε))
  have hAdiv : Tendsto (fun T : ℝ => A / T) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  apply squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) _ hAdiv
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  calc
    ‖(∫ σ : ℝ in (1 + ε)..c,
          explicitFormulaIntegrand x ((σ : ℂ) - T * I)) -
        (∫ σ : ℝ in (1 + ε)..c,
          explicitFormulaIntegrand x ((σ : ℂ) + T * I))‖ ≤
      2 * ((vonMangoldtLSeriesNorm ε * x ^ c / T) *
        (c - (1 + ε))) :=
      norm_horizontal_right_firstOrderContour_difference_le hx hε hc hT
    _ = A / T := by dsimp [A]; ring

end ExplicitFormulaResidues
end PrimeNumberTheorem
