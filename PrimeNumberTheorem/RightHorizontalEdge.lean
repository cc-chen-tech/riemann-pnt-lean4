import PrimeNumberTheorem.SafeSecondOrderExplicitFormula
import ZeroFreeRegion.PhragmenLindelofZeta

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

/-- A full-norm logarithmic-derivative bound on a horizontal point gives the
corresponding first-order explicit-formula integrand bound. -/
lemma norm_explicitFormulaIntegrand_horizontal_le_of_logDeriv_le
    {x σ t K : ℝ} (hx : 1 ≤ x) (hσ : σ ≤ 2) (ht : 0 < |t|)
    (hK : 0 ≤ K)
    (hlog : ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤ K) :
    ‖explicitFormulaIntegrand x ((σ : ℂ) + I * t)‖ ≤
      K * x ^ (2 : ℝ) / |t| := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hxpow : x ^ σ ≤ x ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx hσ
  have hline : |t| ≤ ‖(σ : ℂ) + I * t‖ := by
    have := Complex.abs_im_le_norm ((σ : ℂ) + I * t)
    simpa using this
  have hnum : 0 ≤ K * x ^ (2 : ℝ) :=
    mul_nonneg hK (Real.rpow_nonneg hxpos.le _)
  change ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) *
      (x : ℂ) ^ ((σ : ℂ) + I * t) /
        ((σ : ℂ) + I * t)‖ ≤ _
  rw [norm_div, norm_mul, norm_neg,
    Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
  simp only [Complex.add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im,
    zero_mul, mul_zero, sub_zero, add_zero]
  calc
    ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ * x ^ σ /
        ‖(σ : ℂ) + I * t‖ ≤
      (K * x ^ (2 : ℝ)) / ‖(σ : ℂ) + I * t‖ := by
        apply div_le_div_of_nonneg_right _ (norm_nonneg _)
        exact mul_le_mul hlog hxpow (Real.rpow_nonneg hxpos.le σ) hK
    _ ≤ (K * x ^ (2 : ℝ)) / |t| :=
      div_le_div_of_nonneg_left hnum ht hline

/-- The new inner-zero-free logarithmic-derivative estimate bounds the
positive- or negative-height first-order horizontal segment from the inner
zero-free boundary to `Re(s)=2`. -/
theorem exists_norm_horizontal_inner_explicitFormulaContour_le
    {x : ℝ} (hx : 1 ≤ x) :
    ∃ c C T0 : ℝ, 0 < c ∧ 0 ≤ C ∧ 2 ≤ T0 ∧
      ∀ t : ℝ, T0 ≤ |t| →
        IntervalIntegrable
            (fun σ : ℝ => explicitFormulaIntegrand x ((σ : ℂ) + I * t))
            volume (1 - c / (2 * Real.log |t|)) 2 ∧
          ‖∫ σ : ℝ in (1 - c / (2 * Real.log |t|))..2,
              explicitFormulaIntegrand x ((σ : ℂ) + I * t)‖ ≤
            (C * x ^ (2 : ℝ) * (Real.log |t|) ^ 2 / |t|) *
              (1 + c / (2 * Real.log |t|)) := by
  rcases
      ZeroFreeRegion.exists_riemannZeta_ne_zero_and_norm_logDeriv_le_log_sq_on_inner_zeroFreeRegion
    with ⟨c, C, T0, hc, hC, hT0, hlog⟩
  refine ⟨c, C, T0, hc, hC, hT0, ?_⟩
  intro t ht
  have ht2 : 2 ≤ |t| := hT0.trans ht
  have hlogpos : 0 < Real.log |t| :=
    ZeroFreeRegion.log_abs_pos_of_two_le ht2
  have hleft : 1 - c / (2 * Real.log |t|) ≤ (2 : ℝ) := by
    have hdiv : 0 < c / (2 * Real.log |t|) := by positivity
    linarith
  have hpoint : ∀ σ ∈ Set.uIoc (1 - c / (2 * Real.log |t|)) 2,
      ‖explicitFormulaIntegrand x ((σ : ℂ) + I * t)‖ ≤
        C * x ^ (2 : ℝ) * (Real.log |t|) ^ 2 / |t| := by
    intro σ hσ
    rw [Set.uIoc_of_le hleft] at hσ
    have hld := (hlog σ t ht hσ.1.le hσ.2).2
    have hK : 0 ≤ C * (Real.log |t|) ^ 2 :=
      mul_nonneg hC (sq_nonneg _)
    have hbound := norm_explicitFormulaIntegrand_horizontal_le_of_logDeriv_le
      hx hσ.2 (by positivity) hK hld
    convert hbound using 1 <;> ring
  have hintegrable : IntervalIntegrable
      (fun σ : ℝ => explicitFormulaIntegrand x ((σ : ℂ) + I * t))
      volume (1 - c / (2 * Real.log |t|)) 2 := by
    apply ContinuousOn.intervalIntegrable
    intro σ hσ
    rw [Set.uIcc_of_le hleft] at hσ
    have hzeta := (hlog σ t ht hσ.1 hσ.2).1
    have htne : t ≠ 0 := by
      exact abs_pos.mp (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) ht2)
    have hs0 : (σ : ℂ) + I * t ≠ 0 := by
      intro hs
      have him := congrArg Complex.im hs
      simp only [Complex.add_im, ofReal_im, mul_im, I_re, ofReal_im, I_im,
        ofReal_re, zero_mul, one_mul, zero_im] at him
      exact htne (by simpa using him)
    have hs1 : (σ : ℂ) + I * t ≠ 1 := by
      intro hs
      have him := congrArg Complex.im hs
      simp only [Complex.add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re,
        zero_mul, one_mul, one_im] at him
      exact htne (by simpa using him)
    have hmap : ContinuousAt (fun r : ℝ => ((r : ℂ) + I * t)) σ := by
      fun_prop
    have han : ContinuousAt (explicitFormulaIntegrand x)
        ((σ : ℂ) + I * t) :=
      (analyticAt_explicitFormulaIntegrand_of_ne_zero_of_ne_one_of_zeta_ne_zero
        (zero_lt_one.trans_le hx) hs0 hs1 hzeta).continuousAt
    change ContinuousWithinAt
      (explicitFormulaIntegrand x ∘ fun r : ℝ => ((r : ℂ) + I * t)) _ σ
    exact (ContinuousAt.comp
      (f := fun r : ℝ => ((r : ℂ) + I * t))
      (x := σ) (g := explicitFormulaIntegrand x) han hmap).continuousWithinAt
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun σ : ℝ => explicitFormulaIntegrand x ((σ : ℂ) + I * t))
    (a := 1 - c / (2 * Real.log |t|)) (b := 2)
    (C := C * x ^ (2 : ℝ) * (Real.log |t|) ^ 2 / |t|) hpoint
  rw [abs_of_nonneg (sub_nonneg.mpr hleft)] at hbound
  refine ⟨hintegrable, ?_⟩
  convert hbound using 1 <;> ring

/-- For either unit real sign, the inner zero-free horizontal contribution to
the first-order explicit formula tends to zero along that signed height. -/
theorem exists_tendsto_horizontal_inner_explicitFormulaIntegrand_signed_zero
    {x : ℝ} (hx : 1 ≤ x) :
    ∃ c : ℝ, 0 < c ∧
      ∀ ε : ℝ, |ε| = 1 →
        Tendsto
          (fun T : ℝ => ∫ σ : ℝ in
            (1 - c / (2 * Real.log T))..2,
              explicitFormulaIntegrand x ((σ : ℂ) + I * (ε * T)))
          atTop (𝓝 0) := by
  rcases exists_norm_horizontal_inner_explicitFormulaContour_le hx with
    ⟨c, C, T0, hc, hC, hT0, hbound⟩
  let T1 : ℝ := max T0 (Real.exp c)
  refine ⟨c, hc, ?_⟩
  intro ε hε
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero'
    (f := fun T : ℝ =>
      ‖∫ σ : ℝ in (1 - c / (2 * Real.log T))..2,
        explicitFormulaIntegrand x ((σ : ℂ) + I * (ε * T))‖)
    (g := fun T : ℝ =>
      (2 * C * x ^ (2 : ℝ)) * (Real.log T ^ 2 / T))
    (Eventually.of_forall fun T => norm_nonneg _) ?_ ?_
  · filter_upwards [eventually_ge_atTop T1] with T hT
    have hT0' : T0 ≤ T := (le_max_left T0 (Real.exp c)).trans hT
    have hT2 : 2 ≤ T := hT0.trans hT0'
    have hTabs : |T| = T := abs_of_nonneg (zero_le_two.trans hT2)
    have hεTabs : |ε * T| = T := by rw [abs_mul, hε, one_mul, hTabs]
    have hlogpos : 0 < Real.log T := Real.log_pos (one_lt_two.trans_le hT2)
    have hexp : Real.exp c ≤ T := (le_max_right T0 (Real.exp c)).trans hT
    have hclog : c ≤ Real.log T := by
      have h := Real.log_le_log (Real.exp_pos c) hexp
      simpa using h
    have hfactor : 1 + c / (2 * Real.log T) ≤ 2 := by
      have hfrac : c / (2 * Real.log T) ≤ 1 := by
        apply (div_le_iff₀ (mul_pos (by norm_num) hlogpos)).2
        linarith
      linarith
    have hbase := (hbound (ε * T) (by simpa [hεTabs] using hT0')).2
    rw [hεTabs] at hbase
    have hmain : 0 ≤ C * x ^ (2 : ℝ) * Real.log T ^ 2 / T := by
      apply div_nonneg
      · positivity
      · linarith
    calc
      ‖∫ σ : ℝ in (1 - c / (2 * Real.log T))..2,
          explicitFormulaIntegrand x ((σ : ℂ) + I * (ε * T))‖ ≤
        (C * x ^ (2 : ℝ) * Real.log T ^ 2 / T) *
          (1 + c / (2 * Real.log T)) := by simpa using hbase
      _ ≤ (C * x ^ (2 : ℝ) * Real.log T ^ 2 / T) * 2 :=
        mul_le_mul_of_nonneg_left hfactor hmain
      _ = (2 * C * x ^ (2 : ℝ)) * (Real.log T ^ 2 / T) := by ring
  · have hlim :=
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).const_mul
        (2 * C * x ^ (2 : ℝ))
    simpa only [one_mul, add_zero, mul_zero] using hlim

/-- Both inner horizontal contour contributions tend to zero with one common
zero-free constant. -/
theorem exists_tendsto_horizontal_inner_explicitFormulaIntegrand_both_zero
    {x : ℝ} (hx : 1 ≤ x) :
    ∃ c : ℝ, 0 < c ∧
      Tendsto
        (fun T : ℝ => ∫ σ : ℝ in
          (1 - c / (2 * Real.log T))..2,
            explicitFormulaIntegrand x ((σ : ℂ) + I * T))
        atTop (𝓝 0) ∧
      Tendsto
        (fun T : ℝ => ∫ σ : ℝ in
          (1 - c / (2 * Real.log T))..2,
            explicitFormulaIntegrand x ((σ : ℂ) + I * (-T)))
        atTop (𝓝 0) := by
  rcases exists_tendsto_horizontal_inner_explicitFormulaIntegrand_signed_zero hx with
    ⟨c, hc, hsigned⟩
  refine ⟨c, hc, ?_, ?_⟩
  · simpa using hsigned 1 (by norm_num)
  · simpa using hsigned (-1) (by norm_num)

/-- The inner zero-free horizontal contribution tends to zero at positive
height. -/
theorem exists_tendsto_horizontal_inner_explicitFormulaIntegrand_zero
    {x : ℝ} (hx : 1 ≤ x) :
    ∃ c : ℝ, 0 < c ∧
      Tendsto
        (fun T : ℝ => ∫ σ : ℝ in
          (1 - c / (2 * Real.log T))..2,
            explicitFormulaIntegrand x ((σ : ℂ) + I * T))
        atTop (𝓝 0) := by
  rcases exists_tendsto_horizontal_inner_explicitFormulaIntegrand_both_zero hx with
    ⟨c, hc, hpos, _hneg⟩
  exact ⟨c, hc, hpos⟩

/-- The inner zero-free horizontal contribution tends to zero at negative
height, with the same quantitative input as the positive-height result. -/
theorem exists_tendsto_horizontal_inner_explicitFormulaIntegrand_neg_height_zero
    {x : ℝ} (hx : 1 ≤ x) :
    ∃ c : ℝ, 0 < c ∧
      Tendsto
        (fun T : ℝ => ∫ σ : ℝ in
          (1 - c / (2 * Real.log T))..2,
            explicitFormulaIntegrand x ((σ : ℂ) + I * (-T)))
        atTop (𝓝 0) := by
  rcases exists_tendsto_horizontal_inner_explicitFormulaIntegrand_both_zero hx with
    ⟨c, hc, _hpos, hneg⟩
  exact ⟨c, hc, hneg⟩

end ExplicitFormulaResidues
end PrimeNumberTheorem
