import PrimeNumberTheorem.ZeroDensityLayerBudgetThirdOrderLSeriesBridge
import PrimeNumberTheorem.SmoothedErrorTransfer

open Complex MeasureTheory Set Filter Topology
open scoped ArithmeticFunction BigOperators LSeries.notation

namespace PrimeNumberTheorem.ExplicitFormulaResidues

/-- The negative-odd left-edge majorant after the additional cubic-kernel
factor is included. -/
noncomputable def thirdOrderOddVerticalBound (x : ℝ) (N : ℕ) (T : ℝ) : ℝ :=
  secondOrderOddVerticalBound x N T / (2 * (N : ℝ) + 1)

/-- A pointwise logarithmic-derivative bound gains three reciprocal powers of
horizontal height for the third-order Perron kernel. -/
theorem norm_thirdOrderExplicitFormulaIntegrand_horizontal_le_of_logDeriv_le_of_re_le
    {x σ b t K : ℝ} (hx : 1 ≤ x) (hσ : σ ≤ b) (ht : 0 < |t|)
    (hK : 0 ≤ K)
    (hlog : ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤ K) :
    ‖thirdOrderExplicitFormulaIntegrand x ((σ : ℂ) + I * t)‖ ≤
      K * x ^ b / |t| ^ 3 := by
  let s : ℂ := (σ : ℂ) + I * t
  have hsecond :=
    norm_secondOrderExplicitFormulaIntegrand_horizontal_le_of_logDeriv_le_of_re_le
      hx hσ ht hK hlog
  have hline : |t| ≤ ‖s‖ := by
    have him := Complex.abs_im_le_norm s
    simpa [s] using him
  have hnum : 0 ≤ K * x ^ b :=
    mul_nonneg hK (Real.rpow_nonneg (zero_le_one.trans hx) _)
  rw [thirdOrderExplicitFormulaIntegrand_eq_secondOrder_div, norm_div]
  change ‖secondOrderExplicitFormulaIntegrand x s‖ / ‖s‖ ≤ _
  calc
    ‖secondOrderExplicitFormulaIntegrand x s‖ / ‖s‖ ≤
        (K * x ^ b / |t| ^ 2) / ‖s‖ :=
      div_le_div_of_nonneg_right hsecond (norm_nonneg s)
    _ ≤ (K * x ^ b / |t| ^ 2) / |t| :=
      div_le_div_of_nonneg_left (div_nonneg hnum (sq_nonneg _)) ht hline
    _ = K * x ^ b / |t| ^ 3 := by ring

/-- The third-order kernel gains one additional reciprocal factor on a
negative-odd left vertical segment. -/
theorem norm_thirdOrderExplicitFormulaIntegrand_odd_vertical_le
    {x T t : ℝ} {N : ℕ} (hx : 1 < x) (hT : 0 ≤ T) (ht : |t| ≤ T) :
    ‖thirdOrderExplicitFormulaIntegrand x
      (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      thirdOrderOddVerticalBound x N T := by
  let s : ℂ := ((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I
  let d : ℝ := 2 * (N : ℝ) + 1
  have hsecond := norm_secondOrderExplicitFormulaIntegrand_odd_vertical_le
    (N := N) hx hT ht
  have hdpos : 0 < d := by dsimp [d]; positivity
  have hden : d ≤ ‖s‖ := by
    have hsre : s.re = -d := by
      dsimp [s, d]
      simp
    have hre : d = |s.re| := by
      rw [hsre, abs_neg, abs_of_pos hdpos]
    rw [hre]
    exact Complex.abs_re_le_norm s
  have hbound_nonneg : 0 ≤ secondOrderOddVerticalBound x N T :=
    (norm_nonneg _).trans hsecond
  rw [thirdOrderExplicitFormulaIntegrand_eq_secondOrder_div, norm_div]
  change ‖secondOrderExplicitFormulaIntegrand x s‖ / ‖s‖ ≤ _
  change _ ≤ secondOrderOddVerticalBound x N T / d
  calc
    ‖secondOrderExplicitFormulaIntegrand x s‖ / ‖s‖ ≤
        secondOrderOddVerticalBound x N T / ‖s‖ :=
      div_le_div_of_nonneg_right hsecond (norm_nonneg s)
    _ ≤ secondOrderOddVerticalBound x N T / d :=
      div_le_div_of_nonneg_left hbound_nonneg hdpos hden

/-- Integrating a uniform horizontal logarithmic-derivative bound preserves
all three reciprocal powers of the selected height. -/
theorem norm_integral_thirdOrderHorizontal_le_of_logDeriv
    {x a c b t K : ℝ} (hx : 1 ≤ x) (hac : a ≤ c) (hc : c ≤ b)
    (ht : 0 < |t|) (hK : 0 ≤ K)
    (hlog : ∀ σ ∈ Set.uIoc a c,
      ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤ K) :
    ‖∫ σ : ℝ in a..c,
        thirdOrderExplicitFormulaIntegrand x ((σ : ℂ) + I * t)‖ ≤
      (K * x ^ b / |t| ^ 3) * (c - a) := by
  have hpoint : ∀ σ ∈ Set.uIoc a c,
      ‖thirdOrderExplicitFormulaIntegrand x ((σ : ℂ) + I * t)‖ ≤
        K * x ^ b / |t| ^ 3 := by
    intro σ hσ
    rw [Set.uIoc_of_le hac] at hσ
    exact norm_thirdOrderExplicitFormulaIntegrand_horizontal_le_of_logDeriv_le_of_re_le
      hx (hσ.2.trans hc) ht hK (hlog σ (by simpa [Set.uIoc_of_le hac] using hσ))
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  rw [abs_of_nonneg (sub_nonneg.mpr hac)] at hbound
  exact hbound

/-- Integrated third-order control on a negative-odd left vertical segment. -/
theorem norm_integral_thirdOrderOddVertical_le
    {x T : ℝ} {N : ℕ} (hx : 1 < x) (hT : 0 ≤ T) :
    ‖∫ t : ℝ in (-T)..T,
        thirdOrderExplicitFormulaIntegrand x
          (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      thirdOrderOddVerticalBound x N T * (2 * T) := by
  have hpoint : ∀ t ∈ Set.uIoc (-T) T,
      ‖thirdOrderExplicitFormulaIntegrand x
        (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
        thirdOrderOddVerticalBound x N T := by
    intro t ht
    rw [Set.uIoc_of_le (by linarith)] at ht
    apply norm_thirdOrderExplicitFormulaIntegrand_odd_vertical_le hx hT
    exact abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  rw [abs_of_nonneg (by linarith : 0 ≤ T - -T)] at hbound
  convert hbound using 1 <;> ring

/-- The exact third-order contour remainder is bounded by the norms of its
three non-right rectangle edges. -/
theorem norm_thirdOrderContourRemainder_le_edges (x a c W : ℝ) :
    ‖thirdOrderContourRemainder x a c W‖ ≤
      (‖∫ σ : ℝ in a..c,
          thirdOrderExplicitFormulaIntegrand x
            ((σ : ℂ) + (-(2 * Real.pi * W) : ℝ) * I)‖ +
        ‖∫ σ : ℝ in a..c,
          thirdOrderExplicitFormulaIntegrand x
            ((σ : ℂ) + (2 * Real.pi * W : ℝ) * I)‖ +
        ‖∫ t : ℝ in -(2 * Real.pi * W)..2 * Real.pi * W,
          thirdOrderExplicitFormulaIntegrand x ((a : ℂ) + t * I)‖) /
        (2 * Real.pi) := by
  let bottomEdge : ℂ := ∫ σ : ℝ in a..c,
    thirdOrderExplicitFormulaIntegrand x
      ((σ : ℂ) + (-(2 * Real.pi * W) : ℝ) * Complex.I)
  let topEdge : ℂ := ∫ σ : ℝ in a..c,
    thirdOrderExplicitFormulaIntegrand x
      ((σ : ℂ) + (2 * Real.pi * W : ℝ) * Complex.I)
  let leftEdge : ℂ := ∫ t : ℝ in -(2 * Real.pi * W)..2 * Real.pi * W,
    thirdOrderExplicitFormulaIntegrand x ((a : ℂ) + (t : ℂ) * Complex.I)
  change ‖(bottomEdge - topEdge - Complex.I * leftEdge) /
      (2 * Real.pi * Complex.I)‖ ≤ _
  rw [norm_div]
  have hden : ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
    rw [norm_mul, norm_I, mul_one, norm_mul, norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hden]
  apply (div_le_div_iff_of_pos_right (mul_pos (by norm_num) Real.pi_pos)).2
  calc
    ‖bottomEdge - topEdge - Complex.I * leftEdge‖ ≤
        ‖bottomEdge - topEdge‖ + ‖Complex.I * leftEdge‖ := norm_sub_le _ _
    _ ≤ (‖bottomEdge‖ + ‖topEdge‖) + ‖leftEdge‖ := by
      gcongr
      · exact norm_sub_le bottomEdge topEdge
      · simp
    _ = ‖bottomEdge‖ + ‖topEdge‖ + ‖leftEdge‖ := rfl

/-- Explicit selected-height majorant for the complete cubic contour remainder
on the left line `Re(s) = -1`. -/
noncomputable def thirdOrderGoodHeightContourRemainderMajorant
    (x C A T c : ℝ) : ℝ :=
  (2 * ((C * x ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T ^ 3) *
      (c + 1)) + thirdOrderOddVerticalBound x 0 T * (2 * T)) /
    (2 * Real.pi)

/-- Every sufficiently high unit interval contains a common top/bottom height
where the genuine cubic contour remainder has an explicit `T^-3` horizontal
budget and the negative-one left-edge budget. -/
theorem exists_goodHeight_Icc_norm_thirdOrderContourRemainder_le
    {x c : ℝ} (hx : 1 < x) (hc : 1 < c) (hc2 : c ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ‖thirdOrderContourRemainder x (-1) c
              (T / (2 * Real.pi))‖ ≤
            thirdOrderGoodHeightContourRemainderMajorant x C A T c := by
  rcases exists_goodHeight_Icc_norm_logDeriv_central_band_le_log_sq with
    ⟨C, hC, hchoose⟩
  refine ⟨C, hC, ?_⟩
  intro A hA
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

end PrimeNumberTheorem.ExplicitFormulaResidues
