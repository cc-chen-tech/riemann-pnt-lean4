import PrimeNumberTheorem.MWKFCubicAFEWeightContour

open Complex Filter MeasureTheory Set
open scoped Interval Topology

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Moving the real-product weight past zero

Both horizontal edges are controlled by the actual gamma integral bound
and the Gaussian kernel. The resulting identity retains the residue one.
Constants here depend on fixed t and the contour endpoints, not on P or
the height in the final small-product bound. No T-uniform error estimate
or mollifier cancellation is concluded.
-/

theorem exists_norm_cubicAFEWeightMellinKernel_horizontal_le (t P : ℝ) {a b : ℝ}
    (ha : -1 / 2 < a) (hab : a ≤ b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {x y : ℝ}, x ∈ [[a, b]] → 1 ≤ |y| →
      ‖cubicAFEWeightMellinKernel t P (cubicAFEVerticalPoint x y)‖ ≤
        K * cubicAFEVerticalGaussianMajorant (|a| + |b|) y := by
  obtain ⟨C, hC, hgamma⟩ := MathlibAux.exists_norm_Gammaℝ_le_on_positive_reIcc
    (show 0 < 1 / 2 + a by linarith) (show 0 < 1 / 2 + b by linarith)
  let L := |a| + |b|
  let E := Real.exp (L * |Real.log P|)
  refine ⟨125 * Real.exp (L^2) * C^2 / ‖cubicAFEGammaProduct t 0‖ * E, by positivity, ?_⟩
  intro x y hx hy
  rw [uIcc_of_le hab] at hx
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hxL : |x| ≤ L := by
    apply abs_le.mpr
    constructor <;> dsimp [L] <;>
      linarith [hx.1, hx.2, neg_abs_le a, le_abs_self b, abs_nonneg a, abs_nonneg b]
  have hG : ‖cubicAFEKernelG t (cubicAFEVerticalPoint x y)‖ ≤
      (125 * Real.exp (L^2)) * cubicAFEVerticalGaussianMajorant L y := by
    apply (norm_cubicAFEKernelG_vertical_le t x y).trans
    have hsq : x^2 ≤ L^2 := by
      calc
        x^2 = |x|^2 := (sq_abs x).symm
        _ ≤ L^2 := by gcongr
    unfold cubicAFEVerticalGaussianMajorant
    rw [abs_of_nonneg hL]
    gcongr
  have hgp : ‖cubicAFEGammaProduct t (cubicAFEVerticalPoint x y)‖ ≤ C^2 := by
    unfold cubicAFEGammaProduct
    rw [norm_mul, pow_two]
    apply mul_le_mul (hgamma _ ?_ ?_) (hgamma _ ?_ ?_) (norm_nonneg _) hC <;>
      norm_num [cubicCriticalPoint, cubicAFEVerticalPoint] <;> linarith [hx.1, hx.2]
  have hz : 1 ≤ ‖cubicAFEVerticalPoint x y‖ := hy.trans (by
    simpa [cubicAFEVerticalPoint] using abs_im_le_norm (cubicAFEVerticalPoint x y))
  have he : ‖Complex.exp (-cubicAFEVerticalPoint x y * (Real.log P : ℂ))‖ ≤ E := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hh : -x * Real.log P ≤ L * |Real.log P| := by
      calc
        _ ≤ |-x * Real.log P| := le_abs_self _
        _ = |x| * |Real.log P| := by rw [abs_mul, abs_neg]
        _ ≤ _ := mul_le_mul_of_nonneg_right hxL (abs_nonneg _)
    simpa [cubicAFEVerticalPoint] using hh
  have hM := cubicAFEVerticalGaussianMajorant_nonneg L y
  unfold cubicAFEWeightMellinKernel cubicAFEScalar
  rw [norm_mul, norm_div, norm_div, norm_mul]
  calc
    _ ≤ (((125 * Real.exp (L^2)) * cubicAFEVerticalGaussianMajorant L y) * C^2 /
        ‖cubicAFEGammaProduct t 0‖ / 1) * E := by gcongr
    _ = _ := by ring

private theorem tendsto_gaussian_polynomial (A K : ℝ) (hA : 0 ≤ A) (hK : 0 ≤ K) :
    Tendsto (fun V : ℝ ↦ K * (A + V)^6 * Real.exp (-V^2)) atTop (nhds 0) := by
  have hg : Tendsto (fun V : ℝ ↦ V^6 * Real.exp (-V^2)) atTop (nhds 0) := by
    apply ((tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
      (a := (1 : ℝ)) one_pos (6 : ℝ)).mono_left atTop_le_cocompact).congr'
    filter_upwards [eventually_gt_atTop 0] with V hV
    simp [abs_of_pos hV]
  have hb : Tendsto (fun V : ℝ ↦ (64 * K) * (V^6 * Real.exp (-V^2))) atTop (nhds 0) := by
    simpa using hg.const_mul (64 * K)
  refine squeeze_zero' ?_ ?_ hb
  · filter_upwards [eventually_ge_atTop 0] with V hV
    positivity
  · filter_upwards [eventually_ge_atTop (max A 1)] with V hV
    have hVA : A ≤ V := (le_max_left _ _).trans hV
    have hV0 : 0 ≤ V := zero_le_one.trans ((le_max_right _ _).trans hV)
    have hAV : A + V ≤ 2 * V := by linarith
    calc
      _ ≤ K * (2 * V)^6 * Real.exp (-V^2) := by gcongr
      _ = _ := by ring

/-- A single proof covers the top and bottom edges (`ε=1` and `ε=-1`). -/
theorem tendsto_cubicAFEWeightMellinKernel_horizontalIntegral (t P : ℝ) {a b ε : ℝ}
    (ha : -1 / 2 < a) (hab : a ≤ b) (hε : |ε| = 1) :
    Tendsto (fun V : ℝ ↦ ∫ x : ℝ in a..b,
      cubicAFEWeightMellinKernel t P (cubicAFEVerticalPoint x (ε * V))) atTop (nhds 0) := by
  obtain ⟨K, hK, hb⟩ := exists_norm_cubicAFEWeightMellinKernel_horizontal_le t P ha hab
  let L := |a| + |b|
  have hεsq : ε^2 = 1 := by nlinarith [sq_abs ε]
  have ht := tendsto_gaussian_polynomial (1 + L) (K * |b - a|) (by dsimp [L]; positivity)
    (mul_nonneg hK (abs_nonneg _))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ ht
  filter_upwards [eventually_ge_atTop 1] with V hV
  have hv : 0 ≤ V := zero_le_one.trans hV
  have hh : 1 ≤ |ε * V| := by simpa [abs_mul, hε, abs_of_nonneg hv] using hV
  have hm : cubicAFEVerticalGaussianMajorant L (ε * V) =
      (1 + L + V)^6 * Real.exp (-V^2) := by
    simp [cubicAFEVerticalGaussianMajorant, abs_mul, hε, abs_of_nonneg hv,
      abs_of_nonneg (show 0 ≤ L by dsimp [L]; positivity), mul_pow, hεsq]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b)
    (fun x hx ↦ hb (uIoc_subset_uIcc hx) hh)
  calc
    _ ≤ (K * cubicAFEVerticalGaussianMajorant L (ε * V)) * |b - a| := hi
    _ = _ := by rw [hm]; ring

/-- Moving the absolutely convergent weight from a positive line to a
negative line crosses the simple pole of residue one. -/
theorem cubicAFERealProductWeightVertical_eq_one_add (t : ℝ) {P a b : ℝ}
    (hP : 0 < P) (ha : -1 / 2 < a) (ha0 : a < 0) (hb : 0 < b) :
    cubicAFERealProductWeightVertical t b P = 1 + cubicAFERealProductWeightVertical t a P := by
  have hab : a ≤ b := (ha0.trans hb).le
  have htop := tendsto_cubicAFEWeightMellinKernel_horizontalIntegral t P ha hab
    (ε := 1) (by norm_num)
  have hbottom := tendsto_cubicAFEWeightMellinKernel_horizontalIntegral t P ha hab
    (ε := -1) (by norm_num)
  have hv (X : ℝ) (hX : -1 / 2 < X) (hne : X ≠ 0) :
      Tendsto (fun V : ℝ ↦ ∫ y : ℝ in -V..V,
        cubicAFEWeightMellinKernel t P (cubicAFEVerticalPoint X y)) atTop
        (nhds (∫ y : ℝ, cubicAFERealProductMellinIntegrand t X P y)) :=
    intervalIntegral_tendsto_integral
      (integrable_cubicAFERealProductMellinIntegrand t hX hne hP)
      tendsto_neg_atTop_atBot tendsto_id
  have ht := ((hbottom.sub htop).add ((hv b (by linarith) hb.ne').const_mul I)).sub
    ((hv a ha ha0.ne).const_mul I)
  have hrect : Tendsto (fun V : ℝ ↦
      MathlibAux.boundaryRectIntegral (cubicAFEWeightMellinKernel t P) a b (-V) V)
      atTop (nhds (I * (∫ y : ℝ, cubicAFERealProductMellinIntegrand t b P y) -
        I * (∫ y : ℝ, cubicAFERealProductMellinIntegrand t a P y))) := by
    simpa only [one_mul, neg_one_mul, zero_sub, neg_zero, zero_add,
      MathlibAux.boundaryRectIntegral, cubicAFEVerticalPoint, smul_eq_mul] using ht
  have hconst : Tendsto (fun V : ℝ ↦
      MathlibAux.boundaryRectIntegral (cubicAFEWeightMellinKernel t P) a b (-V) V)
      atTop (nhds (2 * Real.pi * I)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop 0] with V hV
    exact (boundaryRectIntegral_cubicAFEWeightMellinKernel t P ha ha0 hb (by linarith) hV).symm
  have heq := tendsto_nhds_unique hrect hconst
  have hj : (∫ y : ℝ, cubicAFERealProductMellinIntegrand t b P y) =
      2 * Real.pi + (∫ y : ℝ, cubicAFERealProductMellinIntegrand t a P y) := by
    apply mul_left_cancel₀ I_ne_zero
    linear_combination heq
  unfold cubicAFERealProductWeightVertical
  rw [hj]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hpi]

/-- The original positive-line weight is bounded at the lower product
endpoint. The norm mass depends only on fixed t and the negative line. -/
theorem norm_cubicAFERealProductWeightVertical_le_one_add (t : ℝ) {P a b : ℝ}
    (hP : 0 < P) (ha : -1 / 2 < a) (ha0 : a < 0) (hb : 0 < b) :
    ‖cubicAFERealProductWeightVertical t b P‖ ≤ 1 + cubicAFEWeightNormMass t a * P^(-a) := by
  rw [cubicAFERealProductWeightVertical_eq_one_add t hP ha ha0 hb]
  calc
    _ ≤ ‖(1 : ℂ)‖ + ‖cubicAFERealProductWeightVertical t a P‖ := norm_add_le _ _
    _ ≤ _ := by simpa using add_le_add_left (norm_cubicAFERealProductWeightVertical_le t a hP) 1

end PrimeNumberTheorem.MWKFCubic
