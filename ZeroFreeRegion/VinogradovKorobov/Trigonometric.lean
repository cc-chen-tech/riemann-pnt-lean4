import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Algebra.BigOperators.Field

namespace ZeroFreeRegion.VinogradovKorobov

/-- The reciprocal chord of the unit circle, expressed using cotangent. -/
lemma reciprocal_exp_sub_one_eq (x : ℝ) (hx : Real.sin (x / 2) ≠ 0) :
    (Complex.exp (Complex.I * (x : ℂ)) - 1)⁻¹ =
      (-1 / 2 : ℂ) - Complex.I * (Real.cot (x / 2) / 2 : ℝ) := by
  apply inv_eq_of_mul_eq_one_left
  rw [mul_sub, mul_one]
  rw [show Complex.I * (x : ℂ) = (x : ℂ) * Complex.I by ring]
  rw [Complex.exp_mul_I]
  have hhalf_re : ((-1 / 2 : ℂ)).re = -1 / 2 := by norm_num
  have hhalf_im : ((-1 / 2 : ℂ)).im = 0 := by norm_num
  apply Complex.ext <;>
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.one_re, Complex.one_im, Complex.cos_ofReal_re, Complex.cos_ofReal_im,
      Complex.sin_ofReal_re, Complex.sin_ofReal_im, hhalf_re, hhalf_im,
      zero_mul, mul_zero, zero_add, add_zero, one_mul, mul_one, sub_zero]
  all_goals
    rw [Real.cot_eq_cos_div_sin, show x = 2 * (x / 2) by ring,
      Real.cos_two_mul_eq_one_sub, Real.sin_two_mul]
  · field_simp
    nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
  · field_simp
    ring

private lemma hasDerivAt_cot (x : ℝ) (hx : Real.sin x ≠ 0) :
    HasDerivAt Real.cot (-(Real.sin x) ^ (-2 : ℤ)) x := by
  rw [show Real.cot = fun y ↦ Real.cos y / Real.sin y by
    funext y; exact Real.cot_eq_cos_div_sin y]
  convert (Real.hasDerivAt_cos x).div (Real.hasDerivAt_sin x) hx using 1
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq x]

/-- Cotangent is antitone on every closed subinterval of `(0, π)`. -/
lemma antitoneOn_cot_Icc {a b : ℝ} (ha : 0 < a) (hb : b < Real.pi) :
    AntitoneOn Real.cot (Set.Icc a b) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
  · rw [show Real.cot = fun x ↦ Real.cos x / Real.sin x by
        funext x; exact Real.cot_eq_cos_div_sin x]
    exact Real.continuous_cos.continuousOn.div
      Real.continuous_sin.continuousOn fun x hx ↦
        (Real.sin_pos_of_pos_of_lt_pi (ha.trans_le hx.1) (hx.2.trans_lt hb)).ne'
  · intro x hx
    have hx' : x ∈ Set.Icc a b := interior_subset hx
    exact (hasDerivAt_cot x
      (Real.sin_pos_of_pos_of_lt_pi (ha.trans_le hx'.1) (hx'.2.trans_lt hb)).ne').differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : x ∈ Set.Icc a b := interior_subset hx
    have hs : Real.sin x ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi (ha.trans_le hx'.1) (hx'.2.trans_lt hb)).ne'
    rw [(hasDerivAt_cot x hs).deriv]
    exact neg_nonpos.mpr (by positivity)

/-- The distance between reciprocal unit-circle chords is a cotangent
difference when the angles move monotonically through `(0, 2π)`. -/
lemma norm_reciprocal_exp_sub_one_sub_eq {x y : ℝ}
    (hx : 0 < x) (hy : y < 2 * Real.pi) (hxy : x ≤ y) :
    ‖(Complex.exp (Complex.I * (x : ℂ)) - 1)⁻¹ -
        (Complex.exp (Complex.I * (y : ℂ)) - 1)⁻¹‖ =
      (Real.cot (x / 2) - Real.cot (y / 2)) / 2 := by
  have hxhalf : 0 < x / 2 := by positivity
  have hyhalf : y / 2 < Real.pi := by linarith
  have hsinx : Real.sin (x / 2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hxhalf (lt_of_le_of_lt (by linarith) hyhalf)).ne'
  have hsiny : Real.sin (y / 2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (hxhalf.trans_le (by linarith)) hyhalf).ne'
  have hcot : Real.cot (y / 2) ≤ Real.cot (x / 2) :=
    antitoneOn_cot_Icc hxhalf hyhalf
      (Set.left_mem_Icc.mpr (by linarith)) (Set.right_mem_Icc.mpr (by linarith)) (by linarith)
  rw [reciprocal_exp_sub_one_eq x hsinx, reciprocal_exp_sub_one_eq y hsiny]
  have heq :
      (-1 / 2 : ℂ) - Complex.I * (Real.cot (x / 2) / 2 : ℝ) -
          ((-1 / 2 : ℂ) - Complex.I * (Real.cot (y / 2) / 2 : ℝ)) =
        -Complex.I * (((Real.cot (x / 2) - Real.cot (y / 2)) / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  have hnonneg : 0 ≤ (Real.cot (x / 2) - Real.cot (y / 2)) / 2 :=
    div_nonneg (sub_nonneg.mpr hcot) (by norm_num)
  rw [heq, norm_mul, norm_neg, Complex.norm_I, one_mul]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]

lemma norm_reciprocal_exp_sub_one_sub_eq_of_ge {x y : ℝ}
    (hy : 0 < y) (hx : x < 2 * Real.pi) (hyx : y ≤ x) :
    ‖(Complex.exp (Complex.I * (x : ℂ)) - 1)⁻¹ -
        (Complex.exp (Complex.I * (y : ℂ)) - 1)⁻¹‖ =
      (Real.cot (y / 2) - Real.cot (x / 2)) / 2 := by
  rw [← norm_neg, neg_sub]
  exact norm_reciprocal_exp_sub_one_sub_eq hy hx hyx

/-- Reciprocal-chord variation telescopes for a monotone sequence of angles in
`(0, 2π)`. -/
lemma sum_norm_reciprocal_exp_sub_one_eq (theta : ℕ → ℝ) (N : ℕ)
    (hpos : ∀ k ≤ N, 0 < theta k)
    (hlt : ∀ k ≤ N, theta k < 2 * Real.pi)
    (hmono : ∀ k < N, theta k ≤ theta (k + 1)) :
    ∑ k ∈ Finset.range N,
        ‖(Complex.exp (Complex.I * (theta k : ℂ)) - 1)⁻¹ -
          (Complex.exp (Complex.I * (theta (k + 1) : ℂ)) - 1)⁻¹‖ =
      (Real.cot (theta 0 / 2) - Real.cot (theta N / 2)) / 2 := by
  calc
    ∑ k ∈ Finset.range N,
        ‖(Complex.exp (Complex.I * (theta k : ℂ)) - 1)⁻¹ -
          (Complex.exp (Complex.I * (theta (k + 1) : ℂ)) - 1)⁻¹‖ =
        ∑ k ∈ Finset.range N,
          (Real.cot (theta k / 2) - Real.cot (theta (k + 1) / 2)) / 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      exact norm_reciprocal_exp_sub_one_sub_eq
        (hpos k (Nat.le_of_lt (Finset.mem_range.mp hk)))
        (hlt (k + 1) (Nat.succ_le_of_lt (Finset.mem_range.mp hk)))
        (hmono k (Finset.mem_range.mp hk))
    _ = (∑ k ∈ Finset.range N,
          (Real.cot (theta k / 2) - Real.cot (theta (k + 1) / 2))) / 2 := by
      rw [Finset.sum_div]
    _ = (Real.cot (theta 0 / 2) - Real.cot (theta N / 2)) / 2 := by
      rw [Finset.sum_range_sub']

/-- Antitone counterpart of `sum_norm_reciprocal_exp_sub_one_eq`. -/
lemma sum_norm_reciprocal_exp_sub_one_eq_antitone (theta : ℕ → ℝ) (N : ℕ)
    (hpos : ∀ k ≤ N, 0 < theta k)
    (hlt : ∀ k ≤ N, theta k < 2 * Real.pi)
    (hanti : ∀ k < N, theta (k + 1) ≤ theta k) :
    ∑ k ∈ Finset.range N,
        ‖(Complex.exp (Complex.I * (theta k : ℂ)) - 1)⁻¹ -
          (Complex.exp (Complex.I * (theta (k + 1) : ℂ)) - 1)⁻¹‖ =
      (Real.cot (theta N / 2) - Real.cot (theta 0 / 2)) / 2 := by
  calc
    ∑ k ∈ Finset.range N,
        ‖(Complex.exp (Complex.I * (theta k : ℂ)) - 1)⁻¹ -
          (Complex.exp (Complex.I * (theta (k + 1) : ℂ)) - 1)⁻¹‖ =
        ∑ k ∈ Finset.range N,
          (Real.cot (theta (k + 1) / 2) - Real.cot (theta k / 2)) / 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      exact norm_reciprocal_exp_sub_one_sub_eq_of_ge
        (hpos (k + 1) (Nat.succ_le_of_lt (Finset.mem_range.mp hk)))
        (hlt k (Nat.le_of_lt (Finset.mem_range.mp hk)))
        (hanti k (Finset.mem_range.mp hk))
    _ = (∑ k ∈ Finset.range N,
          (Real.cot (theta (k + 1) / 2) - Real.cot (theta k / 2))) / 2 := by
      rw [Finset.sum_div]
    _ = (Real.cot (theta N / 2) - Real.cot (theta 0 / 2)) / 2 := by
      congr 1
      exact Finset.sum_range_sub (fun k ↦ Real.cot (theta k / 2)) N

end ZeroFreeRegion.VinogradovKorobov
