import PrimeNumberTheorem.CarlsonPoleFreeMollifiedErrorGrowth

/-!
# Gaussian `L²` membership for the linear-times-error derivative term

Differentiating the complex Gaussian contributes the scalar factor
`(s - I*w) / Delta^2`.  This file proves that multiplying the pole-free
Carlson error by that linear factor preserves Gaussian `L²` membership.
-/

open Complex Set MeasureTheory

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- Scalar analytic factor arising from differentiation of the Gaussian. -/
noncomputable def carlsonGaussianLinearErrorFactor
    (Delta w : ℝ) (H : ℂ → ℂ) (s : ℂ) : ℂ :=
  (s - I * (w : ℂ)) / (Delta : ℂ) ^ 2 * H s

/-- On the fixed inner strip, the Gaussian section formed from the
linear-times-error term belongs to `L²(ℝ)`. -/
theorem
    memLp_carlsonGaussian_linear_poleFreeTwoScaleMollifiedZetaError_on_inner_strip
    {Delta w : ℝ} {z : ℂ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    (hzre : z.re ∈ Icc (2 / 3 : ℝ) (47 / 12)) :
    MemLp
      (carlsonGaussianHilbertSection Delta w
        (carlsonGaussianLinearErrorFactor Delta w
          (poleFreeTwoScaleMollifiedZetaError Y0 Y1)) z) 2 volume := by
  rcases
      exists_norm_sq_poleFreeTwoScaleMollifiedZetaError_le_polynomial_on_half_four
        hY0 hY01 with ⟨C, hC, hgrowth⟩
  have hDelta0 : Delta ≠ 0 := ne_of_gt hDelta
  have hcont : Continuous fun t : ℝ =>
      carlsonGaussianLinearErrorFactor Delta w
        (poleFreeTwoScaleMollifiedZetaError Y0 Y1)
        (z + I * (t : ℂ)) := by
    have hHcont : Continuous fun t : ℝ =>
        poleFreeTwoScaleMollifiedZetaError Y0 Y1
          (z + I * (t : ℂ)) := by
      rw [continuous_iff_continuousAt]
      intro t
      let point : ℝ → ℂ := fun u => z + I * (u : ℂ)
      have hpoint : ContinuousAt point t := by
        dsimp [point]
        fun_prop
      have hre : 0 < (point t).re := by
        dsimp [point]
        simp only [mul_re, I_re, ofReal_re, I_im, ofReal_im,
          zero_mul, one_mul, sub_self, add_zero]
        linarith [hzre.1]
      have hanalytic :
          AnalyticAt ℂ (poleFreeTwoScaleMollifiedZetaError Y0 Y1) (point t) :=
        analyticOnNhd_poleFreeTwoScaleMollifiedZetaError_re_gt
          (theta := 0) le_rfl Y0 Y1 (point t) hre
      simpa [point, Function.comp_def] using
        hanalytic.continuousAt.comp hpoint
    unfold carlsonGaussianLinearErrorFactor
    fun_prop
  let D : ℝ := |w| + 3
  have hD : 1 ≤ D := by
    dsimp [D]
    linarith [abs_nonneg w]
  let E : ℝ := 16 * C * D ^ 10 / Delta ^ 4
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  have hbound : ∀ t : ℝ,
      ‖carlsonGaussianLinearErrorFactor Delta w
          (poleFreeTwoScaleMollifiedZetaError Y0 Y1)
          (z + I * (t : ℂ))‖ ^ 2 ≤
        E * (1 + |z.im + t - w|) ^ 12 := by
    intro t
    let u : ℝ := z.im + t - w
    let q : ℂ := z + I * (t : ℂ) - I * (w : ℂ)
    have hqre : q.re = z.re := by simp [q]
    have hqim : q.im = u := by simp [q, u]
    have hzreAbs : |z.re| ≤ 4 := by
      rw [abs_of_nonneg (by linarith [hzre.1])]
      linarith [hzre.2]
    have hqnorm : ‖q‖ ≤ 4 * (1 + |u|) := by
      calc
        ‖q‖ ≤ |q.re| + |q.im| := Complex.norm_le_abs_re_add_abs_im q
        _ = |z.re| + |u| := by rw [hqre, hqim]
        _ ≤ 4 + |u| := add_le_add hzreAbs le_rfl
        _ ≤ 4 * (1 + |u|) := by nlinarith [abs_nonneg u]
    have hqpow : ‖q‖ ^ 2 ≤ 16 * (1 + |u|) ^ 2 := by
      calc
        ‖q‖ ^ 2 ≤ (4 * (1 + |u|)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg q) hqnorm 2
        _ = 16 * (1 + |u|) ^ 2 := by ring
    have habs : |z.im + t| ≤ |u| + |w| := by
      calc
        |z.im + t| = |u + w| := by
          congr 1
          dsimp [u]
          ring
        _ ≤ |u| + |w| := abs_add_le _ _
    have hlinear : |z.im + t| + 3 ≤ D * (1 + |u|) := by
      have huD : |u| ≤ D * |u| :=
        le_mul_of_one_le_left (abs_nonneg u) hD
      dsimp [D]
      nlinarith
    have hpow10 :
        (|z.im + t| + 3) ^ 10 ≤ (D * (1 + |u|)) ^ 10 :=
      pow_le_pow_left₀ (by positivity) hlinear 10
    have hzHalfFour : z.re ∈ Icc (1 / 2 : ℝ) 4 := by
      constructor <;> linarith [hzre.1, hzre.2]
    have hHraw := hgrowth (s := z + I * (t : ℂ)) (by
      simpa using hzHalfFour)
    have hHbound :
        ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1
            (z + I * (t : ℂ))‖ ^ 2 ≤
          (C * D ^ 10) * (1 + |u|) ^ 10 := by
      calc
        ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1
            (z + I * (t : ℂ))‖ ^ 2
            ≤ C * (|z.im + t| + 3) ^ 10 := by simpa using hHraw
        _ ≤ C * (D * (1 + |u|)) ^ 10 :=
          mul_le_mul_of_nonneg_left hpow10 hC
        _ = (C * D ^ 10) * (1 + |u|) ^ 10 := by ring
    have hfactorSq :
        ‖q / (Delta : ℂ) ^ 2‖ ^ 2 ≤
          (16 / Delta ^ 4) * (1 + |u|) ^ 2 := by
      rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hDelta]
      have hDeltaSqPos : 0 < Delta ^ 2 := sq_pos_of_pos hDelta
      calc
        (‖q‖ / Delta ^ 2) ^ 2 = ‖q‖ ^ 2 / Delta ^ 4 := by ring
        _ ≤ (16 * (1 + |u|) ^ 2) / Delta ^ 4 :=
          div_le_div_of_nonneg_right hqpow (by positivity)
        _ = (16 / Delta ^ 4) * (1 + |u|) ^ 2 := by ring
    rw [carlsonGaussianLinearErrorFactor, norm_mul, mul_pow]
    change
      ‖q / (Delta : ℂ) ^ 2‖ ^ 2 *
          ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1
            (z + I * (t : ℂ))‖ ^ 2 ≤ _
    calc
      ‖q / (Delta : ℂ) ^ 2‖ ^ 2 *
            ‖poleFreeTwoScaleMollifiedZetaError Y0 Y1
              (z + I * (t : ℂ))‖ ^ 2
          ≤ ((16 / Delta ^ 4) * (1 + |u|) ^ 2) *
              ((C * D ^ 10) * (1 + |u|) ^ 10) := by
            gcongr
      _ = E * (1 + |z.im + t - w|) ^ 12 := by
        dsimp [E, u]
        field_simp [pow_ne_zero 4 hDelta0]
  exact
    memLp_carlsonGaussianHilbertSection_of_complex_polynomial_sq_bound
      hDelta 12
      (carlsonGaussianLinearErrorFactor Delta w
        (poleFreeTwoScaleMollifiedZetaError Y0 Y1)) hcont hbound

end CarlsonZeroDensity
end PrimeNumberTheorem
