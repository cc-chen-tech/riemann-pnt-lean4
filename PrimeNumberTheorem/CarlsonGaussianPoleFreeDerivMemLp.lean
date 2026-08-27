import PrimeNumberTheorem.CarlsonPoleFreeMollifiedErrorDerivGrowth

/-!
# Gaussian `L²` membership for the derivative term

This file treats the `H'` summand in the exact pointwise derivative of the
Carlson Gaussian Hilbert section.  The remaining linear-times-`H` summand is
kept separate so that each domination argument is independently auditable.
-/

open Complex Set MeasureTheory

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- On the fixed inner strip, the Gaussian section formed from the derivative
of the concrete pole-free error belongs to `L²(ℝ)`. -/
theorem
    memLp_carlsonGaussian_deriv_poleFreeTwoScaleMollifiedZetaError_on_inner_strip
    {Delta w : ℝ} {z : ℂ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    (hzre : z.re ∈ Icc (2 / 3 : ℝ) (47 / 12)) :
    MemLp
      (carlsonGaussianHilbertSection Delta w
        (deriv (poleFreeTwoScaleMollifiedZetaError Y0 Y1)) z) 2 volume := by
  rcases
      exists_norm_sq_deriv_poleFreeTwoScaleMollifiedZetaError_le_polynomial_on_inner_strip
        hY0 hY01 with ⟨C, hC, hgrowth⟩
  have hcont : Continuous fun t : ℝ =>
      deriv (poleFreeTwoScaleMollifiedZetaError Y0 Y1)
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
      hanalytic.deriv.continuousAt.comp hpoint
  let D : ℝ := |w| + 4
  have hD : 1 ≤ D := by
    dsimp [D]
    linarith [abs_nonneg w]
  have hbound : ∀ t : ℝ,
      ‖deriv (poleFreeTwoScaleMollifiedZetaError Y0 Y1)
          (z + I * (t : ℂ))‖ ^ 2 ≤
        (C * D ^ 20) * (1 + |z.im + t - w|) ^ 20 := by
    intro t
    let u : ℝ := z.im + t - w
    have habs : |z.im + t| ≤ |u| + |w| := by
      calc
        |z.im + t| = |u + w| := by
          congr 1
          dsimp [u]
          ring
        _ ≤ |u| + |w| := abs_add_le _ _
    have hlinear : |z.im + t| + 4 ≤ D * (1 + |u|) := by
      have huD : |u| ≤ D * |u| :=
        le_mul_of_one_le_left (abs_nonneg u) hD
      dsimp [D]
      nlinarith
    have hpow :
        (|z.im + t| + 4) ^ 20 ≤ (D * (1 + |u|)) ^ 20 :=
      pow_le_pow_left₀ (by positivity) hlinear 20
    have hraw := hgrowth (s := z + I * (t : ℂ)) (by simpa using hzre)
    calc
      ‖deriv (poleFreeTwoScaleMollifiedZetaError Y0 Y1)
          (z + I * (t : ℂ))‖ ^ 2
          ≤ C * (|z.im + t| + 4) ^ 20 := by simpa using hraw
      _ ≤ C * (D * (1 + |u|)) ^ 20 :=
        mul_le_mul_of_nonneg_left hpow hC
      _ = (C * D ^ 20) * (1 + |z.im + t - w|) ^ 20 := by
        dsimp [u]
        ring
  exact
    memLp_carlsonGaussianHilbertSection_of_complex_polynomial_sq_bound
      hDelta 20 (deriv (poleFreeTwoScaleMollifiedZetaError Y0 Y1))
      hcont hbound

end CarlsonZeroDensity
end PrimeNumberTheorem
