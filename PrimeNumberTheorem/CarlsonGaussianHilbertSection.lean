import MathlibAux.HadamardThreeLinesSquared

/-!
# Gaussian strip sections for the Carlson Hilbert three-lines argument

This file fixes the precise complex Gaussian normalization used to turn a
vertical second moment into the norm of a Banach-valued strip function.
-/

open Complex

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- The unnormalized Gaussian height weight centered at `w`. -/
noncomputable def carlsonGaussianWeight (Delta w t : ℝ) : ℝ :=
  Real.exp (-((t - w) ^ 2) / Delta ^ 2)

/-- Pointwise section underlying the `L²(ℝ)`-valued strip map. -/
noncomputable def carlsonGaussianHilbertSection
    (Delta w : ℝ) (H : ℂ → ℂ) (z : ℂ) (t : ℝ) : ℂ :=
  Complex.exp
      ((z + I * (t : ℂ) - I * (w : ℂ)) ^ 2 /
        (2 * (Delta : ℂ) ^ 2)) *
    H (z + I * (t : ℂ))

/-- Exact norm-square of the Gaussian strip section at an arbitrary complex
strip parameter. -/
theorem norm_sq_carlsonGaussianHilbertSection
    {Delta w : ℝ} (hDelta : Delta ≠ 0)
    (H : ℂ → ℂ) (z : ℂ) (t : ℝ) :
    ‖carlsonGaussianHilbertSection Delta w H z t‖ ^ 2 =
      Real.exp
          ((z.re ^ 2 - (z.im + t - w) ^ 2) / Delta ^ 2) *
        ‖H (z + I * (t : ℂ))‖ ^ 2 := by
  have hDeltaSq : Delta ^ 2 ≠ 0 := pow_ne_zero 2 hDelta
  let q : ℂ := z + I * (t : ℂ) - I * (w : ℂ)
  have hqre : q.re = z.re := by simp [q]
  have hqim : q.im = z.im + t - w := by simp [q]
  have hden : (2 * (Delta : ℂ) ^ 2) = ((2 * Delta ^ 2 : ℝ) : ℂ) := by
    norm_num
  have hre :
      (((z + I * (t : ℂ) - I * (w : ℂ)) ^ 2 /
        (2 * (Delta : ℂ) ^ 2))).re =
        (z.re ^ 2 - (z.im + t - w) ^ 2) / (2 * Delta ^ 2) := by
    change (q ^ 2 / (2 * (Delta : ℂ) ^ 2)).re = _
    rw [hden, Complex.div_ofReal_re, pow_two, Complex.mul_re, hqre, hqim]
    ring
  rw [carlsonGaussianHilbertSection, norm_mul, Complex.norm_exp, hre,
    mul_pow, ← Real.exp_nat_mul]
  congr 1
  field_simp [hDeltaSq]
  ring

/-- On a real strip parameter, the norm-square is a constant horizontal
factor times the desired Gaussian height weight. -/
theorem norm_sq_carlsonGaussianHilbertSection_real
    {Delta w : ℝ} (hDelta : Delta ≠ 0)
    (H : ℂ → ℂ) (x t : ℝ) :
    ‖carlsonGaussianHilbertSection Delta w H (x : ℂ) t‖ ^ 2 =
      Real.exp (x ^ 2 / Delta ^ 2) *
        carlsonGaussianWeight Delta w t *
        ‖H ((x : ℂ) + I * (t : ℂ))‖ ^ 2 := by
  rw [norm_sq_carlsonGaussianHilbertSection hDelta H (x : ℂ) t]
  simp only [ofReal_re, ofReal_im, zero_add]
  dsimp [carlsonGaussianWeight]
  calc
    Real.exp ((x ^ 2 - (t - w) ^ 2) / Delta ^ 2) *
        ‖H ((x : ℂ) + I * (t : ℂ))‖ ^ 2 =
      (Real.exp (x ^ 2 / Delta ^ 2) *
          Real.exp (-((t - w) ^ 2) / Delta ^ 2)) *
        ‖H ((x : ℂ) + I * (t : ℂ))‖ ^ 2 := by
      rw [← Real.exp_add]
      congr 2
      field_simp [pow_ne_zero 2 hDelta]
      ring
    _ = Real.exp (x ^ 2 / Delta ^ 2) *
        Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
        ‖H ((x : ℂ) + I * (t : ℂ))‖ ^ 2 := by ring

end CarlsonZeroDensity
end PrimeNumberTheorem
