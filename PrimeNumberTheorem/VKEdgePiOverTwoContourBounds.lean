import PrimeNumberTheorem.VKEdgePiOverTwoZetaContour

open Complex Polynomial

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- Exact modulus of the polynomial-Gaussian contour weight. -/
theorem norm_localizedGaussianWeight
    (A : ℂ[X]) (w z : ℂ) (m : ℝ) :
    ‖localizedGaussianWeight A w m z‖ =
      ‖A.eval (z - w)‖ *
        Real.exp
          (m * (((z - w).re) ^ 2 - ((z - w).im) ^ 2 +
            16 * (z - w).re)) := by
  unfold localizedGaussianWeight
  rw [norm_mul, Complex.norm_exp]
  congr 2
  simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/--
A fixed polynomial grows at most like its coefficient `L¹` norm times the
maximum of `1` and the evaluation radius, raised to the polynomial degree.
-/
theorem norm_polynomial_eval_le_coeffL1_mul_max_pow
    (A : ℂ[X]) (z : ℂ) :
    ‖A.eval z‖ ≤
      (∑ k ∈ A.support, ‖A.coeff k‖) *
        max 1 ‖z‖ ^ A.natDegree := by
  rw [A.eval_eq_sum]
  calc
    ‖∑ k ∈ A.support, A.coeff k * z ^ k‖ ≤
        ∑ k ∈ A.support, ‖A.coeff k * z ^ k‖ :=
      norm_sum_le A.support fun k => A.coeff k * z ^ k
    _ = ∑ k ∈ A.support, ‖A.coeff k‖ * ‖z‖ ^ k := by
      simp only [norm_mul, norm_pow]
    _ ≤ ∑ k ∈ A.support,
        ‖A.coeff k‖ * max 1 ‖z‖ ^ A.natDegree := by
      apply Finset.sum_le_sum
      intro k hk
      gcongr
      exact
        (pow_le_pow_left₀ (norm_nonneg z) (le_max_right 1 ‖z‖) k).trans
          (pow_le_pow_right₀ (le_max_left 1 ‖z‖)
            (A.le_natDegree_of_mem_supp k hk))
    _ = (∑ k ∈ A.support, ‖A.coeff k‖) *
        max 1 ‖z‖ ^ A.natDegree := by
      rw [Finset.sum_mul]

/--
On the fixed left edge `Re(z) = -1`, the Gaussian factor has a uniform
exponential saving.  The constant `15` is valid simultaneously for every
center real part `0 < u < 1`.
-/
theorem norm_localizedGaussianWeight_left_le
    (A : ℂ[X]) {u v t m : ℝ}
    (hu : 0 < u) (hu1 : u < 1) (hm : 0 ≤ m) :
    ‖localizedGaussianWeight A
        ((u : ℂ) + I * v) m
        ((-1 : ℂ) + I * t)‖ ≤
      ‖A.eval (((-1 : ℂ) + I * t) - ((u : ℂ) + I * v))‖ *
        Real.exp (-15 * m - m * (t - v) ^ 2) := by
  rw [norm_localizedGaussianWeight]
  gcongr
  norm_num [Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have huProduct : 0 < u * (1 - u) :=
    mul_pos hu (sub_pos.mpr hu1)
  nlinarith

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
