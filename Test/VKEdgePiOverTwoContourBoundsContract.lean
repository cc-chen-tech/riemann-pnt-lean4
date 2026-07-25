import PrimeNumberTheorem.VKEdgePiOverTwoContourBounds

open Complex Polynomial

open PrimeNumberTheorem.VKEdgePiOverTwo

#check norm_localizedGaussianWeight
#check norm_localizedGaussianWeight_left_le
#check norm_polynomial_eval_le_coeffL1_mul_max_pow

example (A : ℂ[X]) (w z : ℂ) (m : ℝ) :
    ‖localizedGaussianWeight A w m z‖ =
      ‖A.eval (z - w)‖ *
        Real.exp
          (m * (((z - w).re) ^ 2 - ((z - w).im) ^ 2 +
            16 * (z - w).re)) :=
  norm_localizedGaussianWeight A w z m

example (A : ℂ[X]) {u v t m : ℝ}
    (hu : 0 < u) (hu1 : u < 1) (hm : 0 ≤ m) :
    ‖localizedGaussianWeight A
        ((u : ℂ) + I * v) m
        ((-1 : ℂ) + I * t)‖ ≤
      ‖A.eval (((-1 : ℂ) + I * t) - ((u : ℂ) + I * v))‖ *
        Real.exp (-15 * m - m * (t - v) ^ 2) :=
  norm_localizedGaussianWeight_left_le A hu hu1 hm

example (A : ℂ[X]) (z : ℂ) :
    ‖A.eval z‖ ≤
      (∑ k ∈ A.support, ‖A.coeff k‖) *
        max 1 ‖z‖ ^ A.natDegree :=
  norm_polynomial_eval_le_coeffL1_mul_max_pow A z
