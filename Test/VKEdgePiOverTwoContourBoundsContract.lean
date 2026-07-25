import PrimeNumberTheorem.VKEdgePiOverTwoContourBounds

open Complex Polynomial

open PrimeNumberTheorem.VKEdgePiOverTwo

#check norm_localizedGaussianWeight
#check norm_localizedGaussianWeight_left_le
#check norm_polynomial_eval_le_coeffL1_mul_max_pow
#check leftLogDerivBound
#check norm_div_sub_one_left_vertical_le_one
#check norm_regularizedLogDeriv_localizedGaussianWeight_left_le

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

example (t : ℝ) :
    ‖(((-1 : ℂ) + I * t) /
      (((-1 : ℂ) + I * t) - 1))‖ ≤ 1 :=
  norm_div_sub_one_left_vertical_le_one t

example (A : ℂ[X]) {u v T t m : ℝ}
    (hu : 0 < u) (hu1 : u < 1)
    (hT : 0 ≤ T) (ht : |t| ≤ T) (hm : 0 ≤ m) :
    ‖localizedGaussianWeight A ((u : ℂ) + I * v) m
          ((-1 : ℂ) + I * t) *
        (-logDeriv riemannZeta ((-1 : ℂ) + I * t) -
          (((-1 : ℂ) + I * t) /
            (((-1 : ℂ) + I * t) - 1)))‖ ≤
      ‖A.eval (((-1 : ℂ) + I * t) - ((u : ℂ) + I * v))‖ *
        Real.exp (-15 * m - m * (t - v) ^ 2) *
          (leftLogDerivBound T + 1) :=
  norm_regularizedLogDeriv_localizedGaussianWeight_left_le
    A hu hu1 hT ht hm
