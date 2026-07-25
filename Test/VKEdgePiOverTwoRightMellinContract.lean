import PrimeNumberTheorem.VKEdgePiOverTwoRightMellin

open Complex MeasureTheory Polynomial

open PrimeNumberTheorem.VKEdgePiOverTwo

#check ofReal_cpow_neg_add_split
#check integral_rightEdgePolynomialGaussian_cpow_eq

example (A : ℂ[X]) {m : ℝ} (hm : 0 < m)
    (w : ℂ) {x : ℝ} (hx : 0 < x) :
    (∫ t : ℝ,
        (w + ((2 : ℂ) + I * (t : ℂ))) *
          A.eval ((2 : ℂ) + I * (t : ℂ)) *
          Complex.exp
            ((m : ℂ) * ((2 : ℂ) + I * (t : ℂ)) ^ 2 +
              ((16 * m : ℝ) : ℂ) *
                ((2 : ℂ) + I * (t : ℂ))) *
          (x : ℂ) ^
            (-((w + ((2 : ℂ) + I * (t : ℂ))) + 1))) =
      (2 * Real.pi : ℂ) *
        ((x : ℂ) ^ (-(w + 1)) *
          (w * polynomialGaussianKernel A m
              (16 * m - Real.log x) +
            polynomialGaussianKernelDeriv A m
              (16 * m - Real.log x))) :=
  integral_rightEdgePolynomialGaussian_cpow_eq A hm w hx
