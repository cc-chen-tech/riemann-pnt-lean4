import PrimeNumberTheorem.VKEdgePiOverTwoGaussianMellin

open Complex MeasureTheory Polynomial

open PrimeNumberTheorem.VKEdgePiOverTwo

#check integral_verticalGaussian_eq
#check integral_verticalGaussian_monomial_zero_eq
#check integral_verticalPolynomialGaussian_zero_eq
#check integral_verticalGaussian_monomial_eq
#check integrable_verticalPolynomialGaussian
#check integral_verticalPolynomialGaussian_eq
#check integral_verticalPolynomialGaussian_add_mul_eq
#check integrable_verticalPolynomialGaussian_add_mul

example {m : ℝ} (hm : 0 < m) (c r : ℝ) :
    (∫ t : ℝ,
        Complex.exp
          ((m : ℂ) * ((c : ℂ) + I * t) ^ 2 +
            (r : ℂ) * ((c : ℂ) + I * t))) =
      (2 * Real.pi : ℂ) * (normalizedGaussian m r : ℂ) :=
  integral_verticalGaussian_eq hm c r

example (A : ℂ[X]) {m : ℝ} (hm : 0 < m) (r : ℝ) :
    (∫ t : ℝ,
        A.eval (I * (t : ℂ)) *
          Complex.exp
            ((m : ℂ) * (I * (t : ℂ)) ^ 2 +
              (r : ℂ) * (I * (t : ℂ)))) =
      (2 * Real.pi : ℂ) * polynomialGaussianKernel A m r :=
  integral_verticalPolynomialGaussian_zero_eq A hm r

example (A : ℂ[X]) {m : ℝ} (hm : 0 < m) (c r : ℝ) :
    (∫ t : ℝ,
        A.eval ((c : ℂ) + I * (t : ℂ)) *
          Complex.exp
            ((m : ℂ) * ((c : ℂ) + I * (t : ℂ)) ^ 2 +
              (r : ℂ) * ((c : ℂ) + I * (t : ℂ)))) =
      (2 * Real.pi : ℂ) * polynomialGaussianKernel A m r :=
  integral_verticalPolynomialGaussian_eq A hm c r

example (A : ℂ[X]) {m : ℝ} (hm : 0 < m)
    (w : ℂ) (c r : ℝ) :
    (∫ t : ℝ,
        (w + ((c : ℂ) + I * (t : ℂ))) *
          A.eval ((c : ℂ) + I * (t : ℂ)) *
          Complex.exp
            ((m : ℂ) * ((c : ℂ) + I * (t : ℂ)) ^ 2 +
              (r : ℂ) * ((c : ℂ) + I * (t : ℂ)))) =
      (2 * Real.pi : ℂ) *
        (w * polynomialGaussianKernel A m r +
          polynomialGaussianKernelDeriv A m r) :=
  integral_verticalPolynomialGaussian_add_mul_eq A hm w c r

example (A : ℂ[X]) {m : ℝ} (hm : 0 < m)
    (w : ℂ) (c r : ℝ) :
    Integrable
      (fun t : ℝ =>
        (w + ((c : ℂ) + I * (t : ℂ))) *
          A.eval ((c : ℂ) + I * (t : ℂ)) *
          Complex.exp
            ((m : ℂ) * ((c : ℂ) + I * (t : ℂ)) ^ 2 +
              (r : ℂ) * ((c : ℂ) + I * (t : ℂ)))) :=
  integrable_verticalPolynomialGaussian_add_mul A hm w c r
