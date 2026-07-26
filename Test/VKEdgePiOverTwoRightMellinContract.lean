import PrimeNumberTheorem.VKEdgePiOverTwoRightMellin

open Complex MeasureTheory Polynomial

open PrimeNumberTheorem.VKEdgePiOverTwo

#check ofReal_cpow_neg_add_split
#check neg_logDeriv_sub_pole_eq_mul_mellin
#check neg_logDeriv_sub_pole_rightEdge_eq_mul_mellin
#check integrableOn_psiErrorAboveOneComplex_mul_cpow
#check integral_rightEdgePolynomialGaussian_cpow_eq
#check localizedGaussianWeight_mul_regularizedLogDeriv_rightEdge_eq
#check rightEdgeGaussianFactor
#check rightEdgeGaussianFactor_eq_localizedGaussianWeight_mul
#check localizedGaussianWeight_mul_regularizedLogDeriv_rightEdge_eq_factor
#check rightEdgeMellinProduct
#check integrable_rightEdgeMellinProduct
#check integral_rightEdgeGaussianFactor_exp_eq
#check integral_rightEdgeMellinProduct_snd_eq
#check integral_rightEdgeMellinProduct_fst_eq
#check integral_rightEdgeGaussianFactor_mul_mellin_eq
#check integral_localizedGaussianWeight_mul_regularizedLogDeriv_rightEdge_eq
#check integrable_localizedGaussianWeight_mul_regularizedLogDeriv_rightEdge
#check tendsto_intervalIntegral_localizedGaussianWeight_mul_regularizedLogDeriv_rightEdge

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
