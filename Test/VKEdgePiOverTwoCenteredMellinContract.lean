import PrimeNumberTheorem.VKEdgePiOverTwoCenteredMellin

open Complex MeasureTheory Polynomial

namespace PrimeNumberTheorem.VKEdgePiOverTwo

#check localizedGaussianWeightAtCenter
#check localizedPsiGaussianAverageAtCenter
#check integral_rightEdgePolynomialGaussian_cpow_atCenter_eq
#check integral_localizedGaussianWeightAtCenter_mul_regularizedLogDeriv_rightEdge_eq
#check localizedGaussianWeightAtCenter_sixteen
#check localizedPsiGaussianAverageAtCenter_sixteen

example (q : ℝ) (A : ℂ[X]) {m : ℝ} (hm : 0 < m)
    (w : ℂ) {x : ℝ} (hx : 0 < x) :
    (∫ t : ℝ,
        (w + ((2 : ℂ) + I * (t : ℂ))) *
          A.eval ((2 : ℂ) + I * (t : ℂ)) *
          Complex.exp
            ((m : ℂ) * ((2 : ℂ) + I * (t : ℂ)) ^ 2 +
              ((q * m : ℝ) : ℂ) *
                ((2 : ℂ) + I * (t : ℂ))) *
          (x : ℂ) ^
            (-((w + ((2 : ℂ) + I * (t : ℂ))) + 1))) =
      (2 * Real.pi : ℂ) *
        ((x : ℂ) ^ (-(w + 1)) *
          (w * polynomialGaussianKernel A m
              (q * m - Real.log x) +
            polynomialGaussianKernelDeriv A m
              (q * m - Real.log x))) :=
  integral_rightEdgePolynomialGaussian_cpow_atCenter_eq q A hm w hx

example (q : ℝ) (A : ℂ[X]) {m : ℝ} (hm : 0 < m)
    {w : ℂ} (hw : 0 < w.re) :
    (∫ t : ℝ,
        localizedGaussianWeightAtCenter q A w m
            (w + ((2 : ℂ) + I * (t : ℂ))) *
          (-logDeriv riemannZeta
              (w + ((2 : ℂ) + I * (t : ℂ))) -
            (w + ((2 : ℂ) + I * (t : ℂ))) /
              (w + ((2 : ℂ) + I * (t : ℂ)) - 1))) =
      localizedPsiGaussianAverageAtCenter q A w m :=
  integral_localizedGaussianWeightAtCenter_mul_regularizedLogDeriv_rightEdge_eq
    q A hm hw

example (A : ℂ[X]) (w : ℂ) (m : ℝ) :
    localizedGaussianWeightAtCenter 16 A w m =
      localizedGaussianWeight A w m :=
  localizedGaussianWeightAtCenter_sixteen A w m

example (A : ℂ[X]) (w : ℂ) (m : ℝ) :
    localizedPsiGaussianAverageAtCenter 16 A w m =
      localizedPsiGaussianAverage A w m :=
  localizedPsiGaussianAverageAtCenter_sixteen A w m

end PrimeNumberTheorem.VKEdgePiOverTwo
