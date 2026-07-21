import PrimeNumberTheorem.TriangleFourierKernel

open Complex
open FourierTransform
open MeasureTheory Set

namespace PrimeNumberTheorem
namespace DirichletPolynomial

example : Continuous triangleFourierKernel :=
  continuous_triangleFourierKernel

example (x : ℝ) : 0 ≤ triangleFourierKernel x :=
  triangleFourierKernel_nonneg x

example {x : ℝ} (hx : x ∉ Set.Icc (-1 : ℝ) 1) :
    triangleFourierKernel x = 0 :=
  triangleFourierKernel_eq_zero_of_not_mem_Icc hx

example : HasCompactSupport triangleFourierKernel :=
  hasCompactSupport_triangleFourierKernel

example : Integrable triangleFourierKernel :=
  integrable_triangleFourierKernel

example : triangleFourierKernel 0 = 1 :=
  triangleFourierKernel_zero

example : (∫ x : ℝ, triangleFourierKernel x) = 1 :=
  integral_triangleFourierKernel

example (ξ : ℝ) :
    𝓕 (fun x : ℝ => (triangleFourierKernel x : ℂ)) ξ =
      ((Real.sinc (Real.pi * ξ) ^ 2 : ℝ) : ℂ) :=
  fourier_triangleFourierKernel ξ

example : (∫ x : ℝ, carneiroLittmannSincSquareBase x) = 1 :=
  integral_carneiroLittmannSincSquareBase_eq_one

example : (∫ x : ℝ, carneiroLittmannDerivative x) = 1 :=
  integral_carneiroLittmannDerivative_eq_one

#print axioms continuous_triangleFourierKernel
#print axioms triangleFourierKernel_nonneg
#print axioms triangleFourierKernel_eq_zero_of_not_mem_Icc
#print axioms hasCompactSupport_triangleFourierKernel
#print axioms integrable_triangleFourierKernel
#print axioms triangleFourierKernel_zero
#print axioms integral_triangleFourierKernel
#print axioms fourier_triangleFourierKernel
#print axioms integral_carneiroLittmannSincSquareBase_eq_one
#print axioms integral_carneiroLittmannDerivative_eq_one

end DirichletPolynomial
end PrimeNumberTheorem
