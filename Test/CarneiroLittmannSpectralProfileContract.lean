import PrimeNumberTheorem.CarneiroLittmannSpectralProfile

open MeasureTheory Set
open FourierTransform

namespace PrimeNumberTheorem
namespace DirichletPolynomial

example : Continuous carneiroLittmannSpectralProfile :=
  continuous_carneiroLittmannSpectralProfile

example : HasCompactSupport carneiroLittmannSpectralProfile :=
  hasCompactSupport_carneiroLittmannSpectralProfile

example : Integrable carneiroLittmannSpectralProfile :=
  integrable_carneiroLittmannSpectralProfile

example {u : ℝ} (hu : 1 ≤ |u|) :
    carneiroLittmannSpectralProfile u = 0 :=
  carneiroLittmannSpectralProfile_eq_zero_of_one_le_abs hu

example (u : ℝ) : HasDerivAt carneiroLittmannSpectralPrimitive
    (carneiroLittmannSpectralPrimitiveDerivative u) u :=
  hasDerivAt_carneiroLittmannSpectralPrimitive u

example : Differentiable ℝ carneiroLittmannSpectralPrimitive :=
  differentiable_carneiroLittmannSpectralPrimitive

example : Integrable carneiroLittmannSpectralPrimitive :=
  integrable_carneiroLittmannSpectralPrimitive

example : Integrable (deriv carneiroLittmannSpectralPrimitive) :=
  integrable_deriv_carneiroLittmannSpectralPrimitive

example (u : ℝ) :
    carneiroLittmannSpectralPrimitiveDerivative u =
      (((2 * Real.pi : ℝ) : ℂ) * Complex.I) *
        (carneiroLittmannSpectralProfile u -
          2 * (triangleFourierKernel u : ℂ) *
            carneiroLittmannSpectralPhase u) :=
  carneiroLittmannSpectralPrimitiveDerivative_eq u

example (x : ℝ) :
    𝓕 carneiroLittmannSpectralProfile x =
      (carneiroLittmannDerivative x : ℂ) :=
  fourier_carneiroLittmannSpectralProfile x

example (xi : ℝ) :
    fourierKernel carneiroLittmannDerivative xi =
      carneiroLittmannSpectralProfile (xi / (2 * Real.pi)) :=
  fourierKernel_carneiroLittmannDerivative_eq_spectralProfile xi

example {xi : ℝ} (hxi : 2 * Real.pi ≤ |xi|) :
    fourierKernel carneiroLittmannDerivative xi = 0 :=
  fourierKernel_carneiroLittmannDerivative_eq_zero_of_two_pi_le_abs hxi

#print axioms continuous_carneiroLittmannSpectralProfile
#print axioms hasCompactSupport_carneiroLittmannSpectralProfile
#print axioms integrable_carneiroLittmannSpectralProfile
#print axioms carneiroLittmannSpectralProfile_eq_zero_of_one_le_abs
#print axioms hasDerivAt_carneiroLittmannSpectralPrimitive
#print axioms differentiable_carneiroLittmannSpectralPrimitive
#print axioms integrable_carneiroLittmannSpectralPrimitive
#print axioms integrable_deriv_carneiroLittmannSpectralPrimitive
#print axioms carneiroLittmannSpectralPrimitiveDerivative_eq
#print axioms fourier_carneiroLittmannSpectralProfile
#print axioms fourierKernel_carneiroLittmannDerivative_eq_spectralProfile
#print axioms fourierKernel_carneiroLittmannDerivative_eq_zero_of_two_pi_le_abs

end DirichletPolynomial
end PrimeNumberTheorem
