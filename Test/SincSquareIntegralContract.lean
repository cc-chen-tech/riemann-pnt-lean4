import PrimeNumberTheorem.SincSquareIntegral

open FourierTransform MeasureTheory

namespace PrimeNumberTheorem
namespace SincSquareIntegral

noncomputable example (x : ℝ) : ℂ := centeredUnitIntervalIndicator x

example (xi : ℝ) :
    𝓕 centeredUnitIntervalIndicator xi =
      (Real.sinc (Real.pi * xi) : ℂ) :=
  fourier_centeredUnitIntervalIndicator xi

example : Integrable (fun x : ℝ => Real.sinc x ^ 2) :=
  integrable_sinc_sq

example : MemLp centeredUnitIntervalIndicator 1 :=
  centeredUnitIntervalIndicator_memLp_one

example : MemLp centeredUnitIntervalIndicator 2 :=
  centeredUnitIntervalIndicator_memLp_two

example : MemLp (fun x : ℝ =>
    (Real.sinc (Real.pi * x) : ℂ)) 2 :=
  memLp_two_complex_sinc_pi

example : ∫ x : ℝ, Real.sinc (Real.pi * x) ^ 2 = 1 :=
  integral_sinc_pi_mul_sq

example : ∫ x : ℝ, Real.sinc x ^ 2 = Real.pi :=
  integral_sinc_sq

#print axioms fourier_centeredUnitIntervalIndicator
#print axioms integrable_sinc_sq
#print axioms centeredUnitIntervalIndicator_memLp_one
#print axioms centeredUnitIntervalIndicator_memLp_two
#print axioms memLp_two_complex_sinc_pi
#print axioms integral_sinc_pi_mul_sq
#print axioms integral_sinc_sq

end SincSquareIntegral
end PrimeNumberTheorem
