import PrimeNumberTheorem.SincSquareFourier

open FourierTransform

namespace PrimeNumberTheorem
namespace SincSquareFourier

example (xi : ℝ) :
    𝓕 (fun x : ℝ => (Real.sinc (Real.pi * x) ^ 2 : ℂ)) xi =
      (max (1 - |xi|) 0 : ℝ) :=
  fourier_sinc_pi_mul_sq xi

example (xi : ℝ) :
    𝓕 (fun x : ℝ =>
      (Real.sinc (Real.pi * (x + 1)) ^ 2 : ℂ)) xi =
      Complex.exp ((2 * Real.pi * xi : ℝ) * Complex.I) *
        (max (1 - |xi|) 0 : ℝ) :=
  fourier_sinc_pi_add_one_sq xi

example {xi : ℝ} (hxi : 1 ≤ |xi|) :
    𝓕 (fun x : ℝ =>
      (Real.sinc (Real.pi * (x + 1)) ^ 2 : ℂ)) xi = 0 :=
  fourier_sinc_pi_add_one_sq_eq_zero hxi

#print axioms fourier_mul_convolution_eq_of_integrable
#print axioms centeredUnitIntervalIndicator_convolution_self
#print axioms fourier_sinc_pi_mul_sq
#print axioms fourier_sinc_pi_add_one_sq
#print axioms fourier_sinc_pi_add_one_sq_eq_zero

end SincSquareFourier
end PrimeNumberTheorem
