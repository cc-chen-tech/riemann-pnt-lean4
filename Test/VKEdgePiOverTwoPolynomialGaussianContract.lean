import PrimeNumberTheorem.VKEdgePiOverTwoPolynomialGaussian

open MeasureTheory Polynomial

open PrimeNumberTheorem VKEdgePiOverTwo

namespace PrimeNumberTheorem.VKEdgePiOverTwo

#check polynomialGaussianKernel
#check polynomialGaussianKernelDeriv
#check exists_polynomialGaussianKernel_sub_l1_bound
#check exists_polynomialGaussianKernelDeriv_l1_bound
#check polynomialGaussianKernel_X_mul

example (A : ℂ[X]) (hA : A.eval 0 = 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ m : ℝ, 1 ≤ m →
        (∫ t : ℝ,
          ‖polynomialGaussianKernel A m t -
            (normalizedGaussian m t : ℂ)‖) ≤
          C / Real.sqrt m :=
  exists_polynomialGaussianKernel_sub_l1_bound A hA

example (A : ℂ[X]) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ m : ℝ, 1 ≤ m →
        (∫ t : ℝ, ‖polynomialGaussianKernelDeriv A m t‖) ≤
          C / Real.sqrt m :=
  exists_polynomialGaussianKernelDeriv_l1_bound A

example (A : ℂ[X]) (m t : ℝ) :
    polynomialGaussianKernel (X * A) m t =
      polynomialGaussianKernelDeriv A m t :=
  polynomialGaussianKernel_X_mul A m t

end PrimeNumberTheorem.VKEdgePiOverTwo
