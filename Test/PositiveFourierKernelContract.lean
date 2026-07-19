import PrimeNumberTheorem.PositiveFourierKernel

open Complex MeasureTheory
open scoped BigOperators ComplexConjugate

namespace PrimeNumberTheorem
namespace DirichletPolynomial

noncomputable example (g : ℝ → ℝ) (xi : ℝ) : ℂ :=
  fourierKernel g xi

example {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (c : ι → ℂ) (omega : ι → ℝ) (t : ℝ) :
    conj (finiteExponentialSum S c omega t) *
        finiteExponentialSum S c omega t =
      ∑ m ∈ S, ∑ n ∈ S,
        conj (c m) * c n *
          Complex.exp (Complex.I * ((omega n - omega m) * t)) :=
  conj_mul_finiteExponentialSum_eq S c omega t

example {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (c : ι → ℂ) (omega : ι → ℝ) (g : ℝ → ℝ)
    (hg : Integrable g) :
    finiteFourierKernelForm S c omega g =
      ((∫ t, g t * ‖finiteExponentialSum S c omega t‖ ^ 2 : ℝ) : ℂ) :=
  finiteFourierKernelForm_eq_integral_normSq hg

example {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (c : ι → ℂ) (omega : ι → ℝ) (g : ℝ → ℝ)
    (hg : Integrable g) (hg0 : ∀ t, 0 ≤ g t) :
    0 ≤ (finiteFourierKernelForm S c omega g).re :=
  finiteFourierKernelForm_re_nonneg hg hg0

#print axioms conj_mul_finiteExponentialSum_eq
#print axioms finiteFourierKernelForm_eq_integral_normSq
#print axioms finiteFourierKernelForm_re_nonneg

end DirichletPolynomial
end PrimeNumberTheorem
