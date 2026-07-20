import PrimeNumberTheorem.PositiveFourierKernel

open Complex MeasureTheory
open scoped BigOperators ComplexConjugate

namespace PrimeNumberTheorem
namespace DirichletPolynomial

noncomputable example (g : ℝ → ℝ) (xi : ℝ) : ℂ :=
  fourierKernel g xi

example (g : ℝ → ℝ) (delta xi : ℝ) (hdelta : 0 < delta) :
    fourierKernel (fun t => g (delta * t)) xi =
      ((delta⁻¹ : ℝ) : ℂ) * fourierKernel g (xi / delta) :=
  fourierKernel_scale_pos hdelta

example (g h : ℝ → ℝ) (xi : ℝ)
    (hg : Integrable g) (hh : Integrable h) :
    fourierKernel (fun t => g t - h t) xi =
      fourierKernel g xi - fourierKernel h xi :=
  fourierKernel_sub hg hh

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

example {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (c : ι → ℂ) (omega : ι → ℝ) (g h : ℝ → ℝ)
    (hg : Integrable g) (hh : Integrable h) :
    finiteFourierKernelForm S c omega (fun t => g t - h t) =
      finiteFourierKernelForm S c omega g -
        finiteFourierKernelForm S c omega h :=
  finiteFourierKernelForm_sub hg hh

example {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (c : ι → ℂ) (omega : ι → ℝ) (g : ℝ → ℝ) (kappa : ℂ)
    (hkernel : ∀ m ∈ S, ∀ n ∈ S, m ≠ n →
      fourierKernel g (omega n - omega m) =
        kappa / (omega n - omega m)) :
    finiteFourierKernelForm S c omega g =
      fourierKernel g 0 * (∑ n ∈ S, (‖c n‖ ^ 2 : ℂ)) +
        kappa * hilbertForm S c omega :=
  finiteFourierKernelForm_eq_diagonal_add_mul_hilbert hkernel

example {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (c : ι → ℂ) (omega : ι → ℝ) (g : ℝ → ℝ) (C : ℝ)
    (hg : Integrable g) (hg0 : ∀ t, 0 ≤ g t)
    (hzero : fourierKernel g 0 = ((2 * C : ℝ) : ℂ))
    (hkernel : ∀ m ∈ S, ∀ n ∈ S, m ≠ n →
      fourierKernel g (omega n - omega m) =
        (-2 * Complex.I) / (omega n - omega m)) :
    0 ≤ (((C * ∑ n ∈ S, ‖c n‖ ^ 2 : ℝ) : ℂ) -
      Complex.I * hilbertForm S c omega).re :=
  hilbertForm_minus_certificate_of_positive_kernel hg hg0 hzero hkernel

example {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (c : ι → ℂ) (omega : ι → ℝ) (g : ℝ → ℝ) (C : ℝ)
    (hg : Integrable g) (hg0 : ∀ t, 0 ≤ g t)
    (hzero : fourierKernel g 0 = ((2 * C : ℝ) : ℂ))
    (hkernel : ∀ m ∈ S, ∀ n ∈ S, m ≠ n →
      fourierKernel g (omega n - omega m) =
        (2 * Complex.I) / (omega n - omega m)) :
    0 ≤ (((C * ∑ n ∈ S, ‖c n‖ ^ 2 : ℝ) : ℂ) +
      Complex.I * hilbertForm S c omega).re :=
  hilbertForm_plus_certificate_of_positive_kernel hg hg0 hzero hkernel

example {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (c : ι → ℂ) (omega : ι → ℝ) (g : ℝ → ℝ)
    (deltaSmall deltaLarge : ℝ)
    (hg : Integrable g) (hSmall : 0 < deltaSmall)
    (hLarge : 0 < deltaLarge)
    (hmono : ∀ t, g (deltaSmall * t) ≤ g (deltaLarge * t)) :
    0 ≤ (finiteFourierKernelForm S c omega
          (fun t => g (deltaLarge * t)) -
        finiteFourierKernelForm S c omega
          (fun t => g (deltaSmall * t))).re :=
  finiteFourierKernelForm_scaled_sub_re_nonneg hg hSmall hLarge hmono

example {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (c : ι → ℂ) (omega : ι → ℝ) (g : ℕ → ℝ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N,
        (finiteFourierKernelForm S c omega (g (k + 1)) -
          finiteFourierKernelForm S c omega (g k))) =
      finiteFourierKernelForm S c omega (g N) -
        finiteFourierKernelForm S c omega (g 0) :=
  finiteFourierKernelForm_telescope S c omega g N

#print axioms conj_mul_finiteExponentialSum_eq
#print axioms fourierKernel_scale_pos
#print axioms fourierKernel_sub
#print axioms finiteFourierKernelForm_eq_integral_normSq
#print axioms finiteFourierKernelForm_re_nonneg
#print axioms finiteFourierKernelForm_sub
#print axioms finiteFourierKernelForm_eq_diagonal_add_mul_hilbert
#print axioms hilbertForm_minus_certificate_of_positive_kernel
#print axioms hilbertForm_plus_certificate_of_positive_kernel
#print axioms finiteFourierKernelForm_scaled_sub_re_nonneg
#print axioms finiteFourierKernelForm_telescope

end DirichletPolynomial
end PrimeNumberTheorem
