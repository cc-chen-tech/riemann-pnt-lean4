import PrimeNumberTheorem.ScaledHilbertKernel

open Complex MeasureTheory
open scoped BigOperators ComplexConjugate

namespace PrimeNumberTheorem
namespace DirichletPolynomial

noncomputable section

example (g : ℝ → ℝ) (xi : ℝ) :
    fourierKernel (fun t => g (-t)) xi = fourierKernel g (-xi) :=
  fourierKernel_reflect g xi

example {C : ℝ} {kappa : ℂ}
    (profile : PositiveHilbertKernelProfile C kappa) :
    Integrable profile.kernel :=
  profile.integrable_kernel

example {C : ℝ} {kappa : ℂ}
    (profile : PositiveHilbertKernelProfile C kappa) :
    PositiveHilbertKernelProfile C (-kappa) :=
  profile.reflect

example (kernel : CarneiroLittmannKernel) :
    fourierKernel kernel.kernel 0 = (2 : ℂ) :=
  kernel.fourierKernel_zero

example (kernel : CarneiroLittmannKernel) :
    PositiveHilbertKernelProfile (2 * Real.pi) (-2 * Complex.I) :=
  kernel.normalizedProfile

example {C : ℝ} {kappa : ℂ}
    (profile : PositiveHilbertKernelProfile C kappa)
    (delta : ℕ → ℝ) (n : ℕ) (hdelta : 0 < delta n) :
    Integrable (scaledKernelSequence profile delta n) :=
  integrable_scaledKernelSequence profile hdelta

example {C : ℝ} {kappa : ℂ}
    (profile : PositiveHilbertKernelProfile C kappa)
    (delta : ℕ → ℝ) (n : ℕ) :
    0 ≤ scaledKernelSequence profile delta n 0 :=
  scaledKernelSequence_nonneg profile

example {C : ℝ} {kappa : ℂ}
    (profile : PositiveHilbertKernelProfile C kappa)
    (delta : ℕ → ℝ) (hdelta : ∀ n, 0 < delta n)
    (hanti : ∀ n, delta (n + 1) ≤ delta n) (n : ℕ) (t : ℝ) :
    scaledKernelSequence profile delta n t ≤
      scaledKernelSequence profile delta (n + 1) t :=
  scaledKernelSequence_mono profile hdelta hanti n t

example {C : ℝ} {kappa : ℂ}
    (profile : PositiveHilbertKernelProfile C kappa)
    (delta : ℕ → ℝ) (n : ℕ) (hdelta : 0 < delta n) :
    fourierKernel (scaledKernelSequence profile delta n) 0 =
      ((2 * C * (delta n)⁻¹ : ℝ) : ℂ) :=
  fourierKernel_scaledKernelSequence_zero profile hdelta

example {C : ℝ} {kappa : ℂ}
    (profile : PositiveHilbertKernelProfile C kappa)
    (delta : ℕ → ℝ) (n : ℕ) (xi : ℝ)
    (hdelta : 0 < delta n) (hlarge : delta n ≤ |xi|) :
    fourierKernel (scaledKernelSequence profile delta n) xi = kappa / xi :=
  fourierKernel_scaledKernelSequence_of_large_frequency
    profile hdelta hlarge

example {a b C : ℝ} (N : ℕ) (c : ℕ → ℂ) (omega delta : ℕ → ℝ)
    (profileMinus : PositiveHilbertKernelProfile C (-2 * Complex.I))
    (profilePlus : PositiveHilbertKernelProfile C (2 * Complex.I))
    (hab : a ≤ b)
    (hdelta : ∀ n, 0 < delta n)
    (hanti : ∀ n, delta (n + 1) ≤ delta n)
    (hlocal : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N, m ≠ n →
      delta (min m n) ≤ |omega n - omega m|) :
    ∫ t in a..b, ‖finiteExponentialSum (Finset.range N) c omega t‖ ^ 2 ≤
      (b - a) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 +
        2 * C * ∑ n ∈ Finset.range N, (delta n)⁻¹ * ‖c n‖ ^ 2 :=
  finiteExponentialSum_meanSquare_le_of_scaled_positive_kernels
    hab hdelta hanti hlocal profileMinus profilePlus

example {a b C : ℝ} (N : ℕ) (c : ℕ → ℂ) (omega delta : ℕ → ℝ)
    (profile : PositiveHilbertKernelProfile C (-2 * Complex.I))
    (hab : a ≤ b)
    (hdelta : ∀ n, 0 < delta n)
    (hanti : ∀ n, delta (n + 1) ≤ delta n)
    (hlocal : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N, m ≠ n →
      delta (min m n) ≤ |omega n - omega m|) :
    ∫ t in a..b, ‖finiteExponentialSum (Finset.range N) c omega t‖ ^ 2 ≤
      (b - a) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 +
        2 * C * ∑ n ∈ Finset.range N, (delta n)⁻¹ * ‖c n‖ ^ 2 :=
  finiteExponentialSum_meanSquare_le_of_scaled_positive_kernel
    hab hdelta hanti hlocal profile

example {a b : ℝ} (N : ℕ) (c : ℕ → ℂ) (omega delta : ℕ → ℝ)
    (kernel : CarneiroLittmannKernel) (hab : a ≤ b)
    (hdelta : ∀ n, 0 < delta n)
    (hanti : ∀ n, delta (n + 1) ≤ delta n)
    (hlocal : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N, m ≠ n →
      delta (min m n) ≤ |omega n - omega m|) :
    ∫ t in a..b, ‖finiteExponentialSum (Finset.range N) c omega t‖ ^ 2 ≤
      (b - a) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 +
        4 * Real.pi *
          ∑ n ∈ Finset.range N, (delta n)⁻¹ * ‖c n‖ ^ 2 :=
  finiteExponentialSum_meanSquare_le_of_carneiroLittmannKernel
    hab hdelta hanti hlocal kernel

#print axioms fourierKernel_reflect
#print axioms PositiveHilbertKernelProfile.reflect
#print axioms CarneiroLittmannKernel.normalizedProfile
#print axioms integrable_scaledKernelSequence
#print axioms scaledKernelSequence_mono
#print axioms fourierKernel_scaledKernelSequence_zero
#print axioms fourierKernel_scaledKernelSequence_of_large_frequency
#print axioms finiteExponentialSum_meanSquare_le_of_scaled_positive_kernels
#print axioms finiteExponentialSum_meanSquare_le_of_scaled_positive_kernel
#print axioms finiteExponentialSum_meanSquare_le_of_carneiroLittmannKernel

end
end DirichletPolynomial
end PrimeNumberTheorem
