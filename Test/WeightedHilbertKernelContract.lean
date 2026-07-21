import PrimeNumberTheorem.WeightedHilbertKernel

open Complex MeasureTheory
open scoped BigOperators ComplexConjugate

namespace PrimeNumberTheorem
namespace DirichletPolynomial

example (g : ℕ → ℝ → ℝ) (hg : ∀ j, Integrable (g j))
    (n : ℕ) (xi : ℝ) :
    (∑ j ∈ Finset.range (n + 1),
      fourierKernel (positiveKernelIncrement g j) xi) =
        fourierKernel (g n) xi :=
  sum_fourierKernel_positiveKernelIncrement hg n xi

example (N m n : ℕ) (hm : m < N) (hn : n < N)
    (c : ℕ → ℂ) (g : ℕ → ℝ → ℝ) (hg : ∀ j, Integrable (g j))
    (xi : ℝ) :
    (∑ j ∈ Finset.range N,
      conj (tailCoefficient j c m) * tailCoefficient j c n *
        fourierKernel (positiveKernelIncrement g j) xi) =
      conj (c m) * c n * fourierKernel (g (min m n)) xi :=
  sum_tailCoefficient_fourierKernel_increment hg hm hn xi

example (N : ℕ) (c : ℕ → ℂ) (omega : ℕ → ℝ)
    (g : ℕ → ℝ → ℝ) (hg : ∀ j, Integrable (g j)) :
    (∑ j ∈ Finset.range N,
      finiteFourierKernelForm (Finset.range N)
        (tailCoefficient j c) omega (positiveKernelIncrement g j)) =
      ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
        conj (c m) * c n *
          fourierKernel (g (min m n)) (omega n - omega m) :=
  sum_tail_fourierKernelForm_eq_min_kernel hg

example (N : ℕ) (c : ℕ → ℂ) (omega : ℕ → ℝ)
    (g : ℕ → ℝ → ℝ) (diagonal : ℕ → ℂ) (kappa : ℂ)
    (hzero : ∀ n ∈ Finset.range N,
      fourierKernel (g n) 0 = diagonal n)
    (hkernel : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N, m ≠ n →
      fourierKernel (g (min m n)) (omega n - omega m) =
        kappa / (omega n - omega m)) :
    (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
      conj (c m) * c n *
        fourierKernel (g (min m n)) (omega n - omega m)) =
      (∑ n ∈ Finset.range N, diagonal n * (‖c n‖ ^ 2 : ℂ)) +
        kappa * hilbertForm (Finset.range N) c omega :=
  sum_min_fourierKernel_eq_diagonal_add_mul_hilbert hzero hkernel

example (N : ℕ) (c : ℕ → ℂ) (omega : ℕ → ℝ)
    (g : ℕ → ℝ → ℝ) (hg : ∀ j, Integrable (g j))
    (hg0 : ∀ t, 0 ≤ g 0 t)
    (hmono : ∀ j t, g j t ≤ g (j + 1) t) :
    0 ≤ ((∑ j ∈ Finset.range N,
      finiteFourierKernelForm (Finset.range N)
        (tailCoefficient j c) omega (positiveKernelIncrement g j))).re :=
  sum_tail_fourierKernelForm_re_nonneg hg hg0 hmono

example (N : ℕ) (c : ℕ → ℂ) (omega weight : ℕ → ℝ)
    (g : ℕ → ℝ → ℝ) (C : ℝ)
    (hg : ∀ j, Integrable (g j)) (hg0 : ∀ t, 0 ≤ g 0 t)
    (hmono : ∀ j t, g j t ≤ g (j + 1) t)
    (hzero : ∀ n ∈ Finset.range N,
      fourierKernel (g n) 0 = ((2 * C * weight n : ℝ) : ℂ))
    (hkernel : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N, m ≠ n →
      fourierKernel (g (min m n)) (omega n - omega m) =
        (-2 * Complex.I) / (omega n - omega m)) :
    0 ≤ (((C * ∑ n ∈ Finset.range N,
        weight n * ‖c n‖ ^ 2 : ℝ) : ℂ) -
      Complex.I * hilbertForm (Finset.range N) c omega).re :=
  hilbertForm_minus_certificate_of_positive_kernelSequence
    hg hg0 hmono hzero hkernel

example (N : ℕ) (c : ℕ → ℂ) (omega weight : ℕ → ℝ)
    (g : ℕ → ℝ → ℝ) (C : ℝ)
    (hg : ∀ j, Integrable (g j)) (hg0 : ∀ t, 0 ≤ g 0 t)
    (hmono : ∀ j t, g j t ≤ g (j + 1) t)
    (hzero : ∀ n ∈ Finset.range N,
      fourierKernel (g n) 0 = ((2 * C * weight n : ℝ) : ℂ))
    (hkernel : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N, m ≠ n →
      fourierKernel (g (min m n)) (omega n - omega m) =
        (2 * Complex.I) / (omega n - omega m)) :
    0 ≤ (((C * ∑ n ∈ Finset.range N,
        weight n * ‖c n‖ ^ 2 : ℝ) : ℂ) +
      Complex.I * hilbertForm (Finset.range N) c omega).re :=
  hilbertForm_plus_certificate_of_positive_kernelSequence
    hg hg0 hmono hzero hkernel

example (N : ℕ) (c : ℕ → ℂ) (omega weight : ℕ → ℝ)
    (gMinus gPlus : ℕ → ℝ → ℝ) {a b C : ℝ}
    (hab : a ≤ b)
    (homega : Set.InjOn omega (Finset.range N : Set ℕ))
    (hweight : ∀ n ∈ Finset.range N, 0 ≤ weight n)
    (hgMinus : ∀ j, Integrable (gMinus j))
    (hgMinus0 : ∀ t, 0 ≤ gMinus 0 t)
    (hmonoMinus : ∀ j t, gMinus j t ≤ gMinus (j + 1) t)
    (hzeroMinus : ∀ n ∈ Finset.range N,
      fourierKernel (gMinus n) 0 = ((2 * C * weight n : ℝ) : ℂ))
    (hkernelMinus : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N, m ≠ n →
      fourierKernel (gMinus (min m n)) (omega n - omega m) =
        (-2 * Complex.I) / (omega n - omega m))
    (hgPlus : ∀ j, Integrable (gPlus j))
    (hgPlus0 : ∀ t, 0 ≤ gPlus 0 t)
    (hmonoPlus : ∀ j t, gPlus j t ≤ gPlus (j + 1) t)
    (hzeroPlus : ∀ n ∈ Finset.range N,
      fourierKernel (gPlus n) 0 = ((2 * C * weight n : ℝ) : ℂ))
    (hkernelPlus : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N, m ≠ n →
      fourierKernel (gPlus (min m n)) (omega n - omega m) =
        (2 * Complex.I) / (omega n - omega m)) :
    ∫ t in a..b, ‖finiteExponentialSum (Finset.range N) c omega t‖ ^ 2 ≤
      (b - a) * ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 +
        2 * C * ∑ n ∈ Finset.range N, weight n * ‖c n‖ ^ 2 :=
  finiteExponentialSum_meanSquare_le_of_positive_kernelSequences
    hab homega hweight
    hgMinus hgMinus0 hmonoMinus hzeroMinus hkernelMinus
    hgPlus hgPlus0 hmonoPlus hzeroPlus hkernelPlus

#print axioms sum_fourierKernel_positiveKernelIncrement
#print axioms sum_tailCoefficient_fourierKernel_increment
#print axioms sum_tail_fourierKernelForm_eq_min_kernel
#print axioms sum_min_fourierKernel_eq_diagonal_add_mul_hilbert
#print axioms sum_tail_fourierKernelForm_re_nonneg
#print axioms hilbertForm_minus_certificate_of_positive_kernelSequence
#print axioms hilbertForm_plus_certificate_of_positive_kernelSequence
#print axioms finiteExponentialSum_meanSquare_le_of_positive_kernelSequences

end DirichletPolynomial
end PrimeNumberTheorem
