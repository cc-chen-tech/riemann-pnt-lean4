import PrimeNumberTheorem.LocalSeparationKernel

open Complex MeasureTheory
open scoped BigOperators ComplexConjugate

namespace PrimeNumberTheorem
namespace DirichletPolynomial

noncomputable example {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (omega : ι → ℝ) (n : ι) : ℝ :=
  localFrequencySeparation S omega n

example {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {omega : ι → ℝ} {m n : ι}
    (hm : m ∈ S) (hmn : m ≠ n) :
    localFrequencySeparation S omega n ≤ |omega n - omega m| :=
  localFrequencySeparation_le_abs_sub hm hmn

example {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {omega : ι → ℝ} {n : ι}
    (hS : S.Nontrivial) (hn : n ∈ S)
    (homega : Set.InjOn omega (S : Set ι)) :
    0 < localFrequencySeparation S omega n :=
  localFrequencySeparation_pos hS hn homega

noncomputable example (delta : ℝ) : ℝ :=
  normalizedFourierDilationScale delta

example {delta : ℝ} (hdelta : 0 < delta) :
    0 < normalizedFourierDilationScale delta :=
  normalizedFourierDilationScale_pos hdelta

example (delta : ℝ) :
    2 * Real.pi * normalizedFourierDilationScale delta = delta :=
  two_pi_mul_normalizedFourierDilationScale delta

example {deltaNew deltaOld : ℝ} (horder : deltaNew ≤ deltaOld) :
    normalizedFourierDilationScale deltaNew ≤
      normalizedFourierDilationScale deltaOld :=
  normalizedFourierDilationScale_mono horder

example {g : ℝ → ℝ} {kappa : ℂ} {delta xi : ℝ}
    (hdelta : 0 < delta) (hgap : delta ≤ |xi|)
    (htail : ∀ eta : ℝ, 2 * Real.pi ≤ |eta| →
      fourierKernel g eta = kappa / eta) :
    fourierKernel
        (fun t => g (normalizedFourierDilationScale delta * t)) xi =
      kappa / xi :=
  fourierKernel_normalizedDilation_eq_const_div hdelta hgap htail

noncomputable example {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (omega : ι → ℝ) (n : ι) : ℝ :=
  localFourierDilationScale S omega n

example {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {omega : ι → ℝ} {n : ι}
    (hS : S.Nontrivial) (hn : n ∈ S)
    (homega : Set.InjOn omega (S : Set ι)) :
    0 < localFourierDilationScale S omega n :=
  localFourierDilationScale_pos hS hn homega

example {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {omega : ι → ℝ} {m n : ι}
    (hm : m ∈ S) (hmn : m ≠ n) :
    2 * Real.pi * localFourierDilationScale S omega n ≤
      |omega n - omega m| :=
  two_pi_mul_localFourierDilationScale_le_abs_sub hm hmn

example {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {omega : ι → ℝ} {g : ℝ → ℝ} {kappa : ℂ} {m n : ι}
    (hS : S.Nontrivial) (hm : m ∈ S) (hn : n ∈ S) (hmn : m ≠ n)
    (homega : Set.InjOn omega (S : Set ι))
    (htail : ∀ xi : ℝ, 2 * Real.pi ≤ |xi| →
      fourierKernel g xi = kappa / xi) :
    fourierKernel
        (fun t => g (localFourierDilationScale S omega n * t))
        (omega n - omega m) =
      kappa / (omega n - omega m) :=
  fourierKernel_localDilation_eq_const_div
    hS hm hn hmn homega htail

example {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {omega : ι → ℝ} {g : ℝ → ℝ} {m n : ι}
    (hS : S.Nontrivial) (hm : m ∈ S) (hn : n ∈ S) (hmn : m ≠ n)
    (homega : Set.InjOn omega (S : Set ι))
    (htail : ∀ xi : ℝ, 2 * Real.pi ≤ |xi| →
      fourierKernel g xi = (-2 * Complex.I) / xi) :
    fourierKernel
        (fun t => g (localFourierDilationScale S omega n * t))
        (omega n - omega m) =
      (-2 * Complex.I) / (omega n - omega m) :=
  fourierKernel_localDilation_eq_neg_two_I_div
    hS hm hn hmn homega htail

noncomputable example {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (omega : ι → ℝ) : List ℝ :=
  orderedLocalFrequencySeparations S omega

example {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (omega : ι → ℝ) :
    (orderedLocalFrequencySeparations S omega).Pairwise (· ≥ ·) :=
  orderedLocalFrequencySeparations_pairwise S omega

example {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (omega : ι → ℝ) (delta : ℝ) :
    delta ∈ orderedLocalFrequencySeparations S omega ↔
      ∃ n ∈ S, localFrequencySeparation S omega n = delta :=
  mem_orderedLocalFrequencySeparations

example {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {omega : ι → ℝ}
    (hS : S.Nontrivial) (homega : Set.InjOn omega (S : Set ι))
    {delta : ℝ} (hdelta : delta ∈ orderedLocalFrequencySeparations S omega) :
    0 < delta :=
  orderedLocalFrequencySeparations_pos hS homega hdelta

noncomputable example (g : ℝ → ℝ) (delta xi : ℝ) : ℂ :=
  scaledFourierProfile g delta xi

example (g : ℝ → ℝ) {delta xi : ℝ} (hdelta : 0 < delta) :
    fourierKernel (fun t => g (delta * t)) xi =
      scaledFourierProfile g delta xi :=
  fourierKernel_eq_scaledFourierProfile hdelta

example (g : ℝ → ℝ) (delta : ℕ → ℝ) (xi : ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N,
        (scaledFourierProfile g (delta (k + 1)) xi -
          scaledFourierProfile g (delta k) xi)) =
      scaledFourierProfile g (delta N) xi -
        scaledFourierProfile g (delta 0) xi :=
  scaledFourierProfile_telescope g delta xi N

noncomputable example {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (omega : ι → ℝ) (g : ℝ → ℝ) (xi : ℝ) : ℂ :=
  adjacentDifferenceSum (fun delta => scaledFourierProfile g delta xi)
    (orderedLocalFrequencySeparations S omega)

noncomputable example {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (omega : ι → ℝ) (g : ℝ → ℝ) (xi : ℝ) :
    adjacentDifferenceSum (fun delta => scaledFourierProfile g delta xi)
        (orderedLocalFrequencySeparations S omega) =
      endpointDifference (fun delta => scaledFourierProfile g delta xi)
        (orderedLocalFrequencySeparations S omega) :=
  orderedLocalFrequencySeparations_telescope S omega g xi

noncomputable example {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (c : ι → ℂ) (omega : ι → ℝ) (g : ℝ → ℝ) :
    adjacentDifferenceSum
        (fun delta => finiteFourierKernelForm S c omega
          (fun t => g (delta * t)))
        (orderedLocalFrequencySeparations S omega) =
      endpointDifference
        (fun delta => finiteFourierKernelForm S c omega
          (fun t => g (delta * t)))
        (orderedLocalFrequencySeparations S omega) :=
  orderedLocalFrequencySeparations_kernelForm_telescope S c omega g

example (N j : ℕ) : Finset ℕ :=
  suffixIndexSet N j

example {A : Type*} [AddCommMonoid A]
    (term : ℕ → ℕ → ℕ → A) (N : ℕ) :
    (∑ j ∈ Finset.range N, ∑ m ∈ suffixIndexSet N j,
        ∑ n ∈ suffixIndexSet N j, term j m n) =
      ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
        ∑ j ∈ Finset.range (min m n + 1), term j m n :=
  sum_suffix_double_eq_sum_min term N

example {R : Type*} [CommRing R]
    (a : ℕ → ℕ → R) (K : ℕ → ℕ → ℕ → R) (N : ℕ) :
    (∑ j ∈ Finset.range N, ∑ m ∈ suffixIndexSet N j,
        ∑ n ∈ suffixIndexSet N j,
          a m n * (K (j + 1) m n - K j m n)) =
      ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
        a m n * (K (min m n + 1) m n - K 0 m n) :=
  sum_suffix_mul_kernelIncrement_telescope a K N

example (c : ℕ → ℂ) (omega : ℕ → ℝ) (g : ℕ → ℝ → ℝ)
    (hg : ∀ j, Integrable (g j)) (N : ℕ) :
    (∑ j ∈ Finset.range N,
        finiteFourierKernelForm (suffixIndexSet N j) c omega
          (fun t => g (j + 1) t - g j t)) =
      ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
        conj (c m) * c n *
          (fourierKernel (g (min m n + 1)) (omega n - omega m) -
            fourierKernel (g 0) (omega n - omega m)) :=
  sum_suffix_finiteFourierKernelForm_sub_telescope c omega g hg N

example {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (c : ι → ℂ) (omega : ι → ℝ)
    (g : ℝ → ℝ) (index : ℕ → ι) (N : ℕ) :
    (∑ k ∈ Finset.range N,
        (finiteFourierKernelForm S c omega
            (fun t => g (localFrequencySeparation S omega (index (k + 1)) * t)) -
          finiteFourierKernelForm S c omega
            (fun t => g (localFrequencySeparation S omega (index k) * t)))) =
      finiteFourierKernelForm S c omega
          (fun t => g (localFrequencySeparation S omega (index N) * t)) -
        finiteFourierKernelForm S c omega
          (fun t => g (localFrequencySeparation S omega (index 0) * t)) :=
  finiteFourierKernelForm_localSeparation_telescope S c omega g index N

#print axioms localFrequencySeparation_le_abs_sub
#print axioms localFrequencySeparation_pos
#print axioms normalizedFourierDilationScale_pos
#print axioms two_pi_mul_normalizedFourierDilationScale
#print axioms normalizedFourierDilationScale_mono
#print axioms fourierKernel_normalizedDilation_eq_const_div
#print axioms localFourierDilationScale_pos
#print axioms two_pi_mul_localFourierDilationScale_le_abs_sub
#print axioms fourierKernel_localDilation_eq_const_div
#print axioms fourierKernel_localDilation_eq_neg_two_I_div
#print axioms orderedLocalFrequencySeparations_pairwise
#print axioms mem_orderedLocalFrequencySeparations
#print axioms orderedLocalFrequencySeparations_pos
#print axioms fourierKernel_eq_scaledFourierProfile
#print axioms scaledFourierProfile_telescope
#print axioms adjacentDifferenceSum_eq_endpointDifference
#print axioms orderedLocalFrequencySeparations_telescope
#print axioms orderedLocalFrequencySeparations_kernelForm_telescope
#print axioms sum_suffix_double_eq_sum_min
#print axioms sum_suffix_mul_kernelIncrement_telescope
#print axioms sum_suffix_finiteFourierKernelForm_sub_telescope
#print axioms finiteFourierKernelForm_localSeparation_telescope

end DirichletPolynomial
end PrimeNumberTheorem
