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

noncomputable example {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (omega : ι → ℝ) : List ℝ :=
  orderedLocalFrequencySeparations S omega

example {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (omega : ι → ℝ) :
    (orderedLocalFrequencySeparations S omega).Pairwise (· ≤ ·) :=
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
#print axioms orderedLocalFrequencySeparations_pairwise
#print axioms mem_orderedLocalFrequencySeparations
#print axioms orderedLocalFrequencySeparations_pos
#print axioms fourierKernel_eq_scaledFourierProfile
#print axioms scaledFourierProfile_telescope
#print axioms adjacentDifferenceSum_eq_endpointDifference
#print axioms orderedLocalFrequencySeparations_telescope
#print axioms orderedLocalFrequencySeparations_kernelForm_telescope
#print axioms finiteFourierKernelForm_localSeparation_telescope

end DirichletPolynomial
end PrimeNumberTheorem
