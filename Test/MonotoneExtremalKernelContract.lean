import PrimeNumberTheorem.MonotoneExtremalKernel

open Complex MeasureTheory
open scoped BigOperators ComplexConjugate

namespace PrimeNumberTheorem
namespace DirichletPolynomial

example (psi : ℝ → ℝ) : Prop :=
  MonotoneExtremalKernelCertificate psi

example {psi : ℝ → ℝ} (hpsi : MonotoneExtremalKernelCertificate psi) :
    Integrable psi :=
  hpsi.integrable

example {psi : ℝ → ℝ} (hpsi : MonotoneExtremalKernelCertificate psi) :
    fourierKernel psi 0 = 2 :=
  hpsi.fourier_zero

example (g : ℝ → ℝ) (xi : ℝ) :
    fourierKernel (fun t => g (-t)) xi = fourierKernel g (-xi) :=
  fourierKernel_reflect g xi

example {psi : ℝ → ℝ} (hpsi : MonotoneExtremalKernelCertificate psi) :
    Integrable (fun t => psi (-t)) :=
  hpsi.integrable_reflection

example {psi : ℝ → ℝ} (hpsi : MonotoneExtremalKernelCertificate psi) :
    fourierKernel (fun t => psi (-t)) 0 = 2 :=
  hpsi.fourier_reflection_zero

example {psi : ℝ → ℝ} (hpsi : MonotoneExtremalKernelCertificate psi)
    {xi : ℝ} (hxi : 2 * Real.pi ≤ |xi|) :
    fourierKernel (fun t => psi (-t)) xi =
      (2 * Complex.I) / xi :=
  hpsi.fourier_reflection_tail hxi

example {psi : ℝ → ℝ} (hpsi : MonotoneExtremalKernelCertificate psi)
    {delta : ℝ} (hdelta : 0 < delta) :
    Integrable (fun t => psi (delta * t)) :=
  hpsi.integrable_dilation hdelta

example {psi : ℝ → ℝ} (hpsi : MonotoneExtremalKernelCertificate psi)
    {delta : ℝ} (hdelta : 0 < delta) :
    fourierKernel (fun t => psi (delta * t)) 0 =
      (((2 / delta : ℝ)) : ℂ) :=
  hpsi.fourier_zero_dilation hdelta

example {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {omega : ι → ℝ} {psi : ℝ → ℝ} {m n : ι}
    (hpsi : MonotoneExtremalKernelCertificate psi)
    (hS : S.Nontrivial) (hm : m ∈ S) (hn : n ∈ S) (hmn : m ≠ n)
    (homega : Set.InjOn omega (S : Set ι)) :
    fourierKernel
        (fun t => psi (localFourierDilationScale S omega n * t))
        (omega n - omega m) =
      (-2 * Complex.I) / (omega n - omega m) :=
  hpsi.fourier_localDilation_offDiagonal hS hm hn hmn homega

example {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {omega : ι → ℝ} {psi : ℝ → ℝ} {m n : ι}
    (hpsi : MonotoneExtremalKernelCertificate psi)
    (hS : S.Nontrivial) (hm : m ∈ S) (hn : n ∈ S) (hmn : m ≠ n)
    (homega : Set.InjOn omega (S : Set ι)) :
    fourierKernel
        (fun t => psi (-(localFourierDilationScale S omega n * t)))
        (omega n - omega m) =
      (2 * Complex.I) / (omega n - omega m) :=
  hpsi.fourier_reflection_localDilation_offDiagonal
    hS hm hn hmn homega

example {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {omega : ι → ℝ} {psi : ℝ → ℝ} {n : ι}
    (hpsi : MonotoneExtremalKernelCertificate psi)
    (hS : S.Nontrivial) (hn : n ∈ S)
    (homega : Set.InjOn omega (S : Set ι)) :
    fourierKernel
        (fun t => psi (localFourierDilationScale S omega n * t)) 0 =
      (((4 * Real.pi / localFrequencySeparation S omega n : ℝ)) : ℂ) :=
  hpsi.fourier_localDilation_zero hS hn homega

example {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {c : ι → ℂ} {omega : ι → ℝ} {psi : ℝ → ℝ}
    (hpsi : MonotoneExtremalKernelCertificate psi)
    {deltaNew deltaOld : ℝ}
    (hNew : 0 < deltaNew) (hOld : 0 < deltaOld)
    (horder : deltaNew ≤ deltaOld) :
    0 ≤ (finiteFourierKernelForm S c omega
          (fun t => psi (deltaNew * t)) -
        finiteFourierKernelForm S c omega
          (fun t => psi (deltaOld * t))).re :=
  hpsi.kernelForm_dilation_increment_re_nonneg hNew hOld horder

example (psi : ℝ → ℝ) (q : ℕ → ℝ) (j : ℕ) : ℝ → ℝ :=
  cumulativeExtremalWeight psi q j

example {psi : ℝ → ℝ} (hpsi : MonotoneExtremalKernelCertificate psi)
    {q : ℕ → ℝ} (hq : ∀ j, 0 < q j) (j : ℕ) :
    Integrable (cumulativeExtremalWeight psi q j) :=
  hpsi.integrable_cumulativeExtremalWeight hq j

example {psi : ℝ → ℝ} (hpsi : MonotoneExtremalKernelCertificate psi)
    {q : ℕ → ℝ} (hq : ∀ j, 0 < q j)
    (hmono : ∀ j, q (j + 1) ≤ q j) (j : ℕ) (t : ℝ) :
    0 ≤ cumulativeExtremalWeight psi q (j + 1) t -
      cumulativeExtremalWeight psi q j t :=
  hpsi.cumulativeExtremalWeight_sub_nonneg hq hmono j t

example {psi : ℝ → ℝ} (hpsi : MonotoneExtremalKernelCertificate psi)
    (c : ℕ → ℂ) (omega : ℕ → ℝ) {q : ℕ → ℝ}
    (hq : ∀ j, 0 < q j) (hmono : ∀ j, q (j + 1) ≤ q j) (N : ℕ) :
    0 ≤ (∑ j ∈ Finset.range N,
      finiteFourierKernelForm (suffixIndexSet N j) c omega
        (fun t => cumulativeExtremalWeight psi q (j + 1) t -
          cumulativeExtremalWeight psi q j t)).re :=
  hpsi.sum_suffix_cumulativeExtremalWeight_re_nonneg c omega hq hmono N

example (psi : ℝ → ℝ) (q : ℕ → ℝ) (xi : ℝ) :
    fourierKernel (cumulativeExtremalWeight psi q 0) xi = 0 :=
  MonotoneExtremalKernelCertificate.fourierKernel_cumulativeExtremalWeight_zero
    psi q xi

example {psi : ℝ → ℝ} (hpsi : MonotoneExtremalKernelCertificate psi)
    {delta : ℕ → ℝ} (hdelta : ∀ j, 0 < delta j) (n : ℕ) :
    fourierKernel
        (cumulativeExtremalWeight psi
          (fun j => normalizedFourierDilationScale (delta j)) (n + 1)) 0 =
      (((4 * Real.pi / delta n : ℝ)) : ℂ) :=
  hpsi.fourier_cumulativeExtremalWeight_succ_zero hdelta n

example {psi : ℝ → ℝ} (hpsi : MonotoneExtremalKernelCertificate psi)
    {delta : ℕ → ℝ} (hdelta : ∀ j, 0 < delta j)
    {n : ℕ} {xi : ℝ} (hgap : delta n ≤ |xi|) :
    fourierKernel
        (cumulativeExtremalWeight psi
          (fun j => normalizedFourierDilationScale (delta j)) (n + 1)) xi =
      (-2 * Complex.I) / xi :=
  hpsi.fourier_cumulativeExtremalWeight_succ_offDiagonal hdelta hgap

example {psi : ℝ → ℝ} (hpsi : MonotoneExtremalKernelCertificate psi)
    {delta : ℕ → ℝ} (hdelta : ∀ j, 0 < delta j)
    (omega : ℕ → ℝ) {m n : ℕ}
    (hgap : m ≠ n → delta (min m n) ≤ |omega n - omega m|) :
    fourierKernel
        (cumulativeExtremalWeight psi
          (fun j => normalizedFourierDilationScale (delta j)) (min m n + 1))
        (omega n - omega m) -
      fourierKernel
        (cumulativeExtremalWeight psi
          (fun j => normalizedFourierDilationScale (delta j)) 0)
        (omega n - omega m) =
      if m = n then (((4 * Real.pi / delta n : ℝ)) : ℂ)
      else (-2 * Complex.I) / (omega n - omega m) :=
  hpsi.cumulativeExtremalWeight_endpointKernel_eq hdelta omega hgap

example {psi : ℝ → ℝ} (hpsi : MonotoneExtremalKernelCertificate psi)
    (c : ℕ → ℂ) (omega : ℕ → ℝ) {delta : ℕ → ℝ}
    (hdelta : ∀ j, 0 < delta j) (N : ℕ)
    (hgap : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N, m ≠ n →
      delta (min m n) ≤ |omega n - omega m|) :
    (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
      conj (c m) * c n *
        (fourierKernel
            (cumulativeExtremalWeight psi
              (fun j => normalizedFourierDilationScale (delta j))
              (min m n + 1)) (omega n - omega m) -
          fourierKernel
            (cumulativeExtremalWeight psi
              (fun j => normalizedFourierDilationScale (delta j)) 0)
              (omega n - omega m))) =
      (((4 * Real.pi *
        ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 / delta n : ℝ)) : ℂ) +
        (-2 * Complex.I) * hilbertForm (Finset.range N) c omega :=
  hpsi.sum_cumulativeEndpointKernel_eq_diagonal_add_hilbert
    c omega hdelta N hgap

example {psi : ℝ → ℝ} (hpsi : MonotoneExtremalKernelCertificate psi)
    (c : ℕ → ℂ) (omega : ℕ → ℝ) {delta : ℕ → ℝ}
    (hdelta : ∀ j, 0 < delta j)
    (hmono : ∀ j, delta (j + 1) ≤ delta j) (N : ℕ)
    (hgap : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N, m ≠ n →
      delta (min m n) ≤ |omega n - omega m|) :
    0 ≤ ((((2 * Real.pi *
        ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 / delta n : ℝ)) : ℂ) -
      Complex.I * hilbertForm (Finset.range N) c omega).re :=
  hpsi.weightedHilbert_minus_re_nonneg_of_ordered
    c omega hdelta hmono N hgap

example {psi : ℝ → ℝ} (hpsi : MonotoneExtremalKernelCertificate psi)
    (c : ℕ → ℂ) (omega : ℕ → ℝ) {delta : ℕ → ℝ}
    (hdelta : ∀ j, 0 < delta j)
    (hmono : ∀ j, delta (j + 1) ≤ delta j) (N : ℕ)
    (hgap : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N, m ≠ n →
      delta (min m n) ≤ |omega n - omega m|) :
    0 ≤ ((((2 * Real.pi *
        ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 / delta n : ℝ)) : ℂ) +
      Complex.I * hilbertForm (Finset.range N) c omega).re :=
  hpsi.weightedHilbert_plus_re_nonneg_of_ordered
    c omega hdelta hmono N hgap

example {psi : ℝ → ℝ} (hpsi : MonotoneExtremalKernelCertificate psi)
    (c : ℕ → ℂ) (omega : ℕ → ℝ) {delta : ℕ → ℝ}
    (hdelta : ∀ j, 0 < delta j)
    (hmono : ∀ j, delta (j + 1) ≤ delta j) (N : ℕ)
    (hgap : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N, m ≠ n →
      delta (min m n) ≤ |omega n - omega m|) :
    ‖hilbertForm (Finset.range N) c omega‖ ≤
      2 * Real.pi *
        ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 / delta n :=
  hpsi.hilbertForm_range_norm_le_two_pi_weighted_of_ordered
    c omega hdelta hmono N hgap

example {ι : Type*} [DecidableEq ι]
    {psi : ℝ → ℝ} (hpsi : MonotoneExtremalKernelCertificate psi)
    (index : ℕ → ι) (c : ι → ℂ) (omega : ι → ℝ) {delta : ℕ → ℝ}
    (hdelta : ∀ j, 0 < delta j)
    (hmono : ∀ j, delta (j + 1) ≤ delta j) (N : ℕ)
    (hinj : Set.InjOn index (Finset.range N : Set ℕ))
    (hgap : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N, m ≠ n →
      delta (min m n) ≤ |omega (index n) - omega (index m)|) :
    ‖hilbertForm ((Finset.range N).image index) c omega‖ ≤
      2 * Real.pi *
        ∑ n ∈ Finset.range N, ‖c (index n)‖ ^ 2 / delta n :=
  hpsi.hilbertForm_image_norm_le_two_pi_weighted_of_ordered
    index c omega hdelta hmono N hinj hgap

example {ι : Type*} [DecidableEq ι]
    {psi : ℝ → ℝ} (hpsi : MonotoneExtremalKernelCertificate psi)
    (index : ℕ → ι) (c : ι → ℂ) (omega : ι → ℝ) (N : ℕ)
    (hinj : Set.InjOn index (Finset.range N : Set ℕ))
    (hS : ((Finset.range N).image index).Nontrivial)
    (hmem : ∀ j, index j ∈ (Finset.range N).image index)
    (homega : Set.InjOn omega (((Finset.range N).image index : Finset ι) : Set ι))
    (hmono : ∀ j,
      localFrequencySeparation ((Finset.range N).image index) omega (index (j + 1)) ≤
        localFrequencySeparation ((Finset.range N).image index) omega (index j)) :
    ‖hilbertForm ((Finset.range N).image index) c omega‖ ≤
      2 * Real.pi *
        ∑ n ∈ (Finset.range N).image index,
          ‖c n‖ ^ 2 /
            localFrequencySeparation ((Finset.range N).image index) omega n :=
  hpsi.hilbertForm_image_norm_le_two_pi_localSeparation_of_ordered
    index c omega N hinj hS hmem homega hmono

example {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (omega : ι → ℝ) (hS : S.Nonempty) :
    ∃ index : ℕ → ι,
      Set.InjOn index (Finset.range S.card : Set ℕ) ∧
      (Finset.range S.card).image index = S ∧
      (∀ j, index j ∈ S) ∧
      ∀ j,
        localFrequencySeparation S omega (index (j + 1)) ≤
          localFrequencySeparation S omega (index j) :=
  exists_localSeparation_ordered_enumeration S omega hS

example {ι : Type*} [DecidableEq ι]
    {psi : ℝ → ℝ} (hpsi : MonotoneExtremalKernelCertificate psi)
    (S : Finset ι) (c : ι → ℂ) (omega : ι → ℝ)
    (hS : S.Nontrivial) (homega : Set.InjOn omega (S : Set ι)) :
    ‖hilbertForm S c omega‖ ≤
      2 * Real.pi *
        ∑ n ∈ S, ‖c n‖ ^ 2 / localFrequencySeparation S omega n :=
  hpsi.hilbertForm_norm_le_two_pi_localSeparation S c omega hS homega

#print axioms MonotoneExtremalKernelCertificate.integrable_dilation
#print axioms fourierKernel_reflect
#print axioms MonotoneExtremalKernelCertificate.integrable_reflection
#print axioms MonotoneExtremalKernelCertificate.fourier_reflection_zero
#print axioms MonotoneExtremalKernelCertificate.fourier_reflection_tail
#print axioms MonotoneExtremalKernelCertificate.fourier_zero_dilation
#print axioms MonotoneExtremalKernelCertificate.fourier_localDilation_offDiagonal
#print axioms MonotoneExtremalKernelCertificate.fourier_reflection_localDilation_offDiagonal
#print axioms MonotoneExtremalKernelCertificate.fourier_localDilation_zero
#print axioms MonotoneExtremalKernelCertificate.kernelForm_dilation_increment_re_nonneg
#print axioms MonotoneExtremalKernelCertificate.integrable_cumulativeExtremalWeight
#print axioms MonotoneExtremalKernelCertificate.cumulativeExtremalWeight_sub_nonneg
#print axioms MonotoneExtremalKernelCertificate.sum_suffix_cumulativeExtremalWeight_re_nonneg
#print axioms MonotoneExtremalKernelCertificate.fourierKernel_cumulativeExtremalWeight_zero
#print axioms MonotoneExtremalKernelCertificate.fourier_cumulativeExtremalWeight_succ_zero
#print axioms MonotoneExtremalKernelCertificate.fourier_cumulativeExtremalWeight_succ_offDiagonal
#print axioms MonotoneExtremalKernelCertificate.cumulativeExtremalWeight_endpointKernel_eq
#print axioms MonotoneExtremalKernelCertificate.sum_cumulativeEndpointKernel_eq_diagonal_add_hilbert
#print axioms MonotoneExtremalKernelCertificate.weightedHilbert_minus_re_nonneg_of_ordered
#print axioms MonotoneExtremalKernelCertificate.weightedHilbert_plus_re_nonneg_of_ordered
#print axioms MonotoneExtremalKernelCertificate.hilbertForm_range_norm_le_two_pi_weighted_of_ordered
#print axioms MonotoneExtremalKernelCertificate.hilbertForm_image_norm_le_two_pi_weighted_of_ordered
#print axioms MonotoneExtremalKernelCertificate.hilbertForm_image_norm_le_two_pi_localSeparation_of_ordered
#print axioms exists_localSeparation_ordered_enumeration
#print axioms MonotoneExtremalKernelCertificate.hilbertForm_norm_le_two_pi_localSeparation

end DirichletPolynomial
end PrimeNumberTheorem
