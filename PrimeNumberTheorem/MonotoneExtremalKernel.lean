import PrimeNumberTheorem.LocalSeparationKernel

open Complex MeasureTheory
open scoped BigOperators ComplexConjugate

namespace PrimeNumberTheorem
namespace DirichletPolynomial

/-- Reflection of a real weight negates the frequency in the Fourier kernel. -/
theorem fourierKernel_reflect (g : ℝ → ℝ) (xi : ℝ) :
    fourierKernel (fun t => g (-t)) xi = fourierKernel g (-xi) := by
  let F : ℝ → ℂ := fun y =>
    (g y : ℂ) * Complex.exp
      (Complex.I * (((-xi) * y : ℝ) : ℂ))
  unfold fourierKernel
  calc
    (∫ t, (g (-t) : ℂ) * Complex.exp (Complex.I * (xi * t))) =
        ∫ t, F ((-1 : ℝ) * t) := by
      congr 1
      funext t
      simp only [F, neg_mul, one_mul]
      congr 2
      push_cast
      ring
    _ = ∫ y, F y := by
      simpa using (Measure.integral_comp_mul_left F (-1))
    _ = ∫ y, (g y : ℂ) * Complex.exp
          (Complex.I * (((-xi : ℝ) : ℂ) * (y : ℂ))) := by
      congr 1
      funext y
      simp only [F]
      congr 2
      push_cast
      ring

/-- The analytic properties of the monotone Beurling--Selberg error profile
needed by the Fourier proof of the weighted Hilbert--Montgomery--Vaughan
inequality.  With the convention used by `fourierKernel`, the profile
`M - sgn` from Carneiro--Littmann has this normalization. -/
structure MonotoneExtremalKernelCertificate (psi : ℝ → ℝ) : Prop where
  integrable : Integrable psi
  nonnegative : ∀ t, 0 ≤ psi t
  fourier_zero : fourierKernel psi 0 = 2
  fourier_tail : ∀ xi : ℝ, 2 * Real.pi ≤ |xi| →
    fourierKernel psi xi = (-2 * Complex.I) / xi
  dilation_antitone : ∀ {deltaNew deltaOld : ℝ},
    0 < deltaNew → deltaNew ≤ deltaOld → ∀ t,
      psi (deltaOld * t) ≤ psi (deltaNew * t)

/-- The cumulative scaled weight used at each stage of the ordered suffix
argument.  Stage zero is the zero weight; stage `j + 1` uses scale `q j`. -/
def cumulativeExtremalWeight (psi : ℝ → ℝ) (q : ℕ → ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 0
  | j + 1, t => psi (q j * t)

namespace MonotoneExtremalKernelCertificate

theorem integrable_reflection {psi : ℝ → ℝ}
    (hpsi : MonotoneExtremalKernelCertificate psi) :
    Integrable (fun t => psi (-t)) := by
  simpa only [neg_one_mul] using
    hpsi.integrable.comp_mul_left' (by norm_num : (-1 : ℝ) ≠ 0)

theorem fourier_reflection_zero {psi : ℝ → ℝ}
    (hpsi : MonotoneExtremalKernelCertificate psi) :
    fourierKernel (fun t => psi (-t)) 0 = 2 := by
  rw [fourierKernel_reflect, neg_zero, hpsi.fourier_zero]

theorem fourier_reflection_tail {psi : ℝ → ℝ}
    (hpsi : MonotoneExtremalKernelCertificate psi)
    {xi : ℝ} (hxi : 2 * Real.pi ≤ |xi|) :
    fourierKernel (fun t => psi (-t)) xi =
      (2 * Complex.I) / xi := by
  have hneg : 2 * Real.pi ≤ |-xi| := by simpa using hxi
  rw [fourierKernel_reflect, hpsi.fourier_tail (-xi) hneg]
  push_cast
  ring

theorem integrable_dilation {psi : ℝ → ℝ}
    (hpsi : MonotoneExtremalKernelCertificate psi)
    {delta : ℝ} (hdelta : 0 < delta) :
    Integrable (fun t => psi (delta * t)) :=
  hpsi.integrable.comp_mul_left' hdelta.ne'

theorem fourier_zero_dilation {psi : ℝ → ℝ}
    (hpsi : MonotoneExtremalKernelCertificate psi)
    {delta : ℝ} (hdelta : 0 < delta) :
    fourierKernel (fun t => psi (delta * t)) 0 =
      (((2 / delta : ℝ)) : ℂ) := by
  rw [fourierKernel_scale_pos hdelta, zero_div, hpsi.fourier_zero]
  push_cast
  field_simp [hdelta.ne']

theorem fourier_localDilation_offDiagonal
    {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {omega : ι → ℝ} {psi : ℝ → ℝ} {m n : ι}
    (hpsi : MonotoneExtremalKernelCertificate psi)
    (hS : S.Nontrivial) (hm : m ∈ S) (hn : n ∈ S) (hmn : m ≠ n)
    (homega : Set.InjOn omega (S : Set ι)) :
    fourierKernel
        (fun t => psi (localFourierDilationScale S omega n * t))
        (omega n - omega m) =
      (-2 * Complex.I) / (omega n - omega m) :=
  fourierKernel_localDilation_eq_neg_two_I_div
    hS hm hn hmn homega hpsi.fourier_tail

theorem fourier_reflection_localDilation_offDiagonal
    {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {omega : ι → ℝ} {psi : ℝ → ℝ} {m n : ι}
    (hpsi : MonotoneExtremalKernelCertificate psi)
    (hS : S.Nontrivial) (hm : m ∈ S) (hn : n ∈ S) (hmn : m ≠ n)
    (homega : Set.InjOn omega (S : Set ι)) :
    fourierKernel
        (fun t => psi (-(localFourierDilationScale S omega n * t)))
        (omega n - omega m) =
      (2 * Complex.I) / (omega n - omega m) := by
  exact fourierKernel_localDilation_eq_const_div
    (g := fun u => psi (-u)) (kappa := 2 * Complex.I)
    hS hm hn hmn homega (fun xi hxi =>
      hpsi.fourier_reflection_tail hxi)

theorem fourier_localDilation_zero
    {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {omega : ι → ℝ} {psi : ℝ → ℝ} {n : ι}
    (hpsi : MonotoneExtremalKernelCertificate psi)
    (hS : S.Nontrivial) (hn : n ∈ S)
    (homega : Set.InjOn omega (S : Set ι)) :
    fourierKernel
        (fun t => psi (localFourierDilationScale S omega n * t)) 0 =
      (((4 * Real.pi / localFrequencySeparation S omega n : ℝ)) : ℂ) := by
  have hsep := localFrequencySeparation_pos hS hn homega
  have hscale := localFourierDilationScale_pos hS hn homega
  rw [hpsi.fourier_zero_dilation hscale]
  unfold localFourierDilationScale normalizedFourierDilationScale
  push_cast
  field_simp [hsep.ne', Real.pi_ne_zero]
  ring

theorem kernelForm_dilation_increment_re_nonneg
    {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {c : ι → ℂ} {omega : ι → ℝ} {psi : ℝ → ℝ}
    (hpsi : MonotoneExtremalKernelCertificate psi)
    {deltaNew deltaOld : ℝ}
    (hNew : 0 < deltaNew) (hOld : 0 < deltaOld)
    (horder : deltaNew ≤ deltaOld) :
    0 ≤ (finiteFourierKernelForm S c omega
          (fun t => psi (deltaNew * t)) -
        finiteFourierKernelForm S c omega
          (fun t => psi (deltaOld * t))).re := by
  exact finiteFourierKernelForm_scaled_sub_re_nonneg
    hpsi.integrable hOld hNew
    (hpsi.dilation_antitone hNew horder)

theorem integrable_cumulativeExtremalWeight {psi : ℝ → ℝ}
    (hpsi : MonotoneExtremalKernelCertificate psi)
    {q : ℕ → ℝ} (hq : ∀ j, 0 < q j) (j : ℕ) :
    Integrable (cumulativeExtremalWeight psi q j) := by
  cases j with
  | zero => exact MeasureTheory.integrable_zero ℝ ℝ volume
  | succ j =>
      simpa only [cumulativeExtremalWeight] using
        hpsi.integrable_dilation (hq j)

theorem cumulativeExtremalWeight_sub_nonneg {psi : ℝ → ℝ}
    (hpsi : MonotoneExtremalKernelCertificate psi)
    {q : ℕ → ℝ} (hq : ∀ j, 0 < q j)
    (hmono : ∀ j, q (j + 1) ≤ q j) (j : ℕ) (t : ℝ) :
    0 ≤ cumulativeExtremalWeight psi q (j + 1) t -
      cumulativeExtremalWeight psi q j t := by
  cases j with
  | zero =>
      simpa only [cumulativeExtremalWeight, sub_zero] using
        hpsi.nonnegative (q 0 * t)
  | succ j =>
      apply sub_nonneg.mpr
      simpa only [cumulativeExtremalWeight] using
        hpsi.dilation_antitone (hq (j + 1)) (hmono j) t

theorem sum_suffix_cumulativeExtremalWeight_re_nonneg
    {psi : ℝ → ℝ} (hpsi : MonotoneExtremalKernelCertificate psi)
    (c : ℕ → ℂ) (omega : ℕ → ℝ) {q : ℕ → ℝ}
    (hq : ∀ j, 0 < q j) (hmono : ∀ j, q (j + 1) ≤ q j) (N : ℕ) :
    0 ≤ (∑ j ∈ Finset.range N,
      finiteFourierKernelForm (suffixIndexSet N j) c omega
        (fun t => cumulativeExtremalWeight psi q (j + 1) t -
          cumulativeExtremalWeight psi q j t)).re := by
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro j hj
  exact finiteFourierKernelForm_re_nonneg
    ((hpsi.integrable_cumulativeExtremalWeight hq (j + 1)).sub
      (hpsi.integrable_cumulativeExtremalWeight hq j))
    (hpsi.cumulativeExtremalWeight_sub_nonneg hq hmono j)

theorem fourierKernel_cumulativeExtremalWeight_zero
    (psi : ℝ → ℝ) (q : ℕ → ℝ) (xi : ℝ) :
    fourierKernel (cumulativeExtremalWeight psi q 0) xi = 0 := by
  simp [cumulativeExtremalWeight, fourierKernel]

theorem fourier_cumulativeExtremalWeight_succ_zero
    {psi : ℝ → ℝ} (hpsi : MonotoneExtremalKernelCertificate psi)
    {delta : ℕ → ℝ} (hdelta : ∀ j, 0 < delta j) (n : ℕ) :
    fourierKernel
        (cumulativeExtremalWeight psi
          (fun j => normalizedFourierDilationScale (delta j)) (n + 1)) 0 =
      (((4 * Real.pi / delta n : ℝ)) : ℂ) := by
  change fourierKernel
    (fun t => psi (normalizedFourierDilationScale (delta n) * t)) 0 = _
  have hq := normalizedFourierDilationScale_pos (hdelta n)
  rw [hpsi.fourier_zero_dilation hq]
  unfold normalizedFourierDilationScale
  push_cast
  field_simp [(hdelta n).ne', Real.pi_ne_zero]
  ring

theorem fourier_cumulativeExtremalWeight_succ_offDiagonal
    {psi : ℝ → ℝ} (hpsi : MonotoneExtremalKernelCertificate psi)
    {delta : ℕ → ℝ} (hdelta : ∀ j, 0 < delta j)
    {n : ℕ} {xi : ℝ} (hgap : delta n ≤ |xi|) :
    fourierKernel
        (cumulativeExtremalWeight psi
          (fun j => normalizedFourierDilationScale (delta j)) (n + 1)) xi =
      (-2 * Complex.I) / xi := by
  change fourierKernel
    (fun t => psi (normalizedFourierDilationScale (delta n) * t)) xi = _
  exact fourierKernel_normalizedDilation_eq_const_div
    (hdelta n) hgap hpsi.fourier_tail

theorem cumulativeExtremalWeight_endpointKernel_eq
    {psi : ℝ → ℝ} (hpsi : MonotoneExtremalKernelCertificate psi)
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
      else (-2 * Complex.I) / (omega n - omega m) := by
  rw [fourierKernel_cumulativeExtremalWeight_zero, sub_zero]
  by_cases hmn : m = n
  · subst n
    rw [if_pos rfl, min_self, sub_self]
    exact hpsi.fourier_cumulativeExtremalWeight_succ_zero hdelta m
  · rw [if_neg hmn]
    simpa only [Complex.ofReal_sub] using
      hpsi.fourier_cumulativeExtremalWeight_succ_offDiagonal
        hdelta (hgap hmn)

theorem sum_cumulativeEndpointKernel_eq_diagonal_add_hilbert
    {psi : ℝ → ℝ} (hpsi : MonotoneExtremalKernelCertificate psi)
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
        (-2 * Complex.I) * hilbertForm (Finset.range N) c omega := by
  have hpair : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N,
      conj (c m) * c n *
        (fourierKernel
            (cumulativeExtremalWeight psi
              (fun j => normalizedFourierDilationScale (delta j))
              (min m n + 1)) (omega n - omega m) -
          fourierKernel
            (cumulativeExtremalWeight psi
              (fun j => normalizedFourierDilationScale (delta j)) 0)
              (omega n - omega m)) =
        if m = n then
          (((4 * Real.pi * (‖c m‖ ^ 2 / delta m) : ℝ)) : ℂ)
        else (-2 * Complex.I) *
          (conj (c m) * c n / (omega n - omega m)) := by
    intro m hm n hn
    rw [hpsi.cumulativeExtremalWeight_endpointKernel_eq hdelta omega
      (hgap m hm n hn)]
    by_cases hmn : m = n
    · subst n
      simp only [if_true]
      rw [← Complex.normSq_eq_norm_sq]
      push_cast
      rw [Complex.normSq_eq_conj_mul_self]
      ring
    · simp only [if_neg hmn]
      ring
  have hdiag :
      (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
        if m = n then
          (((4 * Real.pi * (‖c m‖ ^ 2 / delta m) : ℝ)) : ℂ)
        else 0) =
        (((4 * Real.pi *
          ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 / delta n : ℝ)) : ℂ) := by
    calc
      (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          if m = n then
            (((4 * Real.pi * (‖c m‖ ^ 2 / delta m) : ℝ)) : ℂ)
          else 0) =
          ∑ m ∈ Finset.range N,
            (((4 * Real.pi * (‖c m‖ ^ 2 / delta m) : ℝ)) : ℂ) := by
        apply Finset.sum_congr rfl
        intro m hm
        simp [hm]
      _ = (((4 * Real.pi *
          ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 / delta n : ℝ)) : ℂ) := by
        push_cast
        rw [Finset.mul_sum]
  have hoff :
      (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
        if m = n then 0
        else (-2 * Complex.I) *
          (conj (c m) * c n / (omega n - omega m))) =
        (-2 * Complex.I) * hilbertForm (Finset.range N) c omega := by
    unfold hilbertForm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hmn : m = n <;> simp [hmn]
  calc
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
        ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          if m = n then
            (((4 * Real.pi * (‖c m‖ ^ 2 / delta m) : ℝ)) : ℂ)
          else (-2 * Complex.I) *
            (conj (c m) * c n / (omega n - omega m)) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      exact hpair m hm n hn
    _ = (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          if m = n then
            (((4 * Real.pi * (‖c m‖ ^ 2 / delta m) : ℝ)) : ℂ)
          else 0) +
        (∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          if m = n then 0
          else (-2 * Complex.I) *
            (conj (c m) * c n / (omega n - omega m))) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro m hm
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hmn : m = n <;> simp [hmn]
    _ = (((4 * Real.pi *
          ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 / delta n : ℝ)) : ℂ) +
        (-2 * Complex.I) * hilbertForm (Finset.range N) c omega := by
      rw [hdiag, hoff]

theorem weightedHilbert_minus_re_nonneg_of_ordered
    {psi : ℝ → ℝ} (hpsi : MonotoneExtremalKernelCertificate psi)
    (c : ℕ → ℂ) (omega : ℕ → ℝ) {delta : ℕ → ℝ}
    (hdelta : ∀ j, 0 < delta j)
    (hmono : ∀ j, delta (j + 1) ≤ delta j) (N : ℕ)
    (hgap : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N, m ≠ n →
      delta (min m n) ≤ |omega n - omega m|) :
    0 ≤ ((((2 * Real.pi *
        ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 / delta n : ℝ)) : ℂ) -
      Complex.I * hilbertForm (Finset.range N) c omega).re := by
  let q : ℕ → ℝ := fun j => normalizedFourierDilationScale (delta j)
  have hq : ∀ j, 0 < q j := fun j =>
    normalizedFourierDilationScale_pos (hdelta j)
  have hqmono : ∀ j, q (j + 1) ≤ q j := fun j =>
    normalizedFourierDilationScale_mono (hmono j)
  have hnonneg := hpsi.sum_suffix_cumulativeExtremalWeight_re_nonneg
    c omega hq hqmono N
  have htelescope := sum_suffix_finiteFourierKernelForm_sub_telescope
    c omega (cumulativeExtremalWeight psi q)
      (hpsi.integrable_cumulativeExtremalWeight hq) N
  rw [htelescope] at hnonneg
  have hendpoint := hpsi.sum_cumulativeEndpointKernel_eq_diagonal_add_hilbert
    c omega hdelta N hgap
  dsimp [q] at hnonneg
  rw [hendpoint] at hnonneg
  have hfactor :
      (((4 * Real.pi *
          ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 / delta n : ℝ)) : ℂ) +
        (-2 * Complex.I) * hilbertForm (Finset.range N) c omega =
      (2 : ℂ) *
        ((((2 * Real.pi *
          ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 / delta n : ℝ)) : ℂ) -
          Complex.I * hilbertForm (Finset.range N) c omega) := by
    push_cast
    ring
  rw [hfactor] at hnonneg
  simpa using hnonneg

theorem weightedHilbert_plus_re_nonneg_of_ordered
    {psi : ℝ → ℝ} (hpsi : MonotoneExtremalKernelCertificate psi)
    (c : ℕ → ℂ) (omega : ℕ → ℝ) {delta : ℕ → ℝ}
    (hdelta : ∀ j, 0 < delta j)
    (hmono : ∀ j, delta (j + 1) ≤ delta j) (N : ℕ)
    (hgap : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N, m ≠ n →
      delta (min m n) ≤ |omega n - omega m|) :
    0 ≤ ((((2 * Real.pi *
        ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 / delta n : ℝ)) : ℂ) +
      Complex.I * hilbertForm (Finset.range N) c omega).re := by
  have hgapNeg : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N, m ≠ n →
      delta (min m n) ≤ |(-omega n) - (-omega m)| := by
    intro m hm n hn hmn
    calc
      delta (min m n) ≤ |omega n - omega m| := hgap m hm n hn hmn
      _ = |(-omega n) - (-omega m)| := by
        rw [show (-omega n) - (-omega m) = -(omega n - omega m) by ring,
          abs_neg]
  have hminus := hpsi.weightedHilbert_minus_re_nonneg_of_ordered
    c (fun n => -omega n) hdelta hmono N hgapNeg
  rw [hilbertForm_neg_frequency] at hminus
  simpa only [mul_neg, sub_neg_eq_add] using hminus

/-- The weighted Hilbert--Montgomery--Vaughan inequality for an already
ordered finite frequency family.  The remaining finite combinatorial step is
to permute an arbitrary family so that its local gaps form `delta`. -/
theorem hilbertForm_range_norm_le_two_pi_weighted_of_ordered
    {psi : ℝ → ℝ} (hpsi : MonotoneExtremalKernelCertificate psi)
    (c : ℕ → ℂ) (omega : ℕ → ℝ) {delta : ℕ → ℝ}
    (hdelta : ∀ j, 0 < delta j)
    (hmono : ∀ j, delta (j + 1) ≤ delta j) (N : ℕ)
    (hgap : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N, m ≠ n →
      delta (min m n) ≤ |omega n - omega m|) :
    ‖hilbertForm (Finset.range N) c omega‖ ≤
      2 * Real.pi *
        ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 / delta n := by
  exact norm_hilbertForm_le_of_two_sided_re_nonneg
    (hpsi.weightedHilbert_plus_re_nonneg_of_ordered
      c omega hdelta hmono N hgap)
    (hpsi.weightedHilbert_minus_re_nonneg_of_ordered
      c omega hdelta hmono N hgap)

/-- Transport the ordered `range N` inequality through an injective finite
reindexing into an arbitrary target index type. -/
theorem hilbertForm_image_norm_le_two_pi_weighted_of_ordered
    {ι : Type*} [DecidableEq ι]
    {psi : ℝ → ℝ} (hpsi : MonotoneExtremalKernelCertificate psi)
    (index : ℕ → ι) (c : ι → ℂ) (omega : ι → ℝ) {delta : ℕ → ℝ}
    (hdelta : ∀ j, 0 < delta j)
    (hmono : ∀ j, delta (j + 1) ≤ delta j) (N : ℕ)
    (hinj : Set.InjOn index (Finset.range N : Set ℕ))
    (hgap : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N, m ≠ n →
      delta (min m n) ≤ |omega (index n) - omega (index m)|) :
    ‖hilbertForm ((Finset.range N).image index) c omega‖ ≤
      2 * Real.pi *
        ∑ n ∈ Finset.range N, ‖c (index n)‖ ^ 2 / delta n := by
  rw [hilbertForm_image_eq (Finset.range N) index hinj]
  exact hpsi.hilbertForm_range_norm_le_two_pi_weighted_of_ordered
    (fun n => c (index n)) (fun n => omega (index n))
    hdelta hmono N hgap

/-- The transported inequality with `delta` specialized to the actual local
frequency separations of the image family.  The enumeration is assumed to be
ordered by these separations; constructing such an enumeration is a separate
finite sorting step. -/
theorem hilbertForm_image_norm_le_two_pi_localSeparation_of_ordered
    {ι : Type*} [DecidableEq ι]
    {psi : ℝ → ℝ} (hpsi : MonotoneExtremalKernelCertificate psi)
    (index : ℕ → ι) (c : ι → ℂ) (omega : ι → ℝ) (N : ℕ)
    (hinj : Set.InjOn index (Finset.range N : Set ℕ))
    (hS : ((Finset.range N).image index).Nontrivial)
    (hmem : ∀ j, index j ∈ (Finset.range N).image index)
    (homega : Set.InjOn omega
      (((Finset.range N).image index : Finset ι) : Set ι))
    (hmono : ∀ j,
      localFrequencySeparation ((Finset.range N).image index) omega (index (j + 1)) ≤
        localFrequencySeparation ((Finset.range N).image index) omega (index j)) :
    ‖hilbertForm ((Finset.range N).image index) c omega‖ ≤
      2 * Real.pi *
        ∑ n ∈ (Finset.range N).image index,
          ‖c n‖ ^ 2 /
            localFrequencySeparation ((Finset.range N).image index) omega n := by
  let S : Finset ι := (Finset.range N).image index
  let delta : ℕ → ℝ := fun j => localFrequencySeparation S omega (index j)
  have hdelta : ∀ j, 0 < delta j := fun j =>
    localFrequencySeparation_pos hS (hmem j) homega
  have hgap : ∀ m ∈ Finset.range N, ∀ n ∈ Finset.range N, m ≠ n →
      delta (min m n) ≤ |omega (index n) - omega (index m)| := by
    intro m hm n hn hmn
    have hindexNe : index m ≠ index n := fun h => hmn (hinj hm hn h)
    rcases le_total m n with hmnOrder | hnmOrder
    · rw [min_eq_left hmnOrder]
      have hsep := localFrequencySeparation_le_abs_sub
        (S := S) (omega := omega) (m := index n) (n := index m)
        (hmem n) hindexNe.symm
      simpa only [abs_sub_comm] using hsep
    · rw [min_eq_right hnmOrder]
      exact localFrequencySeparation_le_abs_sub
        (S := S) (omega := omega) (m := index m) (n := index n)
        (hmem m) hindexNe
  have hbound := hpsi.hilbertForm_image_norm_le_two_pi_weighted_of_ordered
    index c omega hdelta hmono N hinj hgap
  dsimp [delta, S] at hbound
  calc
    ‖hilbertForm ((Finset.range N).image index) c omega‖ ≤
        2 * Real.pi *
          ∑ n ∈ Finset.range N, ‖c (index n)‖ ^ 2 /
            localFrequencySeparation ((Finset.range N).image index) omega (index n) :=
      hbound
    _ = 2 * Real.pi *
        ∑ n ∈ (Finset.range N).image index,
          ‖c n‖ ^ 2 /
            localFrequencySeparation ((Finset.range N).image index) omega n := by
      congr 1
      rw [Finset.sum_image hinj]

/-- The weighted Hilbert--Montgomery--Vaughan inequality for an arbitrary
nontrivial finite family of distinct real frequencies.  The required ordering
is supplied internally by sorting the indices by decreasing local separation. -/
theorem hilbertForm_norm_le_two_pi_localSeparation
    {ι : Type*} [DecidableEq ι]
    {psi : ℝ → ℝ} (hpsi : MonotoneExtremalKernelCertificate psi)
    (S : Finset ι) (c : ι → ℂ) (omega : ι → ℝ)
    (hS : S.Nontrivial) (homega : Set.InjOn omega (S : Set ι)) :
    ‖hilbertForm S c omega‖ ≤
      2 * Real.pi *
        ∑ n ∈ S, ‖c n‖ ^ 2 / localFrequencySeparation S omega n := by
  rcases exists_localSeparation_ordered_enumeration S omega hS.nonempty with
    ⟨index, hinj, himage, hmem, hmono⟩
  have himageNontrivial : ((Finset.range S.card).image index).Nontrivial := by
    rw [himage]
    exact hS
  have hmemImage : ∀ j, index j ∈ (Finset.range S.card).image index := by
    rw [himage]
    exact hmem
  have homegaImage : Set.InjOn omega
      ((((Finset.range S.card).image index : Finset ι)) : Set ι) := by
    rw [himage]
    exact homega
  have hmonoImage : ∀ j,
      localFrequencySeparation ((Finset.range S.card).image index) omega
          (index (j + 1)) ≤
        localFrequencySeparation ((Finset.range S.card).image index) omega
          (index j) := by
    rw [himage]
    exact hmono
  have hbound := hpsi.hilbertForm_image_norm_le_two_pi_localSeparation_of_ordered
    index c omega S.card hinj himageNontrivial hmemImage homegaImage hmonoImage
  rw [himage] at hbound
  exact hbound

end MonotoneExtremalKernelCertificate
end DirichletPolynomial
end PrimeNumberTheorem
