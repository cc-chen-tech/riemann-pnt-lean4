import PrimeNumberTheorem.PositiveFourierKernel
import Mathlib.Data.Finset.Sort

open Complex MeasureTheory
open scoped BigOperators ComplexConjugate

namespace PrimeNumberTheorem
namespace DirichletPolynomial

/-- The distance from one frequency to its nearest distinct frequency in a
finite family.  It is zero when there is no other index in the family. -/
noncomputable def localFrequencySeparation {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (omega : ι → ℝ) (n : ι) : ℝ :=
  if h : (S.erase n).Nonempty then
    (S.erase n).inf' h (fun m => |omega n - omega m|)
  else 0

/-- The local separation is no larger than the distance to any prescribed
distinct frequency in the family. -/
theorem localFrequencySeparation_le_abs_sub
    {ι : Type*} [DecidableEq ι] {S : Finset ι} {omega : ι → ℝ} {m n : ι}
    (hm : m ∈ S) (hmn : m ≠ n) :
    localFrequencySeparation S omega n ≤ |omega n - omega m| := by
  have hmErase : m ∈ S.erase n := Finset.mem_erase.mpr ⟨hmn, hm⟩
  rw [localFrequencySeparation, dif_pos ⟨m, hmErase⟩]
  exact Finset.inf'_le _ hmErase

/-- In a nontrivial finite family of distinct frequencies, every local
separation is strictly positive. -/
theorem localFrequencySeparation_pos
    {ι : Type*} [DecidableEq ι] {S : Finset ι} {omega : ι → ℝ} {n : ι}
    (hS : S.Nontrivial) (hn : n ∈ S)
    (homega : Set.InjOn omega (S : Set ι)) :
    0 < localFrequencySeparation S omega n := by
  have hErase : (S.erase n).Nonempty := hS.erase_nonempty
  rw [localFrequencySeparation, dif_pos hErase, Finset.lt_inf'_iff]
  intro m hm
  have hmS : m ∈ S := Finset.mem_of_mem_erase hm
  have hmn : m ≠ n := (Finset.mem_erase.mp hm).1
  apply abs_pos.mpr
  rw [sub_ne_zero]
  intro heq
  exact hmn (homega hmS hn heq.symm)

/-- Convert a frequency gap in the convention `exp (i * omega * t)` to the
dilation parameter used by Fourier transforms normalized with
`exp (-2 * pi * i * lambda * t)`. -/
noncomputable def normalizedFourierDilationScale (delta : ℝ) : ℝ :=
  delta / (2 * Real.pi)

theorem normalizedFourierDilationScale_pos
    {delta : ℝ} (hdelta : 0 < delta) :
    0 < normalizedFourierDilationScale delta := by
  unfold normalizedFourierDilationScale
  positivity

theorem two_pi_mul_normalizedFourierDilationScale (delta : ℝ) :
    2 * Real.pi * normalizedFourierDilationScale delta = delta := by
  unfold normalizedFourierDilationScale
  field_simp [Real.pi_ne_zero]

theorem normalizedFourierDilationScale_mono
    {deltaNew deltaOld : ℝ} (horder : deltaNew ≤ deltaOld) :
    normalizedFourierDilationScale deltaNew ≤
      normalizedFourierDilationScale deltaOld := by
  unfold normalizedFourierDilationScale
  exact div_le_div_of_nonneg_right horder (by positivity)

/-- A reciprocal Fourier tail beyond `2 * pi` remains exactly reciprocal
after dilation by a prescribed frequency gap divided by `2 * pi`. -/
theorem fourierKernel_normalizedDilation_eq_const_div
    {g : ℝ → ℝ} {kappa : ℂ} {delta xi : ℝ}
    (hdelta : 0 < delta) (hgap : delta ≤ |xi|)
    (htail : ∀ eta : ℝ, 2 * Real.pi ≤ |eta| →
      fourierKernel g eta = kappa / eta) :
    fourierKernel
        (fun t => g (normalizedFourierDilationScale delta * t)) xi =
      kappa / xi := by
  let q := normalizedFourierDilationScale delta
  have hq : 0 < q := normalizedFourierDilationScale_pos hdelta
  have hthreshold : 2 * Real.pi ≤ |xi / q| := by
    rw [abs_div, abs_of_pos hq]
    apply (le_div_iff₀ hq).2
    rw [show 2 * Real.pi * q = delta by
      exact two_pi_mul_normalizedFourierDilationScale delta]
    exact hgap
  rw [fourierKernel_scale_pos hq, htail _ hthreshold]
  push_cast
  field_simp [hq.ne']

/-- The correctly normalized dilation scale attached to one local frequency
separation. -/
noncomputable def localFourierDilationScale
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (omega : ι → ℝ) (n : ι) : ℝ :=
  normalizedFourierDilationScale (localFrequencySeparation S omega n)

theorem localFourierDilationScale_pos
    {ι : Type*} [DecidableEq ι] {S : Finset ι} {omega : ι → ℝ} {n : ι}
    (hS : S.Nontrivial) (hn : n ∈ S)
    (homega : Set.InjOn omega (S : Set ι)) :
    0 < localFourierDilationScale S omega n := by
  exact normalizedFourierDilationScale_pos
    (localFrequencySeparation_pos hS hn homega)

/-- The normalized local dilation reaches the Fourier tail threshold before
every distinct frequency difference. -/
theorem two_pi_mul_localFourierDilationScale_le_abs_sub
    {ι : Type*} [DecidableEq ι] {S : Finset ι} {omega : ι → ℝ} {m n : ι}
    (hm : m ∈ S) (hmn : m ≠ n) :
    2 * Real.pi * localFourierDilationScale S omega n ≤
      |omega n - omega m| := by
  rw [localFourierDilationScale,
    two_pi_mul_normalizedFourierDilationScale]
  exact localFrequencySeparation_le_abs_sub hm hmn

/-- A base kernel with reciprocal-frequency tail beyond `2 * pi`, dilated by
the normalized local separation, preserves its reciprocal-frequency constant
on every off-diagonal frequency. -/
theorem fourierKernel_localDilation_eq_const_div
    {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {omega : ι → ℝ} {g : ℝ → ℝ} {kappa : ℂ} {m n : ι}
    (hS : S.Nontrivial) (hm : m ∈ S) (hn : n ∈ S) (hmn : m ≠ n)
    (homega : Set.InjOn omega (S : Set ι))
    (htail : ∀ xi : ℝ, 2 * Real.pi ≤ |xi| →
      fourierKernel g xi = kappa / xi) :
    fourierKernel
        (fun t => g (localFourierDilationScale S omega n * t))
        (omega n - omega m) =
      kappa / (omega n - omega m) := by
  let delta := localFourierDilationScale S omega n
  have hdelta : 0 < delta := localFourierDilationScale_pos hS hn homega
  have hthreshold :
      2 * Real.pi ≤ |(omega n - omega m) / delta| := by
    rw [abs_div, abs_of_pos hdelta]
    apply (le_div_iff₀ hdelta).2
    exact two_pi_mul_localFourierDilationScale_le_abs_sub hm hmn
  have hfreq : omega n - omega m ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    exact hmn (homega hm hn h.symm)
  rw [fourierKernel_scale_pos hdelta, htail _ hthreshold]
  push_cast
  field_simp [hdelta.ne', hfreq]

/-- The specialization of the convention bridge to the negative Hilbert
kernel supplied by the monotone majorant. -/
theorem fourierKernel_localDilation_eq_neg_two_I_div
    {ι : Type*} [DecidableEq ι]
    {S : Finset ι} {omega : ι → ℝ} {g : ℝ → ℝ} {m n : ι}
    (hS : S.Nontrivial) (hm : m ∈ S) (hn : n ∈ S) (hmn : m ≠ n)
    (homega : Set.InjOn omega (S : Set ι))
    (htail : ∀ xi : ℝ, 2 * Real.pi ≤ |xi| →
      fourierKernel g xi = (-2 * Complex.I) / xi) :
    fourierKernel
        (fun t => g (localFourierDilationScale S omega n * t))
        (omega n - omega m) =
      (-2 * Complex.I) / (omega n - omega m) :=
  fourierKernel_localDilation_eq_const_div
    hS hm hn hmn homega htail

/-- The distinct local separation values, arranged in nonincreasing order as
in the weighted Hilbert--Montgomery--Vaughan argument. -/
noncomputable def orderedLocalFrequencySeparations
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (omega : ι → ℝ) : List ℝ :=
  (S.image (localFrequencySeparation S omega)).sort (· ≥ ·)

/-- The list of distinct local separations is sorted. -/
theorem orderedLocalFrequencySeparations_pairwise
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (omega : ι → ℝ) :
    (orderedLocalFrequencySeparations S omega).Pairwise (· ≥ ·) := by
  classical
  exact Finset.pairwise_sort _ _

/-- Membership in the ordered list is exactly occurrence as a local
separation of an index in the original family. -/
theorem mem_orderedLocalFrequencySeparations
    {ι : Type*} [DecidableEq ι] {S : Finset ι} {omega : ι → ℝ} {delta : ℝ} :
    delta ∈ orderedLocalFrequencySeparations S omega ↔
      ∃ n ∈ S, localFrequencySeparation S omega n = delta := by
  classical
  simp [orderedLocalFrequencySeparations]

/-- Every scale in the ordered local-separation list is positive when the
finite frequency family is nontrivial and injective. -/
theorem orderedLocalFrequencySeparations_pos
    {ι : Type*} [DecidableEq ι] {S : Finset ι} {omega : ι → ℝ}
    (hS : S.Nontrivial) (homega : Set.InjOn omega (S : Set ι))
    {delta : ℝ} (hdelta : delta ∈ orderedLocalFrequencySeparations S omega) :
    0 < delta := by
  rcases mem_orderedLocalFrequencySeparations.mp hdelta with ⟨n, hn, hndelta⟩
  rw [← hndelta]
  exact localFrequencySeparation_pos hS hn homega

/-- The frequency-side profile obtained by positively dilating a Fourier
weight. -/
noncomputable def scaledFourierProfile (g : ℝ → ℝ) (delta xi : ℝ) : ℂ :=
  ((delta⁻¹ : ℝ) : ℂ) * fourierKernel g (xi / delta)

/-- Positive dilation of the original weight realizes the scaled Fourier
profile. -/
theorem fourierKernel_eq_scaledFourierProfile
    {g : ℝ → ℝ} {delta xi : ℝ} (hdelta : 0 < delta) :
    fourierKernel (fun t => g (delta * t)) xi =
      scaledFourierProfile g delta xi := by
  exact fourierKernel_scale_pos hdelta

/-- Successive scaled Fourier profiles telescope along any scale sequence.
An ordered local-separation sequence is the intended application. -/
theorem scaledFourierProfile_telescope
    (g : ℝ → ℝ) (delta : ℕ → ℝ) (xi : ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N,
        (scaledFourierProfile g (delta (k + 1)) xi -
          scaledFourierProfile g (delta k) xi)) =
      scaledFourierProfile g (delta N) xi -
        scaledFourierProfile g (delta 0) xi := by
  exact Finset.sum_range_sub (fun k => scaledFourierProfile g (delta k) xi) N

/-- The sum of successive differences along a list. -/
def adjacentDifferenceSum {α A : Type*} [AddGroup A]
    (F : α → A) : List α → A
  | [] => 0
  | _ :: [] => 0
  | a :: b :: tail =>
      (F b - F a) + adjacentDifferenceSum F (b :: tail)

/-- The endpoint difference of a list, with the empty and singleton cases
normalized to zero. -/
def endpointDifference {α A : Type*} [AddGroup A]
    (F : α → A) : List α → A
  | [] => 0
  | a :: tail =>
      match tail.getLast? with
      | none => 0
      | some b => F b - F a

/-- Summing all adjacent differences leaves only the last value minus the
first value. -/
theorem adjacentDifferenceSum_eq_endpointDifference
    {α A : Type*} [AddCommGroup A] (F : α → A) (l : List α) :
    adjacentDifferenceSum F l = endpointDifference F l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      cases l with
      | nil => rfl
      | cons b tail =>
          simp only [adjacentDifferenceSum]
          rw [ih]
          cases tail with
          | nil => simp [endpointDifference]
          | cons c tail =>
              simp only [endpointDifference, List.getLast?_cons, Option.getD_some]
              abel

/-- The scaled Fourier profiles at the ordered distinct local-separation
scales telescope to their endpoint difference. -/
theorem orderedLocalFrequencySeparations_telescope
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (omega : ι → ℝ) (g : ℝ → ℝ) (xi : ℝ) :
    adjacentDifferenceSum (fun delta => scaledFourierProfile g delta xi)
        (orderedLocalFrequencySeparations S omega) =
      endpointDifference (fun delta => scaledFourierProfile g delta xi)
        (orderedLocalFrequencySeparations S omega) :=
  adjacentDifferenceSum_eq_endpointDifference _ _

/-- The finite Fourier-kernel forms at the ordered distinct local-separation
scales telescope to their endpoint difference. -/
theorem orderedLocalFrequencySeparations_kernelForm_telescope
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (c : ι → ℂ) (omega : ι → ℝ) (g : ℝ → ℝ) :
    adjacentDifferenceSum
        (fun delta => finiteFourierKernelForm S c omega
          (fun t => g (delta * t)))
        (orderedLocalFrequencySeparations S omega) =
      endpointDifference
        (fun delta => finiteFourierKernelForm S c omega
          (fun t => g (delta * t)))
        (orderedLocalFrequencySeparations S omega) :=
  adjacentDifferenceSum_eq_endpointDifference _ _

/-- The indices in `range N` retained at stage `j`. -/
def suffixIndexSet (N j : ℕ) : Finset ℕ :=
  (Finset.range N).filter (j ≤ ·)

/-- Reordering a sum over nested suffixes: a pair `(m,n)` occurs precisely at
the stages `j ≤ min m n`.  This is the finite combinatorial identity used in
the weighted Hilbert--Montgomery--Vaughan proof. -/
theorem sum_suffix_double_eq_sum_min
    {A : Type*} [AddCommMonoid A]
    (term : ℕ → ℕ → ℕ → A) (N : ℕ) :
    (∑ j ∈ Finset.range N, ∑ m ∈ suffixIndexSet N j,
        ∑ n ∈ suffixIndexSet N j, term j m n) =
      ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
        ∑ j ∈ Finset.range (min m n + 1), term j m n := by
  calc
    (∑ j ∈ Finset.range N, ∑ m ∈ suffixIndexSet N j,
        ∑ n ∈ suffixIndexSet N j, term j m n) =
        ∑ j ∈ Finset.range N, ∑ m ∈ Finset.range N,
          ∑ n ∈ Finset.range N,
            if j ≤ m ∧ j ≤ n then term j m n else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [suffixIndexSet]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_filter]
      by_cases hjm : j ≤ m <;> simp [hjm]
    _ = ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          ∑ j ∈ Finset.range N,
            if j ≤ m ∧ j ≤ n then term j m n else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_comm]
    _ = ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          ∑ j ∈ Finset.range (min m n + 1), term j m n := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      have hmN : m < N := Finset.mem_range.mp hm
      have hnN : n < N := Finset.mem_range.mp hn
      have hfilter :
          (Finset.range N).filter (fun j => j ≤ m ∧ j ≤ n) =
            Finset.range (min m n + 1) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      rw [← Finset.sum_filter, hfilter]

/-- After the suffix reordering, successive kernel increments telescope for
each pair of indices. -/
theorem sum_suffix_mul_kernelIncrement_telescope
    {R : Type*} [CommRing R]
    (a : ℕ → ℕ → R) (K : ℕ → ℕ → ℕ → R) (N : ℕ) :
    (∑ j ∈ Finset.range N, ∑ m ∈ suffixIndexSet N j,
        ∑ n ∈ suffixIndexSet N j,
          a m n * (K (j + 1) m n - K j m n)) =
      ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
        a m n * (K (min m n + 1) m n - K 0 m n) := by
  rw [sum_suffix_double_eq_sum_min]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Finset.mul_sum]
  congr 1
  exact Finset.sum_range_sub (fun j => K j m n) (min m n + 1)

/-- The Fourier-kernel form version of the suffix telescope.  Each stage uses
the difference of two integrable weights on the current suffix, and each pair
of indices survives exactly to its `min` endpoint. -/
theorem sum_suffix_finiteFourierKernelForm_sub_telescope
    (c : ℕ → ℂ) (omega : ℕ → ℝ) (g : ℕ → ℝ → ℝ)
    (hg : ∀ j, Integrable (g j)) (N : ℕ) :
    (∑ j ∈ Finset.range N,
        finiteFourierKernelForm (suffixIndexSet N j) c omega
          (fun t => g (j + 1) t - g j t)) =
      ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
        conj (c m) * c n *
          (fourierKernel (g (min m n + 1)) (omega n - omega m) -
            fourierKernel (g 0) (omega n - omega m)) := by
  calc
    (∑ j ∈ Finset.range N,
        finiteFourierKernelForm (suffixIndexSet N j) c omega
          (fun t => g (j + 1) t - g j t)) =
        ∑ j ∈ Finset.range N, ∑ m ∈ suffixIndexSet N j,
          ∑ n ∈ suffixIndexSet N j,
            conj (c m) * c n *
              (fourierKernel (g (j + 1)) (omega n - omega m) -
                fourierKernel (g j) (omega n - omega m)) := by
      apply Finset.sum_congr rfl
      intro j hj
      unfold finiteFourierKernelForm
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      rw [fourierKernel_sub (hg (j + 1)) (hg j)]
    _ = ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          conj (c m) * c n *
            (fourierKernel (g (min m n + 1)) (omega n - omega m) -
              fourierKernel (g 0) (omega n - omega m)) := by
      exact sum_suffix_mul_kernelIncrement_telescope
        (fun m n => conj (c m) * c n)
        (fun j m n => fourierKernel (g j) (omega n - omega m)) N

/-- The finite Fourier-kernel forms telescope when their dilation scales are
the local separations selected by an index sequence. -/
theorem finiteFourierKernelForm_localSeparation_telescope
    {ι : Type*} [DecidableEq ι]
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
          (fun t => g (localFrequencySeparation S omega (index 0) * t)) := by
  exact finiteFourierKernelForm_telescope S c omega
    (fun k t => g (localFrequencySeparation S omega (index k) * t)) N

end DirichletPolynomial
end PrimeNumberTheorem
