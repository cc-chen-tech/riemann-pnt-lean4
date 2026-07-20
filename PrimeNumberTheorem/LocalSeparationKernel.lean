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

/-- The distinct local separation values, arranged in nondecreasing order. -/
noncomputable def orderedLocalFrequencySeparations
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (omega : ι → ℝ) : List ℝ :=
  (S.image (localFrequencySeparation S omega)).sort (· ≤ ·)

/-- The list of distinct local separations is sorted. -/
theorem orderedLocalFrequencySeparations_pairwise
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (omega : ι → ℝ) :
    (orderedLocalFrequencySeparations S omega).Pairwise (· ≤ ·) := by
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
