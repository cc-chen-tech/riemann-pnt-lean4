import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Complex.Basic

open Complex
open scoped BigOperators

namespace MathlibAux

/-!
# Square-norm bounds for finite fibers

These lemmas package finite Cauchy--Schwarz for complex sums and for sums
collected along the fibers of a finite map.  They are useful when several
terms of an exponential polynomial have been merged into one coefficient.
-/

/-- Finite Cauchy--Schwarz for a complex sum, written using
`Complex.normSq`. -/
theorem normSq_finset_sum_le_card_mul_sum_normSq
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℂ) :
    Complex.normSq (∑ x ∈ s, f x) ≤
      (s.card : ℝ) * ∑ x ∈ s, Complex.normSq (f x) := by
  rw [Complex.normSq_eq_norm_sq]
  calc
    ‖∑ x ∈ s, f x‖ ^ 2 ≤ (∑ x ∈ s, ‖f x‖) ^ 2 := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (s.card : ℝ) * ∑ x ∈ s, ‖f x‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    _ = (s.card : ℝ) * ∑ x ∈ s, Complex.normSq (f x) := by
      simp only [Complex.normSq_eq_norm_sq]

/-- Apply finite Cauchy--Schwarz separately on every fiber of a finite map. -/
theorem sum_normSq_fiber_le_sum_card_mul_normSq
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (g : ι → κ) (f : ι → ℂ)
    (_hmaps : ∀ x ∈ s, g x ∈ t) :
    (∑ k ∈ t,
        Complex.normSq (∑ x ∈ s.filter (fun x => g x = k), f x)) ≤
      ∑ k ∈ t,
        ((s.filter (fun x => g x = k)).card : ℝ) *
          ∑ x ∈ s.filter (fun x => g x = k), Complex.normSq (f x) := by
  apply Finset.sum_le_sum
  intro k hk
  exact normSq_finset_sum_le_card_mul_sum_normSq
    (s.filter (fun x => g x = k)) f

/-- If every fiber has cardinality at most `C`, collecting terms along the
fibers increases total square-norm energy by at most the factor `C`. -/
theorem sum_normSq_fiber_le_mul_sum_normSq
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (g : ι → κ) (f : ι → ℂ)
    (hmaps : ∀ x ∈ s, g x ∈ t) {C : ℝ}
    (hcard : ∀ k ∈ t, ((s.filter (fun x => g x = k)).card : ℝ) ≤ C) :
    (∑ k ∈ t,
        Complex.normSq (∑ x ∈ s.filter (fun x => g x = k), f x)) ≤
      C * ∑ x ∈ s, Complex.normSq (f x) := by
  calc
    (∑ k ∈ t,
        Complex.normSq (∑ x ∈ s.filter (fun x => g x = k), f x)) ≤
        ∑ k ∈ t,
          ((s.filter (fun x => g x = k)).card : ℝ) *
            ∑ x ∈ s.filter (fun x => g x = k), Complex.normSq (f x) :=
      sum_normSq_fiber_le_sum_card_mul_normSq s t g f hmaps
    _ ≤ ∑ k ∈ t,
        C * ∑ x ∈ s.filter (fun x => g x = k), Complex.normSq (f x) := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_right (hcard k hk)
        (Finset.sum_nonneg fun x hx => Complex.normSq_nonneg (f x))
    _ = C * ∑ k ∈ t,
        ∑ x ∈ s.filter (fun x => g x = k), Complex.normSq (f x) := by
      rw [Finset.mul_sum]
    _ = C * ∑ x ∈ s, Complex.normSq (f x) := by
      rw [Finset.sum_fiberwise_of_maps_to hmaps]

end MathlibAux
