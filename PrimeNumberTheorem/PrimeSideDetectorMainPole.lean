import Mathlib

open scoped BigOperators

namespace PrimeNumberTheorem
namespace PrimeSideDetector

noncomputable section

/-!
# The main-pole obstruction for prime-side Dirichlet detectors

A finite Dirichlet polynomial with nonnegative, nonzero coefficients cannot
vanish at `s = 1`.  This elementary fact blocks the naive attempt to cancel
the zeta main pole while preserving coefficientwise positivity on the prime
side.
-/

/-- The value at `s = 1` of a finite real Dirichlet detector. -/
def finiteDirichletDetectorAtOne
    (S : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ n ∈ S, a n / (n : ℝ)

/-- Positive weighted coefficient mass at `s = 1`. -/
def positiveDirichletDetectorMassAtOne
    (S : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ n ∈ S, max (a n) 0 / (n : ℝ)

/-- Negative weighted coefficient mass at `s = 1`. -/
def negativeDirichletDetectorMassAtOne
    (S : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ n ∈ S, max (-a n) 0 / (n : ℝ)

private theorem eq_max_sub_max_neg (x : ℝ) :
    x = max x 0 - max (-x) 0 := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
    simp
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [max_eq_right hx', max_eq_left (neg_nonneg.mpr hx')]
    ring

/-- The detector value is exactly positive weighted mass minus negative
weighted mass. -/
theorem finiteDirichletDetectorAtOne_eq_positive_sub_negative
    (S : Finset ℕ) (a : ℕ → ℝ) :
    finiteDirichletDetectorAtOne S a =
      positiveDirichletDetectorMassAtOne S a -
        negativeDirichletDetectorMassAtOne S a := by
  unfold finiteDirichletDetectorAtOne
    positiveDirichletDetectorMassAtOne
    negativeDirichletDetectorMassAtOne
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← sub_div]
  congr 1
  exact eq_max_sub_max_neg (a n)

/-- Nonnegative coefficients, at least one of them positive, give a strictly
positive value at `s = 1`. -/
theorem finiteDirichletDetectorAtOne_pos_of_nonnegative
    {S : Finset ℕ} {a : ℕ → ℝ}
    (hindex : ∀ n ∈ S, 0 < n)
    (hnonneg : ∀ n ∈ S, 0 ≤ a n)
    (hpositive : ∃ n ∈ S, 0 < a n) :
    0 < finiteDirichletDetectorAtOne S a := by
  unfold finiteDirichletDetectorAtOne
  rcases hpositive with ⟨n, hn, han⟩
  refine Finset.sum_pos' (fun k hk => ?_) ⟨n, hn, ?_⟩
  · exact div_nonneg (hnonneg k hk) (Nat.cast_nonneg k)
  · exact div_pos han (by exact_mod_cast hindex n hn)

/-- A nonzero finite Dirichlet detector with nonnegative coefficients cannot
cancel the pole at `s = 1`. -/
theorem finiteDirichletDetectorAtOne_ne_zero_of_nonnegative
    {S : Finset ℕ} {a : ℕ → ℝ}
    (hindex : ∀ n ∈ S, 0 < n)
    (hnonneg : ∀ n ∈ S, 0 ≤ a n)
    (hpositive : ∃ n ∈ S, 0 < a n) :
    finiteDirichletDetectorAtOne S a ≠ 0 :=
  ne_of_gt
    (finiteDirichletDetectorAtOne_pos_of_nonnegative
      hindex hnonneg hpositive)

/-- Cancellation of the value at `s = 1` is exactly equality of the positive
and negative weighted coefficient masses. -/
theorem finiteDirichletDetectorAtOne_eq_zero_iff_mass_balance
    (S : Finset ℕ) (a : ℕ → ℝ) :
    finiteDirichletDetectorAtOne S a = 0 ↔
      positiveDirichletDetectorMassAtOne S a =
        negativeDirichletDetectorMassAtOne S a := by
  rw [finiteDirichletDetectorAtOne_eq_positive_sub_negative]
  exact sub_eq_zero

private theorem finiteDirichletDetectorAtOne_neg
    (S : Finset ℕ) (a : ℕ → ℝ) :
    finiteDirichletDetectorAtOne S (fun n => -a n) =
      -finiteDirichletDetectorAtOne S a := by
  unfold finiteDirichletDetectorAtOne
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- Every nontrivial finite detector which cancels at `s = 1` has both a
positive and a negative supported coefficient. -/
theorem positive_and_negative_coefficients_of_vanishes_at_one
    {S : Finset ℕ} {a : ℕ → ℝ}
    (hindex : ∀ n ∈ S, 0 < n)
    (hzero : finiteDirichletDetectorAtOne S a = 0)
    (hnontrivial : ∃ n ∈ S, a n ≠ 0) :
    (∃ p ∈ S, 0 < a p) ∧
      (∃ n ∈ S, a n < 0) := by
  constructor
  · by_contra hpositive
    push Not at hpositive
    rcases hnontrivial with ⟨n, hn, han⟩
    have hanNeg : 0 < -a n := by
      have hanLe : a n ≤ 0 := hpositive n hn
      have hanLt : a n < 0 := lt_of_le_of_ne hanLe han
      linarith
    have hnegDetector :
        0 < finiteDirichletDetectorAtOne S (fun k => -a k) :=
      finiteDirichletDetectorAtOne_pos_of_nonnegative hindex
        (fun k hk => neg_nonneg.mpr
          (hpositive k hk))
        ⟨n, hn, hanNeg⟩
    rw [finiteDirichletDetectorAtOne_neg, hzero] at hnegDetector
    simp at hnegDetector
  · by_contra hnegative
    push Not at hnegative
    rcases hnontrivial with ⟨n, hn, han⟩
    have hanPos : 0 < a n :=
      lt_of_le_of_ne (hnegative n hn) han.symm
    have hdetectorPos :=
      finiteDirichletDetectorAtOne_pos_of_nonnegative hindex
        (fun k hk => hnegative k hk)
        ⟨n, hn, hanPos⟩
    rw [hzero] at hdetectorPos
    exact (lt_irrefl 0) hdetectorPos

end

end PrimeSideDetector
end PrimeNumberTheorem
