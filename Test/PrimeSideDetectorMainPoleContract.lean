import PrimeNumberTheorem.PrimeSideDetectorMainPole

open scoped BigOperators

namespace PrimeNumberTheorem
namespace PrimeSideDetector

example (S : Finset ℕ) (a : ℕ → ℝ) :
    finiteDirichletDetectorAtOne S a =
      ∑ n ∈ S, a n / (n : ℝ) := rfl

example (S : Finset ℕ) (a : ℕ → ℝ) :
    positiveDirichletDetectorMassAtOne S a =
      ∑ n ∈ S, max (a n) 0 / (n : ℝ) := rfl

example (S : Finset ℕ) (a : ℕ → ℝ) :
    negativeDirichletDetectorMassAtOne S a =
      ∑ n ∈ S, max (-a n) 0 / (n : ℝ) := rfl

#check
  (finiteDirichletDetectorAtOne_eq_positive_sub_negative :
    ∀ (S : Finset ℕ) (a : ℕ → ℝ),
      finiteDirichletDetectorAtOne S a =
        positiveDirichletDetectorMassAtOne S a -
          negativeDirichletDetectorMassAtOne S a)

#check
  (@finiteDirichletDetectorAtOne_pos_of_nonnegative :
    ∀ {S : Finset ℕ} {a : ℕ → ℝ},
      (∀ n ∈ S, 0 < n) →
      (∀ n ∈ S, 0 ≤ a n) →
      (∃ n ∈ S, 0 < a n) →
      0 < finiteDirichletDetectorAtOne S a)

#check
  (@finiteDirichletDetectorAtOne_ne_zero_of_nonnegative :
    ∀ {S : Finset ℕ} {a : ℕ → ℝ},
      (∀ n ∈ S, 0 < n) →
      (∀ n ∈ S, 0 ≤ a n) →
      (∃ n ∈ S, 0 < a n) →
      finiteDirichletDetectorAtOne S a ≠ 0)

#check
  (finiteDirichletDetectorAtOne_eq_zero_iff_mass_balance :
    ∀ (S : Finset ℕ) (a : ℕ → ℝ),
      finiteDirichletDetectorAtOne S a = 0 ↔
        positiveDirichletDetectorMassAtOne S a =
          negativeDirichletDetectorMassAtOne S a)

#check
  (@positive_and_negative_coefficients_of_vanishes_at_one :
    ∀ {S : Finset ℕ} {a : ℕ → ℝ},
      (∀ n ∈ S, 0 < n) →
      finiteDirichletDetectorAtOne S a = 0 →
      (∃ n ∈ S, a n ≠ 0) →
      (∃ p ∈ S, 0 < a p) ∧
        (∃ n ∈ S, a n < 0))

end PrimeSideDetector
end PrimeNumberTheorem
