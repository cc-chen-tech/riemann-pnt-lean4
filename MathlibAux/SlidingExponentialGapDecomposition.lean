import MathlibAux.SlidingExponentialCoefficientBound

open Complex
open scoped BigOperators

namespace MathlibAux

/-!
# Diagonal/off-diagonal decomposition for sliding exponential coefficients

This file separates a finite diagonal-plus-frequency-gap sum into its exact
diagonal energy and an off-diagonal bilinear form involving the original
coefficients.  The result is independent of any particular Dirichlet
polynomial.
-/

/-- The diagonal-plus-frequency-gap sum associated with a finite family of
sliding exponential coefficients. -/
noncomputable def slidingExponentialGapSum
    {ι : Type*} (s : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ)
    (A B H : ℝ) : ℝ := by
  classical
  exact
    ∑ m ∈ s, ∑ n ∈ s,
      if m = n then
        (B - A) * Complex.normSq
          (slidingExponentialCoefficient H coeff freq n)
      else
        2 * ‖slidingExponentialCoefficient H coeff freq m‖ *
            ‖slidingExponentialCoefficient H coeff freq n‖ /
          |freq m - freq n|

/-- A finite sliding-exponential gap sum is bounded by its diagonal energy
plus `H²` times the frequency-gap bilinear form of the original
coefficients. -/
theorem slidingExponentialGapSum_le_diagonal_add_frequencyGap
    {ι : Type*} (s : Finset ι) (coeff : ι → ℂ) (freq : ι → ℝ)
    {A B H : ℝ} (_hAB : A ≤ B) :
    slidingExponentialGapSum s coeff freq A B H ≤
      (B - A) *
          ∑ n ∈ s,
            Complex.normSq (slidingExponentialCoefficient H coeff freq n) +
        H ^ 2 *
          ∑ m ∈ s, ∑ n ∈ s,
            2 * ‖coeff m‖ * ‖coeff n‖ / |freq m - freq n| := by
  classical
  have hoff : ∀ m n : ι,
      2 * ‖slidingExponentialCoefficient H coeff freq m‖ *
          ‖slidingExponentialCoefficient H coeff freq n‖ /
        |freq m - freq n| ≤
      H ^ 2 *
        (2 * ‖coeff m‖ * ‖coeff n‖ / |freq m - freq n|) := by
    intro m n
    by_cases hz : |freq m - freq n| = 0
    · rw [hz]
      simp
    · have hpos : 0 < |freq m - freq n| :=
        lt_of_le_of_ne (abs_nonneg _) (Ne.symm hz)
      have hm :=
        norm_slidingExponentialCoefficient_le_abs_length H coeff freq m
      have hn :=
        norm_slidingExponentialCoefficient_le_abs_length H coeff freq n
      have hnum :
          2 *
              (‖slidingExponentialCoefficient H coeff freq m‖ *
                ‖slidingExponentialCoefficient H coeff freq n‖) ≤
            2 * ((‖coeff m‖ * |H|) * (‖coeff n‖ * |H|)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hm hn (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) (abs_nonneg _)))
          (by norm_num)
      calc
        2 * ‖slidingExponentialCoefficient H coeff freq m‖ *
              ‖slidingExponentialCoefficient H coeff freq n‖ /
            |freq m - freq n| =
            (2 *
                (‖slidingExponentialCoefficient H coeff freq m‖ *
                  ‖slidingExponentialCoefficient H coeff freq n‖)) /
              |freq m - freq n| := by ring
        _ ≤
            (2 * ((‖coeff m‖ * |H|) * (‖coeff n‖ * |H|))) /
              |freq m - freq n| := by
          rw [div_le_iff₀ hpos, div_mul_cancel₀ _ hz]
          exact hnum
        _ =
            H ^ 2 *
              (2 * ‖coeff m‖ * ‖coeff n‖ / |freq m - freq n|) := by
          have hH2 :
              (2 : ℝ) * ((‖coeff m‖ * |H|) * (‖coeff n‖ * |H|)) =
                H ^ 2 * (2 * ‖coeff m‖ * ‖coeff n‖) := by
            rw [show (H : ℝ) ^ 2 = |H| ^ 2 by rw [sq_abs]]
            ring
          rw [← mul_div_assoc, hH2]
  have hinner : ∀ m ∈ s,
      (∑ n ∈ s,
          if m = n then
            (B - A) * Complex.normSq
              (slidingExponentialCoefficient H coeff freq n)
          else
            2 * ‖slidingExponentialCoefficient H coeff freq m‖ *
                ‖slidingExponentialCoefficient H coeff freq n‖ /
              |freq m - freq n|) =
        (B - A) * Complex.normSq
            (slidingExponentialCoefficient H coeff freq m) +
          ∑ n ∈ s,
            2 * ‖slidingExponentialCoefficient H coeff freq m‖ *
                ‖slidingExponentialCoefficient H coeff freq n‖ /
              |freq m - freq n| := by
    intro m hm
    have hpoint : ∀ n ∈ s,
        (if m = n then
            (B - A) * Complex.normSq
              (slidingExponentialCoefficient H coeff freq n)
          else
            2 * ‖slidingExponentialCoefficient H coeff freq m‖ *
                ‖slidingExponentialCoefficient H coeff freq n‖ /
              |freq m - freq n|) =
          (if m = n then
              (B - A) * Complex.normSq
                (slidingExponentialCoefficient H coeff freq n)
            else 0) +
            2 * ‖slidingExponentialCoefficient H coeff freq m‖ *
                ‖slidingExponentialCoefficient H coeff freq n‖ /
              |freq m - freq n| := by
      intro n _hn
      by_cases hmn : m = n
      · subst n
        have hzero :
            2 * ‖slidingExponentialCoefficient H coeff freq m‖ *
                  ‖slidingExponentialCoefficient H coeff freq m‖ /
                |freq m - freq m| = 0 := by
          rw [sub_self, abs_zero, div_zero]
        rw [if_pos rfl, if_pos rfl, hzero, add_zero]
      · rw [if_neg hmn, if_neg hmn, zero_add]
    rw [Finset.sum_congr rfl hpoint, Finset.sum_add_distrib,
      Finset.sum_ite_eq, if_pos hm]
  have hsplit :
      slidingExponentialGapSum s coeff freq A B H =
        (B - A) *
            ∑ n ∈ s,
              Complex.normSq
                (slidingExponentialCoefficient H coeff freq n) +
          ∑ m ∈ s, ∑ n ∈ s,
            2 * ‖slidingExponentialCoefficient H coeff freq m‖ *
                ‖slidingExponentialCoefficient H coeff freq n‖ /
              |freq m - freq n| := by
    unfold slidingExponentialGapSum
    rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib]
    congr 1
    rw [← Finset.mul_sum]
  rw [hsplit]
  apply add_le_add_right
  calc
    (∑ m ∈ s, ∑ n ∈ s,
        2 * ‖slidingExponentialCoefficient H coeff freq m‖ *
            ‖slidingExponentialCoefficient H coeff freq n‖ /
          |freq m - freq n|) ≤
        ∑ m ∈ s, ∑ n ∈ s,
          H ^ 2 *
            (2 * ‖coeff m‖ * ‖coeff n‖ / |freq m - freq n|) := by
      apply Finset.sum_le_sum
      intro m _hm
      apply Finset.sum_le_sum
      intro n _hn
      exact hoff m n
    _ =
        H ^ 2 *
          ∑ m ∈ s, ∑ n ∈ s,
            2 * ‖coeff m‖ * ‖coeff n‖ / |freq m - freq n| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _hm
      rw [Finset.mul_sum]

end MathlibAux
