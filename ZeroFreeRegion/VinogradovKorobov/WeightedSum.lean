import ZeroFreeRegion.VinogradovKorobov.LogVanDerCorput

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

/-- Finite Abel summation written in terms of prefix sums. -/
lemma weighted_sum_eq_endpoint_add_partial_sums
    (a : ℕ → ℝ) (z : ℕ → ℂ) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), (a k : ℂ) * z k) =
      (a N : ℂ) * (∑ k ∈ Finset.range (N + 1), z k) +
        ∑ k ∈ Finset.range N,
          ((a k - a (k + 1) : ℝ) : ℂ) *
            (∑ j ∈ Finset.range (k + 1), z j) := by
  induction N with
  | zero => simp
  | succ N ih =>
      calc
        (∑ k ∈ Finset.range (N + 1 + 1), (a k : ℂ) * z k) =
            (∑ k ∈ Finset.range (N + 1), (a k : ℂ) * z k) +
              (a (N + 1) : ℂ) * z (N + 1) := by
          rw [Finset.sum_range_succ]
        _ = ((a N : ℂ) * (∑ k ∈ Finset.range (N + 1), z k) +
              ∑ k ∈ Finset.range N,
                ((a k - a (k + 1) : ℝ) : ℂ) *
                  (∑ j ∈ Finset.range (k + 1), z j)) +
              (a (N + 1) : ℂ) * z (N + 1) := by rw [ih]
        _ = (a (N + 1) : ℂ) * (∑ k ∈ Finset.range (N + 1 + 1), z k) +
              ∑ k ∈ Finset.range (N + 1),
                ((a k - a (k + 1) : ℝ) : ℂ) *
                  (∑ j ∈ Finset.range (k + 1), z j) := by
          simp only [Finset.sum_range_succ]
          push_cast
          ring

/-- Abel transfer: a uniform bound for every prefix sum transfers to any
nonnegative antitone real weight, with loss only from the first weight. -/
theorem norm_weighted_sum_le_first_mul
    (a : ℕ → ℝ) (z : ℕ → ℂ) (N : ℕ) (B : ℝ)
    (ha : ∀ k ≤ N, 0 ≤ a k)
    (hanti : ∀ k < N, a (k + 1) ≤ a k)
    (hpartial : ∀ k ≤ N,
      ‖∑ j ∈ Finset.range (k + 1), z j‖ ≤ B) :
    ‖∑ k ∈ Finset.range (N + 1), (a k : ℂ) * z k‖ ≤ a 0 * B := by
  have hend :
      ‖(a N : ℂ) * (∑ k ∈ Finset.range (N + 1), z k)‖ ≤ a N * B := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha N le_rfl)]
    exact mul_le_mul_of_nonneg_left (hpartial N le_rfl) (ha N le_rfl)
  have hvariation :
      ‖∑ k ∈ Finset.range N,
          ((a k - a (k + 1) : ℝ) : ℂ) *
            (∑ j ∈ Finset.range (k + 1), z j)‖ ≤
        ∑ k ∈ Finset.range N, (a k - a (k + 1)) * B := by
    calc
      ‖∑ k ∈ Finset.range N,
          ((a k - a (k + 1) : ℝ) : ℂ) *
            (∑ j ∈ Finset.range (k + 1), z j)‖ ≤
          ∑ k ∈ Finset.range N,
            ‖((a k - a (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.range (k + 1), z j)‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range N, (a k - a (k + 1)) * B := by
        apply Finset.sum_le_sum
        intro k hk
        have hkN : k < N := Finset.mem_range.mp hk
        have hdiff : 0 ≤ a k - a (k + 1) := sub_nonneg.mpr (hanti k hkN)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hdiff]
        exact mul_le_mul_of_nonneg_left
          (hpartial k (Nat.le_of_lt hkN)) hdiff
  rw [weighted_sum_eq_endpoint_add_partial_sums]
  calc
    ‖(a N : ℂ) * (∑ k ∈ Finset.range (N + 1), z k) +
        ∑ k ∈ Finset.range N,
          ((a k - a (k + 1) : ℝ) : ℂ) *
            (∑ j ∈ Finset.range (k + 1), z j)‖ ≤
        ‖(a N : ℂ) * (∑ k ∈ Finset.range (N + 1), z k)‖ +
          ‖∑ k ∈ Finset.range N,
            ((a k - a (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.range (k + 1), z j)‖ := norm_add_le _ _
    _ ≤ a N * B + ∑ k ∈ Finset.range N, (a k - a (k + 1)) * B :=
      add_le_add hend hvariation
    _ = a 0 * B := by
      rw [← Finset.sum_mul, Finset.sum_range_sub']
      ring

end ZeroFreeRegion.VinogradovKorobov
