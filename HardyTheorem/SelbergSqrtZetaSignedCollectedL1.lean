import HardyTheorem.SelbergSqrtZetaSignedCollectedEnergy

/-!
# L1 compression for collected signed square-root-zeta coefficients

The pseudo-correlation bound initially produces the square of the collected
coefficient L1 norm. Finite Cauchy--Schwarz compresses this to the number of
distinct frequencies times the collected L2 energy, which can then be
estimated by the exact raw frequency-fiber budget.
-/

open Complex
open scoped BigOperators

namespace HardyTheorem

/-- The square of the collected coefficient L1 norm is at most the number of
distinct frequencies times the collected square energy. -/
theorem sq_sum_norm_selbergSqrtZetaSignedCollectedCoeff_le_card_mul_energy
    (N X : ℕ) :
    (∑ omega ∈ selbergSqrtZetaSignedCollectedFrequencySupport N X,
        ‖selbergSqrtZetaSignedCollectedCoeff N X omega‖) ^ 2 ≤
      ((selbergSqrtZetaSignedCollectedFrequencySupport N X).card : ℝ) *
        ∑ omega ∈ selbergSqrtZetaSignedCollectedFrequencySupport N X,
          Complex.normSq
            (selbergSqrtZetaSignedCollectedCoeff N X omega) := by
  simpa only [Complex.normSq_eq_norm_sq] using
    (sq_sum_le_card_mul_sum_sq
      (s := selbergSqrtZetaSignedCollectedFrequencySupport N X)
      (f := fun omega =>
        ‖selbergSqrtZetaSignedCollectedCoeff N X omega‖))

/-- A nonnegative multiple of the pseudo-correlation coefficient double sum
is controlled by cardinality times collected square energy. -/
theorem
    sum_sum_mul_norm_selbergSqrtZetaSignedCollectedCoeff_le_card_mul_energy
    (N X : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    (∑ omega ∈ selbergSqrtZetaSignedCollectedFrequencySupport N X,
        ∑ nu ∈ selbergSqrtZetaSignedCollectedFrequencySupport N X,
          C * (‖selbergSqrtZetaSignedCollectedCoeff N X omega‖ *
            ‖selbergSqrtZetaSignedCollectedCoeff N X nu‖)) ≤
      C * ((selbergSqrtZetaSignedCollectedFrequencySupport N X).card : ℝ) *
        ∑ omega ∈ selbergSqrtZetaSignedCollectedFrequencySupport N X,
          Complex.normSq
            (selbergSqrtZetaSignedCollectedCoeff N X omega) := by
  let S := selbergSqrtZetaSignedCollectedFrequencySupport N X
  let a : ℝ → ℝ := fun omega =>
    ‖selbergSqrtZetaSignedCollectedCoeff N X omega‖
  have hsq :
      (∑ omega ∈ S, a omega) ^ 2 ≤
        (S.card : ℝ) *
          ∑ omega ∈ S,
            Complex.normSq
              (selbergSqrtZetaSignedCollectedCoeff N X omega) := by
    simpa only [S, a] using
      sq_sum_norm_selbergSqrtZetaSignedCollectedCoeff_le_card_mul_energy N X
  calc
    (∑ omega ∈ S, ∑ nu ∈ S, C * (a omega * a nu)) =
        ∑ omega ∈ S, (C * a omega) * ∑ nu ∈ S, a nu := by
      apply Finset.sum_congr rfl
      intro omega homega
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro nu hnu
      ring
    _ = (∑ omega ∈ S, C * a omega) * ∑ nu ∈ S, a nu := by
      rw [Finset.sum_mul]
    _ = C * (∑ omega ∈ S, a omega) ^ 2 := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ C * ((S.card : ℝ) *
          ∑ omega ∈ S,
            Complex.normSq
              (selbergSqrtZetaSignedCollectedCoeff N X omega)) :=
      mul_le_mul_of_nonneg_left hsq hC
    _ = C * (S.card : ℝ) *
        ∑ omega ∈ S,
          Complex.normSq
            (selbergSqrtZetaSignedCollectedCoeff N X omega) := by ring

/-- The pseudo-correlation coefficient double sum is therefore bounded by
the exact raw signed frequency-fiber multiplicity budget. -/
theorem
    sum_sum_mul_norm_selbergSqrtZetaSignedCollectedCoeff_le_fiber_budget
    (N X : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    (∑ omega ∈ selbergSqrtZetaSignedCollectedFrequencySupport N X,
        ∑ nu ∈ selbergSqrtZetaSignedCollectedFrequencySupport N X,
          C * (‖selbergSqrtZetaSignedCollectedCoeff N X omega‖ *
            ‖selbergSqrtZetaSignedCollectedCoeff N X nu‖)) ≤
      C * ((selbergSqrtZetaSignedCollectedFrequencySupport N X).card : ℝ) *
        ∑ omega ∈ selbergSqrtZetaSignedCollectedFrequencySupport N X,
          (((selbergSqrtZetaSignedPhaseSupport N X).filter
            (fun p => selbergSqrtZetaSignedPhaseFrequency p = omega)).card : ℝ) *
          ∑ p ∈ (selbergSqrtZetaSignedPhaseSupport N X).filter
            (fun p => selbergSqrtZetaSignedPhaseFrequency p = omega),
            Complex.normSq (selbergSqrtZetaSignedPhaseCoeff X p) := by
  have hcard : 0 ≤
      C * ((selbergSqrtZetaSignedCollectedFrequencySupport N X).card : ℝ) :=
    mul_nonneg hC (Nat.cast_nonneg _)
  exact
    (sum_sum_mul_norm_selbergSqrtZetaSignedCollectedCoeff_le_card_mul_energy
      N X hC).trans
      (mul_le_mul_of_nonneg_left
        (sum_normSq_selbergSqrtZetaSignedCollectedCoeff_le_fiber_budget N X)
        hcard)

end HardyTheorem
