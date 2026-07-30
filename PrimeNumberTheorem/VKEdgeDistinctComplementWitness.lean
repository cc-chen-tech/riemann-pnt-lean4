import PrimeNumberTheorem.VKEdgeProportionalWindowTransfer

open Complex Filter MeasureTheory Set

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-!
# Distinct complementary-zero witnesses

Positive energy in the canonical full complementary packet cannot be carried
by an empty complement.  This module turns that observation into an exact
new-zero witness outside any already selected finite set `S`.

The final theorem isolates the remaining iteration input: the true selected
cluster remainder must exceed three times the approximation and closed-term
budgets.  Once that surplus is available, a new zero outside `S` follows
without any additional counting assumption.
-/

/-- If the selected set already contains every zero in the height truncation,
the normalized complementary contribution vanishes identically. -/
theorem
    normalizedFiniteZeroClusterComplementContribution_eq_zero_of_subset
    (S : Finset ℂ) (T beta y : ℝ)
    (hsubset : nontrivialZerosFinset T ⊆ S) :
    normalizedFiniteZeroClusterComplementContribution S T beta y = 0 := by
  have hdiff : nontrivialZerosFinset T \ S = ∅ :=
    Finset.sdiff_eq_empty_iff_subset.mpr hsubset
  simp [normalizedFiniteZeroClusterComplementContribution,
    finiteZeroClusterComplementContribution, hdiff]

/-- Under the same containment hypothesis, the canonical full moving
complementary Gaussian energy is exactly zero. -/
theorem
    dynamicComplementFullMovingGaussianSecondMoment_eq_zero_of_subset
    (S : Finset ℂ) (T beta a m L : ℝ)
    (hsubset : nontrivialZerosFinset T ⊆ S) :
    dynamicComplementForwardMovingGaussianSecondMoment
        S T beta a (dynamicComplementFullBucketSet S T) m L = 0 := by
  rw [dynamicComplementForwardMovingGaussianSecondMoment_fullBucketSet]
  unfold
    normalizedFiniteZeroClusterComplementForwardGaussianSecondMoment
  simp [
    normalizedFiniteZeroClusterComplementContribution_eq_zero_of_subset
      S T beta _ hsubset,
    pow_two]

/-- Strictly positive full complementary energy produces a genuine zeta zero
inside the height truncation that is not already in `S`. -/
theorem
    exists_nontrivialZero_not_mem_of_fullMovingGaussianSecondMoment_pos
    {S : Finset ℂ} {T beta a m L : ℝ}
    (hpos :
      0 <
        dynamicComplementForwardMovingGaussianSecondMoment
          S T beta a (dynamicComplementFullBucketSet S T) m L) :
    ∃ rho ∈ nontrivialZerosFinset T, rho ∉ S := by
  by_contra hnew
  have hsubset : nontrivialZerosFinset T ⊆ S := by
    intro rho hrho
    by_contra hrhoS
    exact hnew ⟨rho, hrho, hrhoS⟩
  have hzero :=
    dynamicComplementFullMovingGaussianSecondMoment_eq_zero_of_subset
      S T beta a m L hsubset
  rw [hzero] at hpos
  exact (lt_irrefl 0) hpos

/-- A selected-cluster residual energy exceeding three times the finite-height
approximation and closed-term budgets forces a new zero outside the selected
set.

This is the duplicate-free witness extraction step.  It does not prove that
the surplus hypothesis persists after adjoining the newly found zero. -/
theorem
    exists_nontrivialZero_not_mem_of_remainder_energy_gt_three_errors
    {S : Finset ℂ} {T beta a m L eta : ℝ}
    (hm : 0 < m)
    (hbeta : 0 ≤ beta)
    (ha : 1 ≤ a)
    (heta : 0 ≤ eta)
    (happrox :
      ∀ y ∈ Set.Icc a (a + L),
        ‖normalizedFiniteZeroClusterApproximationError T beta y‖ ≤ eta)
    (hsurplus :
      3 *
          (eta ^ 2 +
            (Real.exp (-beta * a) *
              zeroPackageClosedTermsUniformBound) ^ 2) <
        normalizedFiniteZeroClusterPsiRemainderWithoutJumpForwardGaussianSecondMoment
          S T beta a m L) :
    ∃ rho ∈ nontrivialZerosFinset T, rho ∉ S := by
  have henergy :=
    dynamicComplementFullMovingGaussianSecondMoment_ge_of_normalizedRemainder
      (S := S) (T := T) (beta := beta) (a := a) (m := m)
      (L := L) (eta := eta)
      (R :=
        normalizedFiniteZeroClusterPsiRemainderWithoutJumpForwardGaussianSecondMoment
          S T beta a m L)
      hm hbeta ha heta happrox le_rfl
  apply
    exists_nontrivialZero_not_mem_of_fullMovingGaussianSecondMoment_pos
  nlinarith

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
