import PrimeNumberTheorem.ExceptionalZeroDetectOrCount
import PrimeNumberTheorem.VKEdgeDistinctComplementWitness

open Complex

namespace PrimeNumberTheorem
namespace ExceptionalZeroDetectOrCount

/-!
# Sharp energy to one strict recorded-zero update

This module only composes the Sharp complementary-energy witness extraction
with the one-window finite-set growth adapter.  All analytic estimates remain
in `VKEdgeDistinctComplementWitness`.
-/

/-- Positive full complementary moving Gaussian energy forces one strict
growth step of the recorded genuine-zero set. -/
theorem
    exists_strictly_larger_recordedZeroSet_of_fullMovingGaussianSecondMoment_pos
    {S : Finset ℂ} {T beta a m L : ℝ}
    (hS : S ⊆ nontrivialZerosFinset T)
    (hpos :
      0 <
        VKEdgePiOverTwo.dynamicComplementForwardMovingGaussianSecondMoment
          S T beta a (VKEdgePiOverTwo.dynamicComplementFullBucketSet S T) m L) :
    ∃ S' : Finset ℂ,
      S ⊆ S' ∧
        S.card < S'.card ∧
        S' ⊆ nontrivialZerosFinset T :=
  exists_strictly_larger_recordedZeroSet_of_new_nontrivialZero hS
    (VKEdgePiOverTwo.exists_nontrivialZero_not_mem_of_fullMovingGaussianSecondMoment_pos
      hpos)

/-- A selected-cluster remainder surplus above three times the approximation
and closed-term budgets forces one strict growth step of the recorded
genuine-zero set. -/
theorem
    exists_strictly_larger_recordedZeroSet_of_remainder_energy_gt_three_errors
    {S : Finset ℂ} {T beta a m L eta : ℝ}
    (hS : S ⊆ nontrivialZerosFinset T)
    (hm : 0 < m)
    (hbeta : 0 ≤ beta)
    (ha : 1 ≤ a)
    (heta : 0 ≤ eta)
    (happrox :
      ∀ y ∈ Set.Icc a (a + L),
        ‖VKEdgePiOverTwo.normalizedFiniteZeroClusterApproximationError T beta y‖ ≤
          eta)
    (hsurplus :
      3 *
          (eta ^ 2 +
            (Real.exp (-beta * a) *
              VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound) ^ 2) <
        VKEdgePiOverTwo.normalizedFiniteZeroClusterPsiRemainderWithoutJumpForwardGaussianSecondMoment
          S T beta a m L) :
    ∃ S' : Finset ℂ,
      S ⊆ S' ∧
        S.card < S'.card ∧
        S' ⊆ nontrivialZerosFinset T :=
  exists_strictly_larger_recordedZeroSet_of_new_nontrivialZero hS
    (VKEdgePiOverTwo.exists_nontrivialZero_not_mem_of_remainder_energy_gt_three_errors
      hm hbeta ha heta happrox hsurplus)

end ExceptionalZeroDetectOrCount
end PrimeNumberTheorem
