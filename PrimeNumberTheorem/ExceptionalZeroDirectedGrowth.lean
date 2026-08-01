import PrimeNumberTheorem.ExceptionalZeroDetectOrCountSharp
import PrimeNumberTheorem.ZeroDensityCount

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

/-- Enlarge the recorded set by every truncated zero that is either not above
`Told` or not strictly to the right of `sigma`.

A witness outside this set is therefore simultaneously new, higher than
`Told`, and in the right strip `sigma < re rho`. -/
noncomputable def rightHigherExclusionSet
    (S : Finset ℂ) (Told sigma T : ℝ) : Finset ℂ :=
  S ∪ (nontrivialZerosFinset T).filter fun rho =>
    rho.im ≤ Told ∨ rho.re ≤ sigma

/-- A truncated zero outside `rightHigherExclusionSet` is a new positive-
ordinate zero in the Carlson right strip and above the old height cutoff. -/
theorem directedWitness_of_not_mem_rightHigherExclusionSet
    {S : Finset ℂ} {Told sigma T : ℝ} {rho : ℂ}
    (hTold : 0 ≤ Told)
    (hrhoT : rho ∈ nontrivialZerosFinset T)
    (hrhoNew : rho ∉ rightHigherExclusionSet S Told sigma T) :
    rho ∈ ZeroDensity.zeroDensityZerosFinset sigma T ∧
      Told < rho.im ∧ rho ∉ S := by
  have hrhoS : rho ∉ S := by
    intro hrhoS
    apply hrhoNew
    simp [rightHigherExclusionSet, hrhoS]
  have hrhoGood : ¬(rho.im ≤ Told ∨ rho.re ≤ sigma) := by
    intro hrhoBad
    apply hrhoNew
    simp [rightHigherExclusionSet, hrhoT, hrhoBad]
  have himLow : Told < rho.im := lt_of_not_ge (not_or.mp hrhoGood).1
  have hre : sigma < rho.re := lt_of_not_ge (not_or.mp hrhoGood).2
  have himPos : 0 < rho.im := lt_of_le_of_lt hTold himLow
  rcases mem_nontrivialZerosFinset.mp hrhoT with ⟨hzero, himT_abs⟩
  have himT : rho.im ≤ T := by
    simpa [abs_of_pos himPos] using himT_abs
  exact
    ⟨ZeroDensity.mem_zeroDensityZerosFinset.mpr
        ⟨hzero, himPos, himT, hre⟩,
      himLow, hrhoS⟩

/-- Positive complementary energy after excluding the recorded, low, and
non-right zeros produces a genuinely new right-strip zero at a higher
ordinate. -/
theorem exists_new_right_zero_above_of_fullMovingGaussianSecondMoment_pos
    {S : Finset ℂ} {Told sigma T beta a m L : ℝ}
    (hTold : 0 ≤ Told)
    (hpos :
      0 <
        dynamicComplementForwardMovingGaussianSecondMoment
          (rightHigherExclusionSet S Told sigma T) T beta a
          (dynamicComplementFullBucketSet
            (rightHigherExclusionSet S Told sigma T) T) m L) :
    ∃ rho,
      rho ∈ ZeroDensity.zeroDensityZerosFinset sigma T ∧
        Told < rho.im ∧ rho ∉ S := by
  rcases
      exists_nontrivialZero_not_mem_of_fullMovingGaussianSecondMoment_pos
        hpos with
    ⟨rho, hrhoT, hrhoNew⟩
  exact
    ⟨rho,
      directedWitness_of_not_mem_rightHigherExclusionSet
        hTold hrhoT hrhoNew⟩

/-- The explicit remainder-surplus endpoint, localized to a new right-strip
zero above `Told`.

The surplus is intentionally required after excluding all truncated low or
non-right zeros. Proving that this surplus persists is the remaining analytic
input; this theorem does not assume it implicitly. -/
theorem exists_new_right_zero_above_of_remainder_energy_gt_three_errors
    {S : Finset ℂ} {Told sigma T beta a m L eta : ℝ}
    (hTold : 0 ≤ Told)
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
          (rightHigherExclusionSet S Told sigma T) T beta a m L) :
    ∃ rho,
      rho ∈ ZeroDensity.zeroDensityZerosFinset sigma T ∧
        Told < rho.im ∧ rho ∉ S := by
  rcases
      exists_nontrivialZero_not_mem_of_remainder_energy_gt_three_errors
        hm hbeta ha heta happrox hsurplus with
    ⟨rho, hrhoT, hrhoNew⟩
  exact
    ⟨rho,
      directedWitness_of_not_mem_rightHigherExclusionSet
        hTold hrhoT hrhoNew⟩

/-- The directed witness strictly enlarges any recorded right-strip zero set
while preserving membership in the same Carlson counting finset. -/
theorem exists_strictly_larger_rightZeroSet_of_remainder_energy_gt_three_errors
    {S : Finset ℂ} {Told sigma T beta a m L eta : ℝ}
    (hS : S ⊆ ZeroDensity.zeroDensityZerosFinset sigma T)
    (hTold : 0 ≤ Told)
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
          (rightHigherExclusionSet S Told sigma T) T beta a m L) :
    ∃ S' : Finset ℂ,
      S ⊆ S' ∧
        S.card < S'.card ∧
          S' ⊆ ZeroDensity.zeroDensityZerosFinset sigma T ∧
            ∃ rho ∈ S', Told < rho.im ∧ rho ∉ S := by
  rcases
      exists_new_right_zero_above_of_remainder_energy_gt_three_errors
        hTold hm hbeta ha heta happrox hsurplus with
    ⟨rho, hrhoRight, hrhoHigh, hrhoNew⟩
  refine
    ⟨insert rho S, Finset.subset_insert rho S, ?_, ?_,
      rho, Finset.mem_insert_self rho S, hrhoHigh, hrhoNew⟩
  · simpa [Finset.card_insert_of_notMem hrhoNew] using
      Nat.lt_succ_self S.card
  · intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hrhoRight
    · exact hS hz

end VKEdgePiOverTwo
end PrimeNumberTheorem
