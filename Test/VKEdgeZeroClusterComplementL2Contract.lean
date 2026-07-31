import PrimeNumberTheorem.VKEdgeZeroClusterComplementL2

open Complex Filter Set

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

#check normalizedEqualRealPartComplementContribution
#check normalizedEqualRealPartComplementSecondMoment

#check
  (normalizedFiniteZeroClusterComplementContribution_equalRealPart :
    ∀ (T beta y : ℝ),
      normalizedFiniteZeroClusterComplementContribution
          (ZeroForcedOscillation.equalRealPartZeroPackage T beta)
          T beta y =
        normalizedEqualRealPartComplementContribution T beta y)

#check
  (exists_uniform_norm_normalizedEqualRealPartComplementContribution_le :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {T beta delta y : ℝ},
        4 ≤ T →
        0 ≤ y →
        (∀ rho ∈ ZeroForcedOscillation.complementaryZeroPackage T beta,
          rho.re ≤ beta - delta) →
        ‖normalizedEqualRealPartComplementContribution T beta y‖ ≤
          Real.exp (-delta * y) *
            (C * (1 + Real.log (T + 6)) ^ 2))

#check
  (exists_uniform_normalizedEqualRealPartComplementSecondMoment_le :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {T beta delta a L : ℝ},
        4 ≤ T →
        0 ≤ delta →
        0 ≤ a →
        0 ≤ L →
        T ∈ Set.Icc (Real.exp (a / 2)) (Real.exp (a / 2) + 1) →
        (∀ rho ∈ ZeroForcedOscillation.complementaryZeroPackage T beta,
          rho.re ≤ beta - delta) →
        normalizedEqualRealPartComplementSecondMoment T beta a L ≤
          L * (Real.exp (-delta * a) * (C * (4 + a) ^ 2)) ^ 2)

#check
  (eventually_normalizedEqualRealPartComplementSecondMoment_lt :
    ∀ {beta delta L eta : ℝ},
      0 < delta →
      0 ≤ L →
      0 < eta →
      ∀ᶠ a in atTop,
        ∀ T ∈ Set.Icc (Real.exp (a / 2)) (Real.exp (a / 2) + 1),
          4 ≤ T →
          (∀ rho ∈ ZeroForcedOscillation.complementaryZeroPackage T beta,
            rho.re ≤ beta - delta) →
          normalizedEqualRealPartComplementSecondMoment T beta a L < eta)

#check
  (normSq_normalizedFiniteZeroClusterPsiRemainderWithoutJump_le_components :
    ∀ (S : Finset ℂ) (T beta y : ℝ),
      ‖normalizedFiniteZeroClusterPsiRemainderWithoutJump S T beta y‖ ^ 2 ≤
        3 *
          (‖normalizedFiniteZeroClusterComplementContribution S T beta y‖ ^ 2 +
            ‖normalizedFiniteZeroClusterApproximationError T beta y‖ ^ 2 +
            ‖normalizedZeroPackageClosedTerms beta y‖ ^ 2))

end VKEdgePiOverTwo
end PrimeNumberTheorem
