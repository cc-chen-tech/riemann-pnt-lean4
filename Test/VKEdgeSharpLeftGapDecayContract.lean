import PrimeNumberTheorem.VKEdgeSharpLeftGapDecay

open Complex MeasureTheory Set

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

#check
  (finiteZeroClusterReciprocalMultiplicityMass :
    Finset ℂ → (ℂ → ℕ) → ℝ)

#check
  (finiteZeroClusterReciprocalMultiplicityMass_nonneg :
    ∀ (S : Finset ℂ) (multiplicity : ℂ → ℕ),
      0 ≤ finiteZeroClusterReciprocalMultiplicityMass S multiplicity)

#check
  (norm_normalizedFiniteZeroClusterContribution_le_exp_leftGap :
    ∀ {S : Finset ℂ} {multiplicity : ℂ → ℕ}
      {beta delta a y : ℝ},
      0 ≤ delta →
      0 ≤ a →
      a ≤ y →
      (∀ rho ∈ S, rho.re ≤ beta - delta) →
      ‖normalizedFiniteZeroClusterContribution
          S multiplicity beta y‖ ≤
        Real.exp (-delta * a) *
          finiteZeroClusterReciprocalMultiplicityMass S multiplicity)

#check
  (normalizedFiniteZeroClusterContributionForwardGaussianSecondMoment_le_exp_leftGap :
    ∀ {S : Finset ℂ} {multiplicity : ℂ → ℕ}
      {beta delta a m L : ℝ},
      0 ≤ delta →
      0 ≤ a →
      0 < m →
      0 ≤ L →
      (∀ rho ∈ S, rho.re ≤ beta - delta) →
      (∫ t : ℝ in Set.Icc 0 L,
          normalizedGaussian m t *
            ‖normalizedFiniteZeroClusterContribution
              S multiplicity beta (a + t)‖ ^ 2) ≤
        (Real.exp (-delta * a) *
          finiteZeroClusterReciprocalMultiplicityMass S multiplicity) ^ 2)

#check
  (normalizedFiniteZeroClusterComplementContribution_empty_eq_selected_add_complement :
    ∀ {S : Finset ℂ} {T beta y : ℝ},
      S ⊆ nontrivialZerosFinset T →
      normalizedFiniteZeroClusterComplementContribution ∅ T beta y =
        normalizedFiniteZeroClusterContribution S
            (analyticOrderNatAt riemannZeta) beta y +
          normalizedFiniteZeroClusterComplementContribution S T beta y)

#check
  (normalizedFiniteZeroClusterComplementForwardGaussianSecondMoment_gt_quarter_of_leftGap :
    ∀ {S : Finset ℂ} {T beta delta a m L C : ℝ},
      S ⊆ nontrivialZerosFinset T →
      0 ≤ delta →
      0 ≤ a →
      0 < m →
      0 ≤ L →
      (∀ rho ∈ S, rho.re ≤ beta - delta) →
      C <
        ∫ t : ℝ in Set.Icc 0 L,
          normalizedGaussian m t *
            ‖normalizedFiniteZeroClusterComplementContribution
              ∅ T beta (a + t)‖ ^ 2 →
      (Real.exp (-delta * a) *
          finiteZeroClusterReciprocalMultiplicityMass
            S (analyticOrderNatAt riemannZeta)) ^ 2 ≤ C / 4 →
      C / 4 <
        ∫ t : ℝ in Set.Icc 0 L,
          normalizedGaussian m t *
            ‖normalizedFiniteZeroClusterComplementContribution
              S T beta (a + t)‖ ^ 2)

end VKEdgePiOverTwo
end PrimeNumberTheorem
