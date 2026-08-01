import PrimeNumberTheorem.VKEdgeRightHigherSharpBlocker

open Complex
open scoped ComplexConjugate

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

#check
  (mem_rightHigherExclusionSet_of_im_le :
    ∀ {S : Finset ℂ} {Told sigma T : ℝ} {rho : ℂ},
      rho ∈ nontrivialZerosFinset T →
      rho.im ≤ Told →
      rho ∈ rightHigherExclusionSet S Told sigma T)

#check
  (targetPair_mem_rightHigherExclusionSet :
    ∀ {S : Finset ℂ} {Told sigma T : ℝ} {rho : ℂ},
      RiemannHypothesis.IsNontrivialZero rho →
      0 < rho.im →
      |rho.im| ≤ T →
      rho.im ≤ Told →
      rho ∈ rightHigherExclusionSet S Told sigma T ∧
        conj rho ∈ rightHigherExclusionSet S Told sigma T)

#check
  (targetPair_not_mem_dynamicComplementZeroSet :
    ∀ {S : Finset ℂ} {Told sigma T : ℝ} {rho : ℂ},
      RiemannHypothesis.IsNontrivialZero rho →
      0 < rho.im →
      |rho.im| ≤ T →
      rho.im ≤ Told →
      rho ∉
          dynamicComplementZeroSet
            (rightHigherExclusionSet S Told sigma T) T ∧
        conj rho ∉
          dynamicComplementZeroSet
            (rightHigherExclusionSet S Told sigma T) T)

#check
  (two_mul_currentSharpL2Constant_lt_targetPairLeadingEnergy :
    ∀ {epsilon : ℝ} {rho : ℂ} {k : ℕ},
      0 < epsilon →
      rho ≠ 1 →
      riemannZeta rho = 0 →
      2 * centeredSharpenedSweptOrdinaryL2Constant epsilon rho k <
        2 * epsilon *
          (analyticOrderNatAt riemannZeta rho : ℝ) ^ 2)

#check
  (rightHigherFullMovingGaussianSecondMoment_eq_zero_of_no_new_right_zero :
    ∀ {S : Finset ℂ} {Told sigma T beta a m L : ℝ},
      (∀ rho ∈ nontrivialZerosFinset T,
        rho ∈ S ∨ rho.im ≤ Told ∨ rho.re ≤ sigma) →
      dynamicComplementForwardMovingGaussianSecondMoment
          (rightHigherExclusionSet S Told sigma T) T beta a
          (dynamicComplementFullBucketSet
            (rightHigherExclusionSet S Told sigma T) T) m L = 0)

#check
  (targetPair_absorbed_and_fullMovingEnergy_zero_of_no_new_right_zero :
    ∀ {S : Finset ℂ} {Told sigma T beta a m L : ℝ} {rho : ℂ},
      RiemannHypothesis.IsNontrivialZero rho →
      0 < rho.im →
      |rho.im| ≤ T →
      rho.im ≤ Told →
      (∀ z ∈ nontrivialZerosFinset T,
        z ∈ S ∨ z.im ≤ Told ∨ z.re ≤ sigma) →
      (rho ∈ rightHigherExclusionSet S Told sigma T ∧
          conj rho ∈ rightHigherExclusionSet S Told sigma T) ∧
        dynamicComplementForwardMovingGaussianSecondMoment
          (rightHigherExclusionSet S Told sigma T) T beta a
          (dynamicComplementFullBucketSet
            (rightHigherExclusionSet S Told sigma T) T) m L = 0)

end VKEdgePiOverTwo
end PrimeNumberTheorem
