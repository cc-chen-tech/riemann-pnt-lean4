import PrimeNumberTheorem.ExceptionalZeroDetectOrCountQuantitativeMass

open Complex
open scoped BigOperators

namespace PrimeNumberTheorem
namespace ExceptionalZeroDetectOrCount

open VKEdgePiOverTwo

#check
  (dynamicComplementRealBandZeroPacket_nonempty_of_coefficientMass_pos :
    ∀ (S : Finset ℂ) (T beta a delta : ℝ) (n : ℕ),
      0 <
          dynamicComplementRealBandPacketCoefficientMass
            S T beta a delta n →
        (dynamicComplementRealBandZeroPacket
          S T beta delta n).Nonempty)

#check
  (sum_sq_lt_card_sq_mul_sq_of_pointwise_le :
    ∀ {ι : Type*} [DecidableEq ι]
      (P : Finset ι) (weight : ι → ℝ) {lambda U : ℝ},
      (∀ rho ∈ P, 0 ≤ weight rho) →
      (∀ rho ∈ P, weight rho ≤ U) →
      lambda < (∑ rho ∈ P, weight rho) ^ 2 →
      lambda < (P.card : ℝ) ^ 2 * U ^ 2)

#check
  (dynamicComplementRealBandPacketCoefficientMass_sq_lt_card_sq_mul_sq :
    ∀ (S : Finset ℂ) (T beta a delta : ℝ) (n : ℕ)
      {lambda U : ℝ},
      (∀ rho ∈ dynamicComplementRealBandZeroPacket
          S T beta delta n,
        ‖finiteZeroClusterCoefficientAt
          (analyticOrderNatAt riemannZeta) beta a rho‖ ≤ U) →
      lambda <
          dynamicComplementRealBandPacketCoefficientMass
            S T beta a delta n ^ 2 →
      lambda <
          ((dynamicComplementRealBandZeroPacket
            S T beta delta n).card : ℝ) ^ 2 * U ^ 2)

#check
  (exists_quantitativeRealBandPacket_of_forwardMovingGaussianL2_gt :
    ∀ {S : Finset ℂ} {T beta a eta m L delta : ℝ}
      {K : Finset ℕ},
      S ⊆ nontrivialZerosFinset T →
      0 < eta →
      1 ≤ m →
      0 ≤ L →
      0 ≤ delta →
      K.Nonempty →
      2 * eta +
          2 * (1 - Real.exp (-delta * L)) ^ 2 *
            (∑ n ∈ K,
              dynamicComplementRealBandPacketCoefficientMass
                S T beta a delta n) ^ 2 <
        dynamicComplementRealBandForwardMovingGaussianSecondMoment
          S T beta a delta K m L →
      ∃ n ∈ K, ∃ P : Finset ℂ,
        P = dynamicComplementRealBandZeroPacket
            S T beta delta n ∧
        eta / (MathlibAux.gaussianBucketSchurConstant * K.card) <
            dynamicComplementRealBandPacketCoefficientMass
              S T beta a delta n ^ 2 ∧
        P ⊆ nontrivialZerosFinset T ∧
        Disjoint S P ∧
        (∀ rho ∈ P,
          beta - delta ≤ rho.re ∧ rho.re ≤ beta) ∧
        (∀ rho ∈ P,
          (n : ℝ) ≤ |rho.im| ∧ |rho.im| < (n : ℝ) + 1) ∧
        P.Nonempty ∧
        S.card < (S ∪ P).card)

end ExceptionalZeroDetectOrCount
end PrimeNumberTheorem
