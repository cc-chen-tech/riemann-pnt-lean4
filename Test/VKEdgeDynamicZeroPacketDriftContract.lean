import PrimeNumberTheorem.VKEdgeDynamicZeroPacketDrift

open Complex
open scoped BigOperators

open PrimeNumberTheorem
open PrimeNumberTheorem.VKEdgePiOverTwo

#check
  (dynamicComplementMovingPacketContribution :
    Finset ℂ → ℝ → ℝ → ℝ → Finset ℕ → ℝ → ℂ)

#check
  (dynamicComplementFrozenPacketContribution :
    Finset ℂ → ℝ → ℝ → ℝ → Finset ℕ → ℝ → ℂ)

#check
  (dynamicComplementForwardMovingGaussianSecondMoment :
    Finset ℂ → ℝ → ℝ → ℝ → Finset ℕ → ℝ → ℝ → ℝ)

#check
  (norm_dynamicComplementMovingPacketContribution_sub_frozen_le :
    ∀ {S : Finset ℂ} {T beta a delta y : ℝ} {K : Finset ℕ},
      0 ≤ delta →
      a ≤ y →
      (∀ n ∈ K, ∀ rho ∈ dynamicComplementZeroPacket S T n,
        beta - delta ≤ rho.re ∧ rho.re ≤ beta) →
      ‖dynamicComplementMovingPacketContribution S T beta a K y -
          dynamicComplementFrozenPacketContribution S T beta a K y‖ ≤
        (1 - Real.exp (-delta * (y - a))) *
          ∑ n ∈ K, dynamicComplementPacketCoefficientMass S T beta a n)

#check
  (dynamicComplementForwardMovingGaussianSecondMoment_le_centeredFrozen :
    ∀ {S : Finset ℂ} {T beta a m L delta : ℝ} {K : Finset ℕ},
      0 < m →
      0 ≤ L →
      0 ≤ delta →
      (∀ n ∈ K, ∀ rho ∈ dynamicComplementZeroPacket S T n,
        beta - delta ≤ rho.re ∧ rho.re ≤ beta) →
      dynamicComplementForwardMovingGaussianSecondMoment
          S T beta a K m L ≤
        2 * dynamicComplementCenteredFrozenGaussianSecondMoment
            S T beta a K m +
          2 * (1 - Real.exp (-delta * L)) ^ 2 *
            (∑ n ∈ K,
              dynamicComplementPacketCoefficientMass S T beta a n) ^ 2)

#check
  (exists_absorbableDynamicComplementPacket_of_forwardMovingGaussianL2_gt :
    ∀ {S : Finset ℂ} {T beta a eta m L delta : ℝ} {K : Finset ℕ},
      0 < eta →
      1 ≤ m →
      0 ≤ L →
      0 ≤ delta →
      K.Nonempty →
      (∀ n ∈ K, ∀ rho ∈ dynamicComplementZeroPacket S T n,
        beta - delta ≤ rho.re ∧ rho.re ≤ beta) →
      2 * eta +
          2 * (1 - Real.exp (-delta * L)) ^ 2 *
            (∑ n ∈ K,
              dynamicComplementPacketCoefficientMass S T beta a n) ^ 2 <
        dynamicComplementForwardMovingGaussianSecondMoment
          S T beta a K m L →
      ∃ n ∈ K,
        eta / (MathlibAux.gaussianBucketSchurConstant * K.card) <
            dynamicComplementPacketCoefficientMass S T beta a n ^ 2 ∧
          (dynamicComplementZeroPacket S T n).Nonempty ∧
            Disjoint S (dynamicComplementZeroPacket S T n) ∧
              dynamicComplementZeroPacket S T n ⊆
                nontrivialZerosFinset T ∧
                S.card <
                  (S ∪ dynamicComplementZeroPacket S T n).card)
