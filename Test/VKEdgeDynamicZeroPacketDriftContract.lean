import PrimeNumberTheorem.VKEdgeDynamicZeroPacketDrift

open Complex
open scoped BigOperators

open PrimeNumberTheorem
open PrimeNumberTheorem.VKEdgePiOverTwo

#check
  (dynamicComplementRealBand :
    ℝ → ℝ → ℂ → Prop)

#check
  (dynamicComplementRealBandZeroPacket :
    Finset ℂ → ℝ → ℝ → ℝ → ℕ → Finset ℂ)

#check
  (dynamicComplementOutsideRealBandZeroPacket :
    Finset ℂ → ℝ → ℝ → ℝ → ℕ → Finset ℂ)

#check
  (dynamicComplementRealBandPacketIndexSet :
    Finset ℂ → ℝ → ℝ → ℝ → Finset ℕ →
      Finset (Σ _n : ℕ, ℂ))

#check
  (dynamicComplementOutsideRealBandPacketIndexSet :
    Finset ℂ → ℝ → ℝ → ℝ → Finset ℕ →
      Finset (Σ _n : ℕ, ℂ))

#check
  (dynamicComplementRealBandPacketCoefficientMass :
    Finset ℂ → ℝ → ℝ → ℝ → ℝ → ℕ → ℝ)

#check
  (dynamicComplementMovingPacketContribution :
    Finset ℂ → ℝ → ℝ → ℝ → Finset ℕ → ℝ → ℂ)

#check
  (dynamicComplementRealBandMovingPacketContribution :
    Finset ℂ → ℝ → ℝ → ℝ → ℝ → Finset ℕ → ℝ → ℂ)

#check
  (dynamicComplementOutsideRealBandMovingPacketContribution :
    Finset ℂ → ℝ → ℝ → ℝ → ℝ → Finset ℕ → ℝ → ℂ)

#check
  (dynamicComplementMovingPacketContribution_eq_realBand_add_outside :
    ∀ (S : Finset ℂ) (T beta a delta : ℝ) (K : Finset ℕ) (y : ℝ),
      dynamicComplementMovingPacketContribution S T beta a K y =
        dynamicComplementRealBandMovingPacketContribution
            S T beta a delta K y +
          dynamicComplementOutsideRealBandMovingPacketContribution
            S T beta a delta K y)

#check
  (dynamicComplementFrozenPacketContribution :
    Finset ℂ → ℝ → ℝ → ℝ → Finset ℕ → ℝ → ℂ)

#check
  (dynamicComplementForwardMovingGaussianSecondMoment :
    Finset ℂ → ℝ → ℝ → ℝ → Finset ℕ → ℝ → ℝ → ℝ)

#check
  (dynamicComplementRealBandForwardMovingGaussianSecondMoment :
    Finset ℂ → ℝ → ℝ → ℝ → ℝ → Finset ℕ → ℝ → ℝ → ℝ)

#check
  (dynamicComplementOutsideRealBandForwardMovingGaussianSecondMoment :
    Finset ℂ → ℝ → ℝ → ℝ → ℝ → Finset ℕ → ℝ → ℝ → ℝ)

#check
  (dynamicComplementForwardMovingGaussianSecondMoment_le_realBand_add_outside :
    ∀ (S : Finset ℂ) (T beta a delta : ℝ) (K : Finset ℕ)
      {m L : ℝ},
      0 < m →
      dynamicComplementForwardMovingGaussianSecondMoment
          S T beta a K m L ≤
        2 * dynamicComplementRealBandForwardMovingGaussianSecondMoment
            S T beta a delta K m L +
          2 * dynamicComplementOutsideRealBandForwardMovingGaussianSecondMoment
            S T beta a delta K m L)

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

#check
  (exists_absorbableDynamicComplementRealBandPacket_of_forwardMovingGaussianL2_gt :
    ∀ {S : Finset ℂ} {T beta a eta m L delta : ℝ} {K : Finset ℕ},
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
      ∃ n ∈ K,
        eta / (MathlibAux.gaussianBucketSchurConstant * K.card) <
            dynamicComplementRealBandPacketCoefficientMass
              S T beta a delta n ^ 2 ∧
          (dynamicComplementRealBandZeroPacket
            S T beta delta n).Nonempty ∧
            Disjoint S
              (dynamicComplementRealBandZeroPacket
                S T beta delta n) ∧
              dynamicComplementRealBandZeroPacket
                  S T beta delta n ⊆
                nontrivialZerosFinset T ∧
                S.card <
                  (S ∪ dynamicComplementRealBandZeroPacket
                    S T beta delta n).card ∧
                  ∀ rho ∈ dynamicComplementRealBandZeroPacket
                      S T beta delta n,
                    dynamicComplementRealBand beta delta rho)

#check
  (exists_absorbableDynamicComplementRealBandPacket_of_fullMovingGaussianL2_gt :
    ∀ {S : Finset ℂ} {T beta a eta m L delta : ℝ} {K : Finset ℕ},
      0 < eta →
      1 ≤ m →
      0 ≤ L →
      0 ≤ delta →
      K.Nonempty →
      2 *
          (2 * eta +
            2 * (1 - Real.exp (-delta * L)) ^ 2 *
              (∑ n ∈ K,
                dynamicComplementRealBandPacketCoefficientMass
                  S T beta a delta n) ^ 2) +
          2 *
            dynamicComplementOutsideRealBandForwardMovingGaussianSecondMoment
              S T beta a delta K m L <
        dynamicComplementForwardMovingGaussianSecondMoment
          S T beta a K m L →
      ∃ n ∈ K,
        eta / (MathlibAux.gaussianBucketSchurConstant * K.card) <
            dynamicComplementRealBandPacketCoefficientMass
              S T beta a delta n ^ 2 ∧
          (dynamicComplementRealBandZeroPacket
            S T beta delta n).Nonempty ∧
            Disjoint S
              (dynamicComplementRealBandZeroPacket
                S T beta delta n) ∧
              dynamicComplementRealBandZeroPacket
                  S T beta delta n ⊆
                nontrivialZerosFinset T ∧
                S.card <
                  (S ∪ dynamicComplementRealBandZeroPacket
                    S T beta delta n).card ∧
                  ∀ rho ∈ dynamicComplementRealBandZeroPacket
                      S T beta delta n,
                    dynamicComplementRealBand beta delta rho)
