import PrimeNumberTheorem.VKEdgeDynamicMaximalLayer

open Complex

open PrimeNumberTheorem
open PrimeNumberTheorem.VKEdgePiOverTwo

#check
  (dynamicComplementZeroSet :
    Finset ℂ → ℝ → Finset ℂ)

#check
  (dynamicMaximalComplementRealPart :
    Finset ℂ → ℝ → ℝ)

#check
  (dynamicMaximalRealPartZeroLayer :
    Finset ℂ → ℝ → Finset ℂ)

#check
  (dynamicBelowMaximalRealPartZeroSet :
    Finset ℂ → ℝ → Finset ℂ)

#check
  (dynamicMaximalComplementRealPartGap :
    Finset ℂ → ℝ → ℝ)

#check
  (dynamicMaximalComplementBandWidth :
    Finset ℂ → ℝ → ℝ)

#check
  (re_le_dynamicMaximalComplementRealPart :
    ∀ {S : Finset ℂ} {T : ℝ} {rho : ℂ},
      rho ∈ dynamicComplementZeroSet S T →
        rho.re ≤ dynamicMaximalComplementRealPart S T)

#check
  (mem_dynamicMaximalRealPartZeroLayer :
    ∀ {S : Finset ℂ} {T : ℝ} {rho : ℂ},
      rho ∈ dynamicMaximalRealPartZeroLayer S T ↔
        rho ∈ dynamicComplementZeroSet S T ∧
          rho.re = dynamicMaximalComplementRealPart S T)

#check
  (dynamicMaximalRealPartZeroLayer_nonempty :
    ∀ (S : Finset ℂ) (T : ℝ),
      (dynamicComplementZeroSet S T).Nonempty →
        (dynamicMaximalRealPartZeroLayer S T).Nonempty)

#check
  (mem_dynamicBelowMaximalRealPartZeroSet :
    ∀ {S : Finset ℂ} {T : ℝ} {rho : ℂ},
      rho ∈ dynamicBelowMaximalRealPartZeroSet S T ↔
        rho ∈ dynamicComplementZeroSet S T ∧
          rho.re < dynamicMaximalComplementRealPart S T)

#check
  (dynamicMaximalComplementRealPartGap_pos :
    ∀ (S : Finset ℂ) (T : ℝ),
      0 < dynamicMaximalComplementRealPartGap S T)

#check
  (re_le_dynamicMaximalComplementRealPart_sub_gap :
    ∀ {S : Finset ℂ} {T : ℝ} {rho : ℂ},
      rho ∈ dynamicBelowMaximalRealPartZeroSet S T →
        rho.re ≤
          dynamicMaximalComplementRealPart S T -
            dynamicMaximalComplementRealPartGap S T)

#check
  (dynamicMaximalComplementBandWidth_pos :
    ∀ (S : Finset ℂ) (T : ℝ),
      0 < dynamicMaximalComplementBandWidth S T)

#check
  (dynamicComplementRealBand_iff_re_eq_dynamicMaximal :
    ∀ {S : Finset ℂ} {T : ℝ} {rho : ℂ},
      rho ∈ dynamicComplementZeroSet S T →
        (dynamicComplementRealBand
            (dynamicMaximalComplementRealPart S T)
            (dynamicMaximalComplementBandWidth S T) rho ↔
          rho.re = dynamicMaximalComplementRealPart S T))

#check
  (re_le_dynamicMaximal_sub_gap_of_not_realBand :
    ∀ {S : Finset ℂ} {T : ℝ} {rho : ℂ},
      rho ∈ dynamicComplementZeroSet S T →
        (¬ dynamicComplementRealBand
          (dynamicMaximalComplementRealPart S T)
          (dynamicMaximalComplementBandWidth S T) rho) →
          rho.re ≤
            dynamicMaximalComplementRealPart S T -
              dynamicMaximalComplementRealPartGap S T)

#check
  (re_le_dynamicMaximal_sub_gap_of_mem_outsidePacket :
    ∀ {S : Finset ℂ} {T : ℝ} {n : ℕ} {rho : ℂ},
      rho ∈ dynamicComplementOutsideRealBandZeroPacket
          S T
          (dynamicMaximalComplementRealPart S T)
          (dynamicMaximalComplementBandWidth S T) n →
        rho.re ≤
          dynamicMaximalComplementRealPart S T -
            dynamicMaximalComplementRealPartGap S T)

#check
  (dynamicMaximalOutsidePacketCoefficientMass :
    Finset ℂ → ℝ → ℝ → Finset ℕ → ℝ)

#check
  (dynamicMaximalOutsideReciprocalMultiplicityMass :
    Finset ℂ → ℝ → Finset ℕ → ℝ)

#check
  (norm_dynamicMaximalOutsideMovingPacketContribution_le :
    ∀ {S : Finset ℂ} {T a t : ℝ} {K : Finset ℕ},
      0 ≤ t →
        ‖dynamicComplementOutsideRealBandMovingPacketContribution
            S T
            (dynamicMaximalComplementRealPart S T) a
            (dynamicMaximalComplementBandWidth S T) K (a + t)‖ ≤
          Real.exp (-dynamicMaximalComplementRealPartGap S T * t) *
            dynamicMaximalOutsidePacketCoefficientMass S T a K)

#check
  (dynamicMaximalOutsidePacketCoefficientMass_le_exp_gap_mul_reciprocal :
    ∀ (S : Finset ℂ) (T a : ℝ) (K : Finset ℕ),
      0 ≤ a →
        dynamicMaximalOutsidePacketCoefficientMass S T a K ≤
          Real.exp (-dynamicMaximalComplementRealPartGap S T * a) *
            dynamicMaximalOutsideReciprocalMultiplicityMass S T K)

#check
  (dynamicMaximalOutsideReciprocalMultiplicityMass_le_card_mul_global :
    ∀ (S : Finset ℂ) (T : ℝ) (K : Finset ℕ),
      dynamicMaximalOutsideReciprocalMultiplicityMass S T K ≤
        (K.card : ℝ) *
          ExplicitFormulaAux.globalReciprocalZeroMultiplicity T)

#check
  (dynamicMaximalOutsideForwardMovingGaussianSecondMoment_le_coefficientMass_sq :
    ∀ (S : Finset ℂ) (T a : ℝ) (K : Finset ℕ) {m L : ℝ},
      0 < m →
        dynamicComplementOutsideRealBandForwardMovingGaussianSecondMoment
            S T
            (dynamicMaximalComplementRealPart S T) a
            (dynamicMaximalComplementBandWidth S T) K m L ≤
          dynamicMaximalOutsidePacketCoefficientMass S T a K ^ 2)

#check
  (dynamicMaximalOutsideForwardMovingGaussianSecondMoment_le_exp_gap_sq :
    ∀ (S : Finset ℂ) (T a : ℝ) (K : Finset ℕ) {m L : ℝ},
      0 < m →
        0 ≤ a →
          dynamicComplementOutsideRealBandForwardMovingGaussianSecondMoment
              S T
              (dynamicMaximalComplementRealPart S T) a
              (dynamicMaximalComplementBandWidth S T) K m L ≤
            (Real.exp (-dynamicMaximalComplementRealPartGap S T * a) *
              dynamicMaximalOutsideReciprocalMultiplicityMass S T K) ^ 2)

#check
  (exists_dynamicMaximalOutsideForwardMovingGaussianSecondMoment_le_log_sq :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : Finset ℂ) (T a : ℝ) (K : Finset ℕ) {m L : ℝ},
        4 ≤ T →
          0 ≤ a →
            0 < m →
              dynamicComplementOutsideRealBandForwardMovingGaussianSecondMoment
                  S T
                  (dynamicMaximalComplementRealPart S T) a
                  (dynamicMaximalComplementBandWidth S T) K m L ≤
                (Real.exp
                    (-dynamicMaximalComplementRealPartGap S T * a) *
                  ((K.card : ℝ) *
                    (C * (1 + Real.log (T + 6)) ^ 2))) ^ 2)

#check
  (exists_uniformDynamicMaximalLayerAbsorption_of_fullMovingGaussianL2_gt :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {S : Finset ℂ} {T a eta m L : ℝ} {K : Finset ℕ},
        4 ≤ T →
          0 ≤ a →
            0 < eta →
              1 ≤ m →
                0 ≤ L →
                  K.Nonempty →
                    2 *
                        (2 * eta +
                          2 *
                            (1 - Real.exp
                              (-dynamicMaximalComplementBandWidth S T * L)) ^ 2 *
                            (∑ n ∈ K,
                              dynamicComplementRealBandPacketCoefficientMass
                                S T
                                (dynamicMaximalComplementRealPart S T) a
                                (dynamicMaximalComplementBandWidth S T) n) ^ 2) +
                        2 *
                          (Real.exp
                              (-dynamicMaximalComplementRealPartGap S T * a) *
                            ((K.card : ℝ) *
                              (C * (1 + Real.log (T + 6)) ^ 2))) ^ 2 <
                      dynamicComplementForwardMovingGaussianSecondMoment
                        S T
                        (dynamicMaximalComplementRealPart S T) a K m L →
                    ∃ n ∈ K,
                      eta /
                          (MathlibAux.gaussianBucketSchurConstant * K.card) <
                          dynamicComplementRealBandPacketCoefficientMass
                            S T
                            (dynamicMaximalComplementRealPart S T) a
                            (dynamicMaximalComplementBandWidth S T) n ^ 2 ∧
                        (dynamicComplementRealBandZeroPacket
                          S T
                          (dynamicMaximalComplementRealPart S T)
                          (dynamicMaximalComplementBandWidth S T) n).Nonempty ∧
                          Disjoint S
                            (dynamicComplementRealBandZeroPacket
                              S T
                              (dynamicMaximalComplementRealPart S T)
                              (dynamicMaximalComplementBandWidth S T) n) ∧
                            dynamicComplementRealBandZeroPacket
                                S T
                                (dynamicMaximalComplementRealPart S T)
                                (dynamicMaximalComplementBandWidth S T) n ⊆
                              nontrivialZerosFinset T ∧
                              S.card <
                                (S ∪ dynamicComplementRealBandZeroPacket
                                  S T
                                  (dynamicMaximalComplementRealPart S T)
                                  (dynamicMaximalComplementBandWidth S T) n).card ∧
                                ∀ rho ∈ dynamicComplementRealBandZeroPacket
                                    S T
                                    (dynamicMaximalComplementRealPart S T)
                                    (dynamicMaximalComplementBandWidth S T) n,
                                  rho.re =
                                    dynamicMaximalComplementRealPart S T)
