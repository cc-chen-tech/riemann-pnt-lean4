import PrimeNumberTheorem.VKEdgeDynamicZeroPacket

open Complex

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

#check dynamicComplementZeroPacket
#check dynamicComplementPacketCoefficientMass
#check dynamicComplementGaussianMajorantEnergy
#check dynamicComplementPacketIndexSet
#check dynamicComplementFrozenGaussianSecondMoment
#check dynamicComplementCenteredFrozenGaussianSecondMoment

#check
  (finiteExponentialSum_phaseTwist_eq_shift :
    ∀ {ι : Type} [DecidableEq ι]
      (S : Finset ι) (c : ι → ℂ) (omega : ι → ℝ) (a t : ℝ),
      DirichletPolynomial.finiteExponentialSum S
          (DirichletPolynomial.phaseTwist c omega a) omega t =
        DirichletPolynomial.finiteExponentialSum S c omega (a + t))

#check
  (fourierKernel_normalizedGaussian :
    ∀ {m : ℝ}, 0 < m → ∀ xi : ℝ,
      DirichletPolynomial.fourierKernel (normalizedGaussian m) xi =
        (Real.exp (-m * xi ^ 2) : ℂ))

#check
  (dynamicComplementFrozenGaussianSecondMoment_le_majorant :
    ∀ (S : Finset ℂ) (T beta a : ℝ) (K : Finset ℕ)
      {m : ℝ}, 0 < m →
      dynamicComplementFrozenGaussianSecondMoment S T beta a K m ≤
        dynamicComplementGaussianMajorantEnergy S T beta a K m)

#check
  (dynamicComplementCenteredFrozenGaussianSecondMoment_le_majorant :
    ∀ (S : Finset ℂ) (T beta a : ℝ) (K : Finset ℕ)
      {m : ℝ}, 0 < m →
      dynamicComplementCenteredFrozenGaussianSecondMoment
          S T beta a K m ≤
        dynamicComplementGaussianMajorantEnergy S T beta a K m)

#check
  (dynamicComplementGaussianMajorantEnergy_le :
    ∀ (S : Finset ℂ) (T beta a : ℝ) (K : Finset ℕ)
      {m : ℝ}, 1 ≤ m →
      dynamicComplementGaussianMajorantEnergy S T beta a K m ≤
        MathlibAux.gaussianBucketSchurConstant *
          ∑ n ∈ K,
            dynamicComplementPacketCoefficientMass S T beta a n ^ 2)

#check
  (exists_absorbableDynamicComplementPacket_of_gaussianMajorantEnergy_gt :
    ∀ {S : Finset ℂ} {T beta a eta m : ℝ} {K : Finset ℕ},
      0 < eta →
      1 ≤ m →
      K.Nonempty →
      eta < dynamicComplementGaussianMajorantEnergy S T beta a K m →
      ∃ n ∈ K,
        eta /
              (MathlibAux.gaussianBucketSchurConstant *
                (K.card : ℝ)) <
            dynamicComplementPacketCoefficientMass S T beta a n ^ 2 ∧
          (dynamicComplementZeroPacket S T n).Nonempty ∧
          Disjoint S (dynamicComplementZeroPacket S T n) ∧
          dynamicComplementZeroPacket S T n ⊆
            nontrivialZerosFinset T ∧
          S.card <
            (S ∪ dynamicComplementZeroPacket S T n).card)

#check
  (exists_absorbableDynamicComplementPacket_of_frozenGaussianL2_gt :
    ∀ {S : Finset ℂ} {T beta a eta m : ℝ} {K : Finset ℕ},
      0 < eta →
      1 ≤ m →
      K.Nonempty →
      eta <
        dynamicComplementFrozenGaussianSecondMoment S T beta a K m →
      ∃ n ∈ K,
        eta /
              (MathlibAux.gaussianBucketSchurConstant *
                (K.card : ℝ)) <
            dynamicComplementPacketCoefficientMass S T beta a n ^ 2 ∧
          (dynamicComplementZeroPacket S T n).Nonempty ∧
          Disjoint S (dynamicComplementZeroPacket S T n) ∧
          dynamicComplementZeroPacket S T n ⊆
            nontrivialZerosFinset T ∧
          S.card <
            (S ∪ dynamicComplementZeroPacket S T n).card)

#check
  (exists_absorbableDynamicComplementPacket_of_centeredFrozenGaussianL2_gt :
    ∀ {S : Finset ℂ} {T beta a eta m : ℝ} {K : Finset ℕ},
      0 < eta →
      1 ≤ m →
      K.Nonempty →
      eta <
        dynamicComplementCenteredFrozenGaussianSecondMoment
          S T beta a K m →
      ∃ n ∈ K,
        eta /
              (MathlibAux.gaussianBucketSchurConstant *
                (K.card : ℝ)) <
            dynamicComplementPacketCoefficientMass S T beta a n ^ 2 ∧
          (dynamicComplementZeroPacket S T n).Nonempty ∧
          Disjoint S (dynamicComplementZeroPacket S T n) ∧
          dynamicComplementZeroPacket S T n ⊆
            nontrivialZerosFinset T ∧
          S.card <
            (S ∪ dynamicComplementZeroPacket S T n).card)

end VKEdgePiOverTwo
end PrimeNumberTheorem
