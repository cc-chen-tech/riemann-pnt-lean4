import PrimeNumberTheorem.VKEdgeInitialFullMovingEnergy

open Complex Filter MeasureTheory Set

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

#check
  (normalizedPsiError_sq_eq_norm_sq_mul_normalizedChebyshevPsiErrorAtExponent :
    ∀ (rho : ℂ) (y : ℝ),
      normalizedPsiError rho y ^ 2 =
        ‖rho‖ ^ 2 *
          ‖normalizedChebyshevPsiErrorAtExponent rho.re y‖ ^ 2)

#check (normalizedGaussian_sqScale_endpoint :
  ∀ {L : ℝ}, 0 < L →
    normalizedGaussian (L ^ 2) L =
      Real.exp (-(1 : ℝ) / 4) /
        (2 * Real.sqrt Real.pi * L))

#check (normalizedGaussian_sqScale_endpoint_le :
  ∀ {L t : ℝ}, 0 < L → t ∈ Set.Icc 0 L →
    normalizedGaussian (L ^ 2) L ≤
      normalizedGaussian (L ^ 2) t)

#check (normalizedPsiErrorForwardGaussianSecondMoment :
  ℂ → ℝ → ℝ → ℝ → ℝ)

#check
  (normalizedFiniteZeroClusterPsiRemainderWithoutJumpForwardGaussianSecondMoment_empty :
    ∀ (rho : ℂ) (T a m L : ℝ), rho ≠ 0 →
      normalizedFiniteZeroClusterPsiRemainderWithoutJumpForwardGaussianSecondMoment
          ∅ T rho.re a m L =
        (1 / ‖rho‖ ^ 2) *
          normalizedPsiErrorForwardGaussianSecondMoment rho a m L)

#check
  (normalizedPsiErrorForwardGaussianSecondMoment_ge_endpoint_mul_ordinary :
    ∀ (rho : ℂ) {a L : ℝ}, 0 < L →
      normalizedGaussian (L ^ 2) L *
          (∫ y : ℝ in Set.Icc a (a + L),
            normalizedPsiError rho y ^ 2) ≤
        normalizedPsiErrorForwardGaussianSecondMoment
          rho a (L ^ 2) L)

#check (initialEmptyClusterResidualGaussianL2Constant :
  ℝ → ℂ → ℕ → ℝ)

#check
  (exists_eventually_emptyClusterResidualForwardGaussianSecondMoment_gt :
    ∀ {ε : ℝ} {rho : ℂ} {sigma : ℝ},
      0 < ε →
      0 < rho.im →
      riemannZeta rho = 0 →
      1 / 2 < sigma →
      sigma < rho.re →
      rho.re < 1 →
      ∃ k : ℕ,
        riemannZeta (missingHarmonicContourCenter rho k) ≠ 0 ∧
        0 < initialEmptyClusterResidualGaussianL2Constant ε rho k ∧
        ∀ᶠ Y : ℝ in atTop,
          ∀ T : ℝ,
            initialEmptyClusterResidualGaussianL2Constant ε rho k <
              normalizedFiniteZeroClusterPsiRemainderWithoutJumpForwardGaussianSecondMoment
                ∅ T rho.re (Real.log Y)
                  ((ε * Real.log Y) ^ 2) (ε * Real.log Y))

end VKEdgePiOverTwo
end PrimeNumberTheorem
