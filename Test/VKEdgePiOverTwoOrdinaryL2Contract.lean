import PrimeNumberTheorem.VKEdgePiOverTwoOrdinaryL2

open Complex Filter MeasureTheory Polynomial Set Topology

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

#check polynomialGaussianEnvelopeConstant
#check projectedPsiKernelAtCenterEnvelopeConstant
#check centeredSharpenedProjectedPsiKernelEnvelopeConstant
#check centeredNormalizedWindowOrdinarySecondMoment

#check (gaussianDerivativeExpBound_nonneg :
  ∀ k : ℕ, 0 ≤ gaussianDerivativeExpBound k)

#check (polynomialGaussianEnvelopeConstant_nonneg :
  ∀ A : ℂ[X], 0 ≤ polynomialGaussianEnvelopeConstant A)

#check (polynomialGaussianKernel_add_deriv_norm_le_scaled_exp_abs_mul :
  ∀ (A : ℂ[X]) {m : ℝ}, 1 ≤ m → ∀ t : ℝ,
    ‖polynomialGaussianKernel A m t‖ +
        ‖polynomialGaussianKernelDeriv A m t‖ ≤
      polynomialGaussianEnvelopeConstant A *
        Real.exp |(Real.sqrt m)⁻¹ * t| *
        normalizedGaussian m t)

#check (exp_scaled_abs_mul_normalizedGaussian_le_exp_one_div_sqrt :
  ∀ {m : ℝ}, 1 ≤ m → ∀ t : ℝ,
    Real.exp |(Real.sqrt m)⁻¹ * t| * normalizedGaussian m t ≤
      Real.exp 1 / Real.sqrt m)

#check (projectedPsiKernelAtCenterEnvelopeConstant_nonneg :
  ∀ (A : ℂ[X]) (w : ℂ),
    0 ≤ projectedPsiKernelAtCenterEnvelopeConstant A w)

#check (projectedPsiKernelAtCenter_abs_le_scaled_exp_abs_mul :
  ∀ (q : ℝ) (A : ℂ[X]) {w : ℂ}, w ≠ 0 →
    ∀ m : ℝ, 1 ≤ m → ∀ y : ℝ,
      |projectedPsiKernelAtCenter q A w m y| ≤
        projectedPsiKernelAtCenterEnvelopeConstant A w *
          Real.exp |(Real.sqrt m)⁻¹ * (q * m - y)| *
          normalizedGaussian m (q * m - y))

#check (relativeProjectedPsiKernelAtCenterEnvelopeConstant_nonneg :
  ∀ (A : ℂ[X]) (target center c : ℂ),
    0 ≤ relativeProjectedPsiKernelAtCenterEnvelopeConstant
      A target center c)

#check (centeredSharpenedProjectedPsiKernelEnvelopeConstant_pos :
  ∀ (q : ℝ) (rho : ℂ) (k : ℕ),
    0 < centeredSharpenedProjectedPsiKernelEnvelopeConstant q rho k)

#check (centeredSharpenedProjectedPsiKernel_abs_le_inv_sqrt :
  ∀ (q : ℝ) {rho : ℂ} {k : ℕ}, rho ≠ 0 → 0 < rho.im →
    ∀ m : ℝ, 1 ≤ m → ∀ y : ℝ,
      |centeredSharpenedProjectedPsiKernel q rho k m y| ≤
        centeredSharpenedProjectedPsiKernelEnvelopeConstant q rho k /
          Real.sqrt m)

#check (centeredNormalizedWindowOrdinarySecondMoment_eq :
  ∀ (q d : ℝ) (rho : ℂ) (m : ℝ),
    centeredNormalizedWindowOrdinarySecondMoment q d rho m =
      ∫ y : ℝ in localizedGaussianLogWindow q d m,
        ‖rho‖ ^ 2 *
          (chebyshevPsi (Real.exp y) - Real.exp y) ^ 2 *
          Real.exp (-2 * rho.re * y))

#check (ordinarySecondMoment_lower_of_weightedSecondMoment :
  ∀ {q d : ℝ} {rho : ℂ} {kernel : ℝ → ℝ → ℝ}
      {m C2 K : ℝ},
    1 ≤ m →
    (∀ y ∈ localizedGaussianLogWindow q d m,
      |kernel m y| ≤ K / Real.sqrt m) →
    IntegrableOn
      (fun y => normalizedPsiError rho y ^ 2 * |kernel m y|)
      (localizedGaussianLogWindow q d m) →
    IntegrableOn
      (fun y => normalizedPsiError rho y ^ 2)
      (localizedGaussianLogWindow q d m) →
    C2 < centeredNormalizedWindowSecondMoment q d rho kernel m →
    C2 * Real.sqrt m <
      K * centeredNormalizedWindowOrdinarySecondMoment q d rho m)

#check (
  eventually_centeredSharpenedNormalizedPsiError_ordinarySecondMoment_gt :
  ∀ {q d : ℝ} {rho : ℂ} {k : ℕ},
    16 ≤ q → 0 < d → d < q → 16 * (q + d) ≤ d ^ 2 →
    0 < rho.re → rho.re < 1 → 0 < rho.im →
    riemannZeta rho = 0 →
    riemannZeta (missingHarmonicContourCenter rho k) ≠ 0 →
    ∀ᶠ m : ℝ in atTop,
      centeredSharpenedOrdinaryL2Constant q rho k * Real.sqrt m <
        centeredNormalizedWindowOrdinarySecondMoment q d rho m)

#check (exists_eventually_ordinarySecondMoment_in_epsilonLogWindow_gt :
  ∀ {ε : ℝ} {rho : ℂ} {sigma : ℝ},
    0 < ε → 0 < rho.im → riemannZeta rho = 0 →
    1 / 2 < sigma → sigma < rho.re → rho.re < 1 →
    ∃ k : ℕ,
      riemannZeta (missingHarmonicContourCenter rho k) ≠ 0 ∧
      0 < centeredSharpenedOrdinaryL2Constant
        (epsilonCenterCoefficient ε) rho k ∧
      ∀ᶠ Y : ℝ in atTop,
        centeredSharpenedOrdinaryL2Constant
              (epsilonCenterCoefficient ε) rho k *
            Real.sqrt (epsilonGaussianScale ε Y) <
          ∫ y : ℝ in
              Set.Icc (Real.log Y) ((1 + ε) * Real.log Y),
            normalizedPsiError rho y ^ 2)

end VKEdgePiOverTwo
end PrimeNumberTheorem
