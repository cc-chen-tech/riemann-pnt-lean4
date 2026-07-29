import PrimeNumberTheorem.VKEdgePiOverTwoSweptL2

open Complex Filter MeasureTheory Set
open PrimeNumberTheorem
open PrimeNumberTheorem.VKEdgePiOverTwo

#check sweptGaussianEnvelope
#check epsilonSweepRatio
#check centeredSharpenedSweptOrdinaryL2Constant

#check (exp_scaled_abs_mul_normalizedGaussian_le_sweptEnvelope :
  ∀ {q M R m y : ℝ},
    1 ≤ M → 1 ≤ R → M ≤ m → m ≤ R * M →
    Real.exp |(Real.sqrt m)⁻¹ * (q * m - y)| *
        normalizedGaussian m (q * m - y) ≤
      sweptGaussianEnvelope q M R m y)

#check (integral_sweptGaussianEnvelope_le :
  ∀ {q M R y : ℝ},
    0 < q → 0 < M → 0 < R →
    (∫ m in Set.Icc M (R * M),
        sweptGaussianEnvelope q M R m y) ≤
      Real.exp 2 * Real.sqrt (2 * R) / q)

#check (centeredSharpenedProjectedPsiKernel_abs_le_scaledEnvelope :
  ∀ (q : ℝ) {rho : ℂ} {k : ℕ},
    rho ≠ 0 → 0 < rho.im →
    ∀ (m : ℝ), 1 ≤ m → ∀ y : ℝ,
      |centeredSharpenedProjectedPsiKernel q rho k m y| ≤
        centeredSharpenedProjectedPsiKernelEnvelopeConstant q rho k *
          (Real.exp |(Real.sqrt m)⁻¹ * (q * m - y)| *
            normalizedGaussian m (q * m - y)))

#check (ordinarySecondMoment_linear_lower_of_sweptWeightedLower :
  ∀ {q d M R a b C2 K B : ℝ} {rho : ℂ}
      {kernel : ℝ → ℝ → ℝ},
    1 ≤ M → 0 < q → 1 < R → 0 ≤ K → 0 ≤ B →
    (∀ y ∈ Set.Icc a b, normalizedPsiError rho y ^ 2 ≤ B) →
    (∀ m ∈ Set.Icc M (R * M),
      localizedGaussianLogWindow q d m ⊆ Set.Icc a b) →
    (∀ m ∈ Set.Icc M (R * M),
      ∀ y ∈ localizedGaussianLogWindow q d m,
        |kernel m y| ≤
          K *
            (Real.exp |(Real.sqrt m)⁻¹ * (q * m - y)| *
              normalizedGaussian m (q * m - y))) →
    (∀ m ∈ Set.Icc M (R * M),
      IntegrableOn
        (fun y => normalizedPsiError rho y ^ 2 * |kernel m y|)
        (localizedGaussianLogWindow q d m)) →
    (∀ m ∈ Set.Icc M (R * M),
      C2 < centeredNormalizedWindowSecondMoment q d rho kernel m) →
    C2 * (R - 1) * M ≤
      K * (Real.exp 2 * Real.sqrt (2 * R) / q) *
        ∫ y in Set.Icc a b, normalizedPsiError rho y ^ 2)

#check (one_lt_epsilonSweepRatio :
  ∀ {ε : ℝ}, 0 < ε → 1 < epsilonSweepRatio ε)

#check (localizedGaussianLogWindow_subset_epsilonWindow_of_mem_sweep :
  ∀ {ε Y m : ℝ},
    0 < ε → 1 < Y →
    m ∈ Set.Icc
      (epsilonGaussianScale (ε / 2) Y)
      (epsilonSweepRatio ε * epsilonGaussianScale (ε / 2) Y) →
    localizedGaussianLogWindow
        (epsilonCenterCoefficient (ε / 2))
        (epsilonRadiusCoefficient (ε / 2)) m ⊆
      Set.Icc (Real.log Y) ((1 + ε) * Real.log Y))

#check (exists_eventually_ordinarySecondMoment_in_epsilonLogWindow_gt_linear :
  ∀ {ε : ℝ} {rho : ℂ} {sigma : ℝ},
    0 < ε → 0 < rho.im → riemannZeta rho = 0 →
    1 / 2 < sigma → sigma < rho.re → rho.re < 1 →
    ∃ k : ℕ,
      riemannZeta (missingHarmonicContourCenter rho k) ≠ 0 ∧
      0 < centeredSharpenedSweptOrdinaryL2Constant ε rho k ∧
      ∀ᶠ Y : ℝ in Filter.atTop,
        centeredSharpenedSweptOrdinaryL2Constant ε rho k *
            Real.log Y <
          ∫ y in Set.Icc (Real.log Y) ((1 + ε) * Real.log Y),
            normalizedPsiError rho y ^ 2)
