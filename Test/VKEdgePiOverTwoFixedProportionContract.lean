import PrimeNumberTheorem.VKEdgePiOverTwoFixedProportion

open Complex Filter MeasureTheory Set
open PrimeNumberTheorem VKEdgePiOverTwo

#check (measurable_normalizedPsiError_fixedProportion :
  ∀ rho : ℂ, Measurable (normalizedPsiError rho))

#check (
  exists_eventually_fixedProportion_largeNormalizedPsiError_of_fourthMoment :
  ∀ {ε C4 : ℝ} {rho : ℂ} {sigma : ℝ},
    0 < ε →
    0 < rho.im →
    riemannZeta rho = 0 →
    1 / 2 < sigma →
    sigma < rho.re →
    rho.re < 1 →
    0 < C4 →
    -- External analytic input: this project does not currently prove it.
    (∀ᶠ Y : ℝ in atTop,
      IntegrableOn
          (fun y => normalizedPsiError rho y ^ 4)
          (Icc (Real.log Y) ((1 + ε) * Real.log Y)) ∧
        (∫ y in Icc (Real.log Y) ((1 + ε) * Real.log Y),
            normalizedPsiError rho y ^ 4) ≤
          C4 * Real.log Y) →
    ∃ k : ℕ,
      riemannZeta (missingHarmonicContourCenter rho k) ≠ 0 ∧
      0 < centeredSharpenedSweptOrdinaryL2Constant ε rho k ∧
      ∀ᶠ Y : ℝ in atTop,
      (centeredSharpenedSweptOrdinaryL2Constant ε rho k ^ 2 /
            (4 * C4)) *
          Real.log Y <
        volume.real
          {y ∈ Icc (Real.log Y) ((1 + ε) * Real.log Y) |
            centeredSharpenedSweptOrdinaryL2Constant ε rho k /
                  (2 * ε) <
              normalizedPsiError rho y ^ 2})
