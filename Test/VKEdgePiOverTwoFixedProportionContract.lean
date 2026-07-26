import PrimeNumberTheorem.VKEdgePiOverTwoFixedProportion

open Complex Filter MeasureTheory Set
open PrimeNumberTheorem VKEdgePiOverTwo

#check exists_eventually_fixedProportion_largeNormalizedPsiError_of_fourthMoment

example
    {ε C4 : ℝ} {rho : ℂ} {sigma : ℝ}
    (hε : 0 < ε)
    (hgamma : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (hσ : 1 / 2 < sigma)
    (hσrho : sigma < rho.re)
    (hrhoRe1 : rho.re < 1)
    (hC4 : 0 < C4)
    (hfourth :
      ∀ᶠ Y : ℝ in atTop,
        IntegrableOn
            (fun y => normalizedPsiError rho y ^ 4)
            (Icc (Real.log Y) ((1 + ε) * Real.log Y)) ∧
          (∫ y in Icc (Real.log Y) ((1 + ε) * Real.log Y),
              normalizedPsiError rho y ^ 4) ≤
            C4 * Real.log Y) :
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
                normalizedPsiError rho y ^ 2} :=
  exists_eventually_fixedProportion_largeNormalizedPsiError_of_fourthMoment
    hε hgamma hzero hσ hσrho hrhoRe1 hC4 hfourth
