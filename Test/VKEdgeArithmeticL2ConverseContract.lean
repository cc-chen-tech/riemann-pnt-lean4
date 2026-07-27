import PrimeNumberTheorem.VKEdgeArithmeticL2Converse

open Complex Filter MeasureTheory Set
open PrimeNumberTheorem
open PrimeNumberTheorem.VKEdgePiOverTwo

#check (logarithmicPsiErrorSecondMoment :
  ℝ → ℝ → ℝ)

#check (normalizedPsiError_secondMoment_le_arithmetic :
  ∀ {ε Y : ℝ} {rho : ℂ},
    0 ≤ ε → 1 < Y → 0 ≤ rho.re → rho.re < 1 →
    (∫ y in Set.Icc (Real.log Y) ((1 + ε) * Real.log Y),
        normalizedPsiError rho y ^ 2) ≤
      ‖rho‖ ^ 2 * Real.exp (-2 * rho.re * Real.log Y) *
        logarithmicPsiErrorSecondMoment ε Y)

#check (exists_eventually_logarithmicPsiErrorSecondMoment_gt :
  ∀ {ε : ℝ} {rho : ℂ} {sigma : ℝ},
    0 < ε → 0 < rho.im → riemannZeta rho = 0 →
    1 / 2 < sigma → sigma < rho.re → rho.re < 1 →
    ∃ k : ℕ,
      riemannZeta (missingHarmonicContourCenter rho k) ≠ 0 ∧
      0 < centeredSharpenedSweptOrdinaryL2Constant ε rho k ∧
      ∀ᶠ Y : ℝ in Filter.atTop,
        (centeredSharpenedSweptOrdinaryL2Constant ε rho k /
              ‖rho‖ ^ 2) *
            Real.exp (2 * rho.re * Real.log Y) * Real.log Y <
          logarithmicPsiErrorSecondMoment ε Y)

#check (logarithmicPsiErrorSecondMoment_not_isLittleO_of_offLineZero :
  ∀ {ε : ℝ} {rho : ℂ} {sigma : ℝ},
    0 < ε → 0 < rho.im → riemannZeta rho = 0 →
    1 / 2 < sigma → sigma < rho.re → rho.re < 1 →
    ¬((fun Y : ℝ => logarithmicPsiErrorSecondMoment ε Y) =o[atTop]
      (fun Y : ℝ =>
        Real.exp (2 * rho.re * Real.log Y) * Real.log Y)))

#check (riemannZeta_ne_zero_of_logarithmicPsiErrorSecondMoment_isLittleO :
  ∀ {ε : ℝ} {rho : ℂ},
    0 < ε → 0 < rho.im → 1 / 2 < rho.re → rho.re < 1 →
    (fun Y : ℝ => logarithmicPsiErrorSecondMoment ε Y) =o[atTop]
      (fun Y : ℝ =>
        Real.exp (2 * rho.re * Real.log Y) * Real.log Y) →
    riemannZeta rho ≠ 0)
