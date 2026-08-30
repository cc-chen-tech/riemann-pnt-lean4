import PrimeNumberTheorem.CarlsonTwoScaleHorizontalBudget

set_option autoImplicit false

open Complex Filter Set
open PrimeNumberTheorem.CarlsonZeroDensity

example {C₁ C₂ U S r : ℝ} {Y0 Y1 : ℕ}
    (hC₁ : 1 ≤ C₁) (hC₁U : C₁ ≤ U) (hC₂ : 1 ≤ C₂) (hC₂U : C₂ ≤ U)
    (hY1 : 1 ≤ Y1) (hY1U : (Y1 : ℝ) ≤ U) (hU : 6 ≤ U)
    (hS : 0 ≤ S) (hSU : S + 14 ≤ 4 * U)
    (hr : r ∈ Icc (121 / 32 : ℝ) (122 / 32 : ℝ)) :
    4 * max (regularizedTwoScaleCarlsonFactorLogVariationMajorant C₁ Y0 Y1 S
        (regularizedTwoScaleCarlsonFactorZeroLogMajorant C₂ Y0 Y1 S)) 1 *
        (r + 15 / 4) / (r - 15 / 4) ^ 2 +
      regularizedTwoScaleCarlsonFactorZeroLogMajorant C₂ Y0 Y1 S /
        (1 / (4 * (regularizedTwoScaleCarlsonFactorZeroLogMajorant C₂ Y0 Y1 S + 1))) ≤
      (16 * carlsonHorizontalMajorantCoefficient) * (1 + Real.log U) ^ 2 :=
  twoScale_horizontal_explicitMajorant_le_logSquare hC₁ hC₁U hC₂ hC₂U hY1 hY1U hU hS hSU hr

example : ∃ K > (0 : ℝ), ∀ᶠ U : ℝ in atTop,
    ∀ {Y0 Y1 : ℕ}, 2 ≤ Y0 → Y0 < Y1 → (Y1 : ℝ) ≤ U →
      ∀ {sigma S : ℝ}, 1 / 2 < sigma → 5 ≤ S → S + 14 ≤ 4 * U →
        ∃ t ∈ Icc S (S + 1),
          (∀ x ∈ Icc sigma 4,
            regularizedTwoScaleCarlsonZeroDetector Y0 Y1 ((x : ℂ) + (t : ℂ) * I) ≠ 0) ∧
          ∀ x ∈ Icc sigma 4,
            ‖logDeriv (regularizedTwoScaleCarlsonZeroDetector Y0 Y1) ((x : ℂ) + (t : ℂ) * I)‖ ≤
              K * (1 + Real.log U) ^ 2 :=
  exists_eventually_twoScale_horizontal_logDeriv_le_logSquare

#print axioms twoScale_horizontal_explicitMajorant_le_logSquare
#print axioms exists_eventually_twoScale_horizontal_logDeriv_le_logSquare
