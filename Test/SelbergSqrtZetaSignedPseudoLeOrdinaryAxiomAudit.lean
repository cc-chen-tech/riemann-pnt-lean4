import HardyTheorem.SelbergSqrtZetaSignedPseudoLeOrdinary

open Complex MeasureTheory
open HardyTheorem

#check
  norm_integral_integral_integral_selbergSqrtZetaSignedComplexModel_mul_shift_le_conj_shift

example (kappa T : ℝ) (X : ℕ) {H : ℝ}
    (hT : 0 < T) (hH : 0 ≤ H) (hroom : H ≤ T) :
    ‖∫ v in 0..H, ∫ w in 0..H, ∫ t in T..2 * T - H,
        selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
          selbergSqrtZetaSignedComplexModel kappa T X (t + w)‖ ≤
      ‖∫ v in 0..H, ∫ w in 0..H, ∫ t in T..2 * T - H,
        selbergSqrtZetaSignedComplexModel kappa T X (t + v) *
          (starRingEnd ℂ)
            (selbergSqrtZetaSignedComplexModel kappa T X (t + w))‖ :=
  norm_integral_integral_integral_selbergSqrtZetaSignedComplexModel_mul_shift_le_conj_shift
    kappa T X hT hH hroom

#print axioms
  norm_integral_integral_integral_selbergSqrtZetaSignedComplexModel_mul_shift_le_conj_shift
