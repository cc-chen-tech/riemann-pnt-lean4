import HardyTheorem.SelbergSqrtZetaSignedRationalFourierTransfer
import HardyTheorem.SelbergSqrtZetaSignedTruncatedEnergy
import MathlibAux.FourierLowEnergy
import MathlibAux.FourierWeightedTail

/-!
# Fourier budget for the signed rational short model

The low-frequency and reciprocal-square high-frequency estimates reduce the
whole sliding-window square mass to the dyadic `L²` budget of the truncated
phase.  The existing collected-frequency mean-square estimate then supplies
an explicit Selberg model budget.
-/

open Complex FourierTransform MeasureTheory Set
open scoped FourierTransform

namespace HardyTheorem

/-- The exact signed rational short model has square mass at most five times
the window-length square times the existing collected-frequency model
budget. -/
theorem
    integral_normSq_selbergSqrtZetaSignedRationalShortModel_le_five_mul_modelL2Budget
    (T : ℝ) (X : ℕ) {H : ℝ}
    (hT : 0 < T) (hH : 0 < H) (hroom : H ≤ T) :
    (∫ t in T..2 * T - H,
      Complex.normSq
        (selbergSqrtZetaSignedRationalShortModel T X H t)) ≤
      5 * H ^ 2 * selbergSqrtZetaSignedModelL2Budget T X := by
  let F : ℝ → ℂ := selbergSqrtZetaSignedTruncatedPhase T X
  let hF2 : MemLp F 2 :=
    memLp_two_selbergSqrtZetaSignedTruncatedPhase T X hT
  let f : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ) := hF2.toLp F
  let E : ℝ := ∫ y : ℝ, ‖F y‖ ^ 2
  have hcoe : (fun y : ℝ => f y) =ᵐ[volume] F := by
    simpa only [f] using hF2.coeFn_toLp
  have henergy :
      (∫ y : ℝ, ‖f y‖ ^ 2) = E := by
    apply integral_congr_ae
    filter_upwards [hcoe] with y hy
    rw [hy]
  have hlow :
      (∫ y : ℝ in {y | |y| ≤ 1 / H},
        ‖(𝓕 f : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) y‖ ^ 2) ≤ E := by
    have h :=
      MathlibAux.integral_norm_sq_fourier_low_le f H
    simpa only [henergy] using h
  have hhigh :
      (∫ y : ℝ in {y | 1 / H < |y|},
        ‖(𝓕 f : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) y‖ ^ 2 / y ^ 2) ≤
          H ^ 2 * E := by
    simpa only [f, hF2, E] using
      MathlibAux.integral_normSq_fourier_weightedTail_le hF2 hH
  have hmodel : E ≤ selbergSqrtZetaSignedModelL2Budget T X := by
    simpa only [E, F, Complex.normSq_eq_norm_sq] using
      integral_normSq_selbergSqrtZetaSignedTruncatedPhase_le_modelL2Budget
        T X hT
  have hparseval :=
    integral_normSq_selbergSqrtZetaSignedRationalShortModel_le_fourier_low_high
      T X hT hH hroom
  calc
    (∫ t in T..2 * T - H,
        Complex.normSq
          (selbergSqrtZetaSignedRationalShortModel T X H t)) ≤
        H ^ 2 *
            (∫ y : ℝ in {y | |y| ≤ 1 / H},
              ‖(𝓕 f :
                Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) y‖ ^ 2) +
          4 *
            (∫ y : ℝ in {y | 1 / H < |y|},
              ‖(𝓕 f :
                Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) y‖ ^ 2 / y ^ 2) := by
      simpa only [f, hF2, F] using hparseval
    _ ≤ H ^ 2 * E + 4 * (H ^ 2 * E) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hlow (sq_nonneg H))
        (mul_le_mul_of_nonneg_left hhigh (by norm_num))
    _ = 5 * H ^ 2 * E := by ring
    _ ≤ 5 * H ^ 2 * selbergSqrtZetaSignedModelL2Budget T X :=
      mul_le_mul_of_nonneg_left hmodel (by positivity)

end HardyTheorem
