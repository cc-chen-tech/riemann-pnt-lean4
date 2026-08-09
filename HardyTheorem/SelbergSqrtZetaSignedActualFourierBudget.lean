import HardyTheorem.SelbergSqrtZetaSignedActualFourierTransfer
import HardyTheorem.SelbergSqrtZetaSignedRationalFourierBudget

/-!
# Fourier budget for the actual signed Selberg short windows

The uniform first-zeta approximation transfers the genuine mollified Hardy
short integral to the exact rational model.  Combining that transfer with
the Fourier short-window estimate leaves one global model-energy term and an
explicit approximation error.
-/

open Complex MeasureTheory

namespace HardyTheorem

/-- The genuine signed short-window second moment is controlled by ten times
the window-length square times the collected model energy, plus the explicit
uniform first-zeta approximation error. -/
theorem
    exists_integral_sq_selbergSqrtZetaSignedShortIntegral_le_modelL2Budget_add_error :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, 2 ≤ X → ∀ T H : ℝ,
        T0 ≤ T → 0 < H → H ≤ T →
          (∫ t in T..2 * T - H,
            (selbergSqrtZetaSignedShortIntegral X H t) ^ 2) ≤
            10 * H ^ 2 * selbergSqrtZetaSignedModelL2Budget T X +
              2 * T * (4 * C * H * X / Real.sqrt T) ^ 2 := by
  obtain ⟨C, T0, hC, hT0, htransfer⟩ :=
    exists_integral_sq_selbergSqrtZetaSignedShortIntegral_le_rationalShortModel_add_error
  refine ⟨C, T0, hC, hT0, ?_⟩
  intro X hX T H hT hH hroom
  have hTpos : 0 < T := zero_lt_one.trans_le (hT0.trans hT)
  have hrational :=
    integral_normSq_selbergSqrtZetaSignedRationalShortModel_le_five_mul_modelL2Budget
      T X hTpos hH hroom
  calc
    (∫ t in T..2 * T - H,
        (selbergSqrtZetaSignedShortIntegral X H t) ^ 2) ≤
        2 * (∫ t in T..2 * T - H,
          Complex.normSq
            (selbergSqrtZetaSignedRationalShortModel T X H t)) +
          2 * T * (4 * C * H * X / Real.sqrt T) ^ 2 :=
      htransfer X hX T H hT hH hroom
    _ ≤ 2 * (5 * H ^ 2 * selbergSqrtZetaSignedModelL2Budget T X) +
          2 * T * (4 * C * H * X / Real.sqrt T) ^ 2 :=
      add_le_add
        (mul_le_mul_of_nonneg_left hrational (by norm_num)) le_rfl
    _ = 10 * H ^ 2 * selbergSqrtZetaSignedModelL2Budget T X +
          2 * T * (4 * C * H * X / Real.sqrt T) ^ 2 := by
      ring

end HardyTheorem
