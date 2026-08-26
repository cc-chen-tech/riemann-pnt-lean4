import HardyTheorem.SelbergS12ZetaInverse

open Complex

namespace HardyTheorem

/-!
# Selberg S12: branch-independent square-root bound

Only the identity `R(t)^2 = 1 / ζ(1+it)` is needed for the norm estimate;
the choice of the analytic branch is postponed to the contour layer.
-/

theorem exists_norm_squareRoot_inv_riemannZeta_oneLine_le :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (t : ℝ) (R : ℂ), t ≠ 0 →
        R ^ 2 = (riemannZeta ((1 : ℂ) + I * t))⁻¹ →
        ‖R‖ ≤ B * Real.sqrt |t| := by
  rcases exists_norm_inv_riemannZeta_oneLine_le_mul_abs with ⟨A, hA, hbound⟩
  let B : ℝ := Real.sqrt A
  have hB : 0 ≤ B := Real.sqrt_nonneg A
  refine ⟨B, hB, ?_⟩
  intro t R ht0 hR
  have hsq : ‖R‖ ^ 2 ≤ A * |t| := by
    calc
      ‖R‖ ^ 2 = ‖R ^ 2‖ := by rw [norm_pow]
      _ = ‖(riemannZeta ((1 : ℂ) + I * t))⁻¹‖ := by rw [hR]
      _ ≤ A * |t| := hbound t ht0
  calc
    ‖R‖ = Real.sqrt (‖R‖ ^ 2) := by
      rw [Real.sqrt_sq (norm_nonneg R)]
    _ ≤ Real.sqrt (A * |t|) := Real.sqrt_le_sqrt hsq
    _ = B * Real.sqrt |t| := by
      rw [Real.sqrt_mul hA]

end HardyTheorem
