import HardyTheorem.SelbergS12StripHigh

namespace HardyTheorem

/-! # Selberg S12: global reciprocal-zeta bound on the closed one-strip -/

theorem exists_norm_inv_riemannZeta_strip_le_mul_offset :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ epsilon t : ℝ, 0 < epsilon → epsilon ≤ 1 →
        ‖(riemannZeta (selbergS12StripPoint epsilon t))⁻¹‖ ≤
          A * (epsilon + |t|) := by
  rcases exists_norm_inv_riemannZeta_strip_le_mul_abs_high with
    ⟨Ahi, T, hAhi, hT, hhigh⟩
  rcases exists_norm_inv_riemannZeta_strip_le_mul_offset_on_bounded_height T with
    ⟨Alo, hAlo, hlow⟩
  let A : ℝ := max Alo Ahi
  have hA : 0 ≤ A := hAlo.trans (le_max_left _ _)
  refine ⟨A, hA, ?_⟩
  intro epsilon t heps heps1
  have heps0 : 0 ≤ epsilon := heps.le
  by_cases ht : T ≤ |t|
  · have h := hhigh epsilon t heps0 heps1 ht
    have hcoeff : Ahi ≤ A := le_max_right _ _
    calc
      ‖(riemannZeta (selbergS12StripPoint epsilon t))⁻¹‖ ≤ Ahi * |t| := h
      _ ≤ A * |t| := mul_le_mul_of_nonneg_right hcoeff (abs_nonneg _)
      _ ≤ A * (epsilon + |t|) :=
        mul_le_mul_of_nonneg_left (by linarith) hA
  · have ht' : |t| ≤ T := (lt_of_not_ge ht).le
    have h := hlow epsilon t heps0 heps1 ht' (by positivity)
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left Alo Ahi) (by positivity))

end HardyTheorem
