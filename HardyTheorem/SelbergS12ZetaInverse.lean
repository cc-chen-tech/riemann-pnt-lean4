import HardyTheorem.SelbergS12BoundedHeight

open Complex

namespace HardyTheorem

/-!
# Selberg S12: global punctured one-line reciprocal bound

The pole neighborhood, compact middle annulus, and high-height Grönwall
estimate are combined here.  The exclusion `t ≠ 0` is mathematically
essential for Mathlib's chosen point value of zeta at its pole; it is harmless
for all contour integrals.
-/

theorem exists_norm_inv_riemannZeta_oneLine_le_mul_abs :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ t : ℝ, t ≠ 0 →
        ‖(riemannZeta ((1 : ℂ) + I * t))⁻¹‖ ≤ A * |t| := by
  rcases exists_norm_inv_riemannZeta_oneLine_le_two_mul_abs_near_zero with
    ⟨r, hr, hnear⟩
  rcases exists_norm_inv_riemannZeta_oneLine_le_mul_abs_high with
    ⟨Ahi, T, hAhi, hT, hhigh⟩
  rcases exists_norm_inv_riemannZeta_oneLine_le_mul_abs_on_annulus
      (T := T) hr with ⟨Amid, hAmid, hmiddle⟩
  let A : ℝ := max 2 (max Ahi Amid)
  have hA : 0 ≤ A := by
    exact le_trans (by norm_num : (0 : ℝ) ≤ 2) (le_max_left _ _)
  refine ⟨A, hA, ?_⟩
  intro t ht0
  by_cases hsmall : |t| < r
  · have h := hnear t ht0 hsmall
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left 2 (max Ahi Amid))
      (abs_nonneg t))
  by_cases hlarge : T ≤ |t|
  · have h := hhigh t hlarge
    have hcoeff : Ahi ≤ A :=
      (le_max_left Ahi Amid).trans (le_max_right 2 (max Ahi Amid))
    exact h.trans (mul_le_mul_of_nonneg_right hcoeff (abs_nonneg t))
  · have hrange_low : r ≤ |t| := le_of_not_gt hsmall
    have hrange_high : |t| ≤ T := (lt_of_not_ge hlarge).le
    have h := hmiddle t hrange_low hrange_high
    have hcoeff : Amid ≤ A :=
      (le_max_right Ahi Amid).trans (le_max_right 2 (max Ahi Amid))
    exact h.trans (mul_le_mul_of_nonneg_right hcoeff (abs_nonneg t))

end HardyTheorem
