import ZeroFreeRegion.MeromorphicAux

open Complex
open ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.zeta
  LSeries.notation

namespace HardyTheorem

/-!
# Selberg S12: the absolutely convergent moving right line

This is the first analytic input for S12.  On `Re(s) > 1`, the reciprocal
of zeta is the Möbius L-series and is bounded by the real zeta majorant
`σ / (σ - 1)`.
-/

theorem norm_LSeries_moebius_le_re_div_sub_one
    {s : ℂ} (hs : 1 < s.re) :
    ‖L ↗μ s‖ ≤ s.re / (s.re - 1) := by
  have hmu : LSeriesSummable ↗μ s :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  have hzeta : LSeriesSummable ↗ζ s :=
    ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  have hterm : ∀ n,
      ‖LSeries.term ↗μ s n‖ ≤ ‖LSeries.term ↗ζ s n‖ := by
    intro n
    apply LSeries.norm_term_le
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp only [hn, ArithmeticFunction.zeta_apply, if_false,
        Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  have hsreal : 1 < ((s.re : ℂ)).re := by simpa using hs
  have hzetareal : LSeriesSummable ↗ζ (s.re : ℂ) :=
    ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hsreal
  calc
    ‖L ↗μ s‖ ≤
        ∑' n, ‖LSeries.term ↗μ s n‖ :=
      norm_tsum_le_tsum_norm hmu.norm
    _ ≤ ∑' n, ‖LSeries.term ↗ζ s n‖ :=
      hmu.norm.tsum_le_tsum hterm hzeta.norm
    _ = (L ↗ζ (s.re : ℂ)).re := by
      rw [LSeries, re_tsum hzetareal]
      apply tsum_congr
      intro n
      calc
        ‖LSeries.term ↗ζ s n‖ =
            ‖LSeries.term ↗ζ (s.re : ℂ) n‖ := by
          simp [LSeries.norm_term_eq]
        _ = (LSeries.term ↗ζ (s.re : ℂ) n).re := by
          rcases eq_or_ne n 0 with rfl | hn
          · simp [LSeries.term]
          · rw [LSeries.term_of_ne_zero hn]
            simp only [hn, ArithmeticFunction.zeta_apply, if_false]
            have hpow : (n : ℂ) ^ (s.re : ℂ) =
                (((n : ℝ) ^ s.re : ℝ) : ℂ) := by
              exact (Complex.ofReal_cpow (Nat.cast_nonneg n) s.re).symm
            rw [hpow]
            simp
            positivity
    _ = (riemannZeta (s.re : ℂ)).re := by
      rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hsreal]
    _ ≤ s.re / (s.re - 1) :=
      ZeroFreeRegion.riemannZeta_re_le_sigma_div_sub s.re hs

theorem norm_inv_riemannZeta_le_re_div_sub_one
    {s : ℂ} (hs : 1 < s.re) :
    ‖(riemannZeta s)⁻¹‖ ≤ s.re / (s.re - 1) := by
  have hproduct :=
    ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at hproduct
  have hinv : (riemannZeta s)⁻¹ = L ↗μ s :=
    inv_eq_of_mul_eq_one_right hproduct
  rw [hinv]
  exact norm_LSeries_moebius_le_re_div_sub_one hs

/-- The moving point just to the right of the one-line. -/
noncomputable def selbergS12MovingRightPoint (a t : ℝ) : ℂ :=
  ((1 + a / Real.log |t| : ℝ) : ℂ) + I * t

@[simp] theorem selbergS12MovingRightPoint_re (a t : ℝ) :
    (selbergS12MovingRightPoint a t).re = 1 + a / Real.log |t| := by
  simp [selbergS12MovingRightPoint]

/-- At the moving right point, absolute convergence costs only
`1 + log|t| / a`. -/
theorem norm_inv_riemannZeta_selbergS12MovingRightPoint_le
    {a t : ℝ} (ha : 0 < a) (ht : 1 < |t|) :
    ‖(riemannZeta (selbergS12MovingRightPoint a t))⁻¹‖ ≤
      1 + Real.log |t| / a := by
  have hlog : 0 < Real.log |t| := Real.log_pos ht
  have hre : 1 < (selbergS12MovingRightPoint a t).re := by
    simp only [selbergS12MovingRightPoint_re]
    linarith [div_pos ha hlog]
  have hbound := norm_inv_riemannZeta_le_re_div_sub_one hre
  calc
    ‖(riemannZeta (selbergS12MovingRightPoint a t))⁻¹‖ ≤
        (selbergS12MovingRightPoint a t).re /
          ((selbergS12MovingRightPoint a t).re - 1) := hbound
    _ = 1 + Real.log |t| / a := by
      rw [selbergS12MovingRightPoint_re]
      field_simp [ha.ne', hlog.ne']
      ring

end HardyTheorem
