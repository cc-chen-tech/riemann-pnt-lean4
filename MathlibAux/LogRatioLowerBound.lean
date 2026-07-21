import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace MathlibAux

/-- The logarithmic distance between two positive reals dominates their
relative additive distance. -/
theorem abs_sub_div_max_le_abs_log_div
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    |x - y| / max x y ≤ |Real.log (x / y)| := by
  rcases le_total x y with hxy | hyx
  · have hratioPos : 0 < x / y := div_pos hx hy
    have hratioLe : x / y ≤ 1 := (div_le_one hy).2 hxy
    have hlogNonpos : Real.log (x / y) ≤ 0 :=
      Real.log_nonpos hratioPos.le hratioLe
    have hlower := Real.one_sub_inv_le_log_of_pos (div_pos hy hx)
    have hswap : -Real.log (x / y) = Real.log (y / x) := by
      rw [Real.log_div hx.ne' hy.ne', Real.log_div hy.ne' hx.ne']
      ring
    have hfrac : 1 - (y / x)⁻¹ = (y - x) / y := by
      rw [inv_div]
      field_simp [hy.ne']
    rw [max_eq_right hxy, abs_of_nonpos (sub_nonpos.2 hxy),
      abs_of_nonpos hlogNonpos, hswap]
    rw [hfrac] at hlower
    simpa only [neg_sub] using hlower
  · have hratioOne : 1 ≤ x / y :=
      (le_div_iff₀ hy).2 (by simpa using hyx)
    have hlogNonneg : 0 ≤ Real.log (x / y) := Real.log_nonneg hratioOne
    have hlower := Real.one_sub_inv_le_log_of_pos (div_pos hx hy)
    have hfrac : 1 - (x / y)⁻¹ = (x - y) / x := by
      rw [inv_div]
      field_simp [hx.ne']
    rw [max_eq_left hyx, abs_of_nonneg (sub_nonneg.2 hyx),
      abs_of_nonneg hlogNonneg]
    rw [hfrac] at hlower
    exact hlower

end MathlibAux
