import HardyTheorem.ConreyShiftedH

/-! Exact same-mollifier approximation of V1 by the degree-one differential
polynomial. This is a pointwise estimate, not a mean-value hypothesis. -/

open Complex Set

namespace HardyTheorem

/-- The explicit Q(-D/L) zeta for Q(x)=1-51x/50. -/
noncomputable def conreyExplicitV (L : ℝ) (s : ℂ) : ℂ :=
  riemannZeta s + ((51 / (50 * L) : ℝ) : ℂ) * deriv riemannZeta s

/-- The uniform error coefficient on exp(a L) <= t <= exp L. -/
noncomputable def conreyV1ComparisonCoefficient (L a : ℝ) : ℝ :=
  (51 / 50 : ℝ) * ((1 - a) / 2 + (10 + |Real.log (2 * Real.pi)| / 2) / L)

private theorem comparisonCoefficient_nonneg {L a : ℝ} (hL : 0 < L) (ha : a ≤ 1) :
    0 ≤ conreyV1ComparisonCoefficient L a := by
  unfold conreyV1ComparisonCoefficient
  exact mul_nonneg (by norm_num) (add_nonneg
    (div_nonneg (sub_nonneg.mpr ha) (by norm_num)) (by positivity))

private theorem actual_difference {L : ℝ} (hL : L ≠ 0) (s : ℂ) :
    conreyDegreeOneV1 (49 / 100) 0 (51 / 50) L s - conreyExplicitV L s =
      ((51 / (50 * L) : ℝ) : ℂ) *
        (deriv conreyH s / conreyH s - ((L / 2 : ℝ) : ℂ)) * riemannZeta s := by
  unfold conreyDegreeOneV1 conreyExplicitV
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hL]
  ring

/-- The actual long product error on any original high subinterval.
No nonzero or regularity assumptions on the finite mollifier are needed. -/
theorem norm_conreyMollifiedV1_sub_V_le
    {L sigma a t : ℝ} {Y : ℕ} {P : ℝ → ℝ}
    (hL : 0 < L) (hs : 0 < sigma) (hsHalf : sigma ≤ 1 / 2)
    (_ha : a ≤ 1) (ht : 3 ≤ t) (htlow : Real.exp (a * L) ≤ t) (httop : t ≤ Real.exp L) :
    ‖conreyMollifiedDegreeOneV1 (49 / 100) 0 (51 / 50) L Y sigma P ((sigma : ℂ) + I * t) -
      conreyExplicitV L ((sigma : ℂ) + I * t) * conreyMollifier Y sigma P ((sigma : ℂ) + I * t)‖ ≤
      conreyV1ComparisonCoefficient L a *
        ‖riemannZeta ((sigma : ℂ) + I * t) * conreyMollifier Y sigma P ((sigma : ℂ) + I * t)‖ := by
  let s : ℂ := (sigma : ℂ) + I * t
  let m : ℂ := ((Real.log (t / (2 * Real.pi)) / 2 : ℝ) : ℂ)
  have htpos : 0 < t := by linarith
  have hloglow : a * L ≤ Real.log t := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) htlow
  have hlogtop : Real.log t ≤ L := by
    simpa only [Real.log_exp] using Real.log_le_log htpos httop
  have habs : |Real.log (t / (2 * Real.pi)) - L| ≤
      L - Real.log t + |Real.log (2 * Real.pi)| := by
    rw [Real.log_div htpos.ne' (mul_ne_zero (by norm_num) Real.pi_ne_zero)]
    calc
      _ = |-(L - Real.log t) - Real.log (2 * Real.pi)| := by congr 1; ring
      _ ≤ |-(L - Real.log t)| + |Real.log (2 * Real.pi)| := abs_sub _ _
      _ = _ := by rw [abs_neg, abs_of_nonneg (sub_nonneg.mpr hlogtop)]
  have hm : ‖m - ((L / 2 : ℝ) : ℂ)‖ ≤
      (L - Real.log t + |Real.log (2 * Real.pi)|) / 2 := by
    have he : m - ((L / 2 : ℝ) : ℂ) =
        (((Real.log (t / (2 * Real.pi)) - L) / 2 : ℝ) : ℂ) := by
      dsimp [m]
      push_cast
      ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_div]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right habs (by norm_num : (0 : ℝ) ≤ 2)
  have hH := norm_logDeriv_conreyH_shifted_sub_half_log_le hs hsHalf ht
  have herr : ‖deriv conreyH s / conreyH s - ((L / 2 : ℝ) : ℂ)‖ ≤
      (1 - a) * L / 2 + (10 + |Real.log (2 * Real.pi)| / 2) := by
    have htri := norm_add_le (deriv conreyH s / conreyH s - m) (m - ((L / 2 : ℝ) : ℂ))
    rw [sub_add_sub_cancel] at htri
    change ‖deriv conreyH s / conreyH s - m‖ ≤ 10 at hH
    nlinarith only [htri, hH, hm, hloglow]
  have hcoeff : ‖((51 / (50 * L) : ℝ) : ℂ)‖ = 51 / (50 * L) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hfactor : 51 / (50 * L) *
      ((1 - a) * L / 2 + (10 + |Real.log (2 * Real.pi)| / 2)) =
      conreyV1ComparisonCoefficient L a := by
    unfold conreyV1ComparisonCoefficient
    field_simp [hL.ne']
  change ‖conreyDegreeOneV1 (49 / 100) 0 (51 / 50) L s * conreyMollifier Y sigma P s -
      conreyExplicitV L s * conreyMollifier Y sigma P s‖ ≤ _
  rw [← sub_mul, actual_difference hL.ne']
  rw [mul_assoc, mul_assoc, norm_mul, norm_mul, hcoeff]
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left herr (by positivity : 0 ≤ 51 / (50 * L)))
    (norm_nonneg (riemannZeta s * conreyMollifier Y sigma P s))
  rw [hfactor] at hmul
  simpa only [mul_assoc] using hmul

end HardyTheorem
