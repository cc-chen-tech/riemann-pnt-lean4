import HardyTheorem.HardyCompletedCriticalLine
import HardyTheorem.SelbergSqrtZetaMollifier

open Complex

namespace HardyTheorem

/-!
# Selberg's completed-zeta mollified sign function

This is the real function used by the Fourier--Mellin mainline of Selberg's
positive-proportion argument.  On the critical line,

`Xi(t) / (t^2 + 1/4) = -(1/2) * completedRiemannZeta(1/2 + i t)`.

Consequently the function below is the Titchmarsh--Selberg function with the
unitary normalization `1 / sqrt (2*pi)`, written directly in terms of the
completed zeta function already available in Mathlib.  The fixed minus sign
reverses orientations but does not change sign-change locations.
-/

/-- The nonnegative factor relating Selberg's completed mollified function
to Hardy's `Z` function. -/
noncomputable def selbergCompletedMollifiedPositiveFactor
    (delta : ℝ) (X : ℕ) (t : ℝ) : ℝ :=
  (1 / (2 * Real.sqrt (2 * Real.pi))) *
    ‖Gammaℝ ((1 / 2 : ℂ) + I * t)‖ *
    Complex.normSq
      (selbergMollifier X
        (fun n => (selbergSqrtZetaTaperedCoeff X n : ℂ))
        ((1 / 2 : ℂ) + I * t)) *
    Real.exp ((Real.pi / 4 - delta / 2) * t)

/-- Selberg's completed-zeta function with two copies of the tapered
`zeta^(-1/2)` mollifier and exponential Fourier tilt. -/
noncomputable def selbergCompletedMollifiedF
    (delta : ℝ) (X : ℕ) (t : ℝ) : ℝ :=
  -(1 / (2 * Real.sqrt (2 * Real.pi))) *
    hardyCompletedCriticalLine t *
    Complex.normSq
      (selbergMollifier X
        (fun n => (selbergSqrtZetaTaperedCoeff X n : ℂ))
        ((1 / 2 : ℂ) + I * t)) *
    Real.exp ((Real.pi / 4 - delta / 2) * t)

theorem selbergCompletedMollifiedPositiveFactor_nonneg
    (delta : ℝ) (X : ℕ) (t : ℝ) :
    0 ≤ selbergCompletedMollifiedPositiveFactor delta X t := by
  unfold selbergCompletedMollifiedPositiveFactor
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) :=
    Real.sqrt_pos.2 (mul_pos (by norm_num) Real.pi_pos)
  have hcoefficient :
      0 ≤ (1 / (2 * Real.sqrt (2 * Real.pi)) : ℝ) :=
    (one_div_pos.mpr (mul_pos (by norm_num) hsqrt)).le
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg hcoefficient (norm_nonneg _))
      (Complex.normSq_nonneg _))
    (Real.exp_pos _).le

private theorem conj_inv_nat_cpow_criticalLine_eq_neg
    (n : ℕ) (t : ℝ) :
    (starRingEnd ℂ)
        (1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)) =
      1 / (n : ℂ) ^ ((1 / 2 : ℂ) - I * t) := by
  rw [map_div₀, map_one]
  have harg : (n : ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]
    exact Real.pi_ne_zero.symm
  have hpow := Complex.cpow_conj
    (n : ℂ) ((1 / 2 : ℂ) + I * t) harg
  have hconj :
      (starRingEnd ℂ) ((1 / 2 : ℂ) + I * t) =
        (1 / 2 : ℂ) - I * t := by
    apply Complex.ext <;> norm_num
  rw [hconj] at hpow
  simpa using congrArg Inv.inv hpow.symm

/-- Since the tapered square-root-zeta coefficients are real, conjugation
reflects the finite mollifier from height `t` to height `-t`. -/
theorem conj_selbergCompletedSqrtZetaMollifier_criticalLine_eq_neg
    (X : ℕ) (t : ℝ) :
    (starRingEnd ℂ)
        (selbergMollifier X
          (fun n => (selbergSqrtZetaTaperedCoeff X n : ℂ))
          ((1 / 2 : ℂ) + I * t)) =
      selbergMollifier X
        (fun n => (selbergSqrtZetaTaperedCoeff X n : ℂ))
        ((1 / 2 : ℂ) - I * t) := by
  unfold selbergMollifier
  simp only [map_sum, map_mul, Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro n _hn
  congr 1
  exact conj_inv_nat_cpow_criticalLine_eq_neg n t

/-- On the critical line the two mollifier factors in Selberg's contour
integral are exactly the squared norm of the mollifier. -/
theorem selbergCompletedSqrtZetaMollifier_mul_reflection_eq_normSq
    (X : ℕ) (t : ℝ) :
    selbergMollifier X
          (fun n => (selbergSqrtZetaTaperedCoeff X n : ℂ))
          ((1 / 2 : ℂ) + I * t) *
        selbergMollifier X
          (fun n => (selbergSqrtZetaTaperedCoeff X n : ℂ))
          ((1 / 2 : ℂ) - I * t) =
      (Complex.normSq
        (selbergMollifier X
          (fun n => (selbergSqrtZetaTaperedCoeff X n : ℂ))
          ((1 / 2 : ℂ) + I * t)) : ℂ) := by
  let z : ℂ :=
    selbergMollifier X
      (fun n => (selbergSqrtZetaTaperedCoeff X n : ℂ))
      ((1 / 2 : ℂ) + I * t)
  have hreflect :
      (starRingEnd ℂ) z =
        selbergMollifier X
          (fun n => (selbergSqrtZetaTaperedCoeff X n : ℂ))
          ((1 / 2 : ℂ) - I * t) := by
    simpa only [z] using
      conj_selbergCompletedSqrtZetaMollifier_criticalLine_eq_neg X t
  change z * _ = (Complex.normSq z : ℂ)
  rw [← hreflect]
  exact Complex.mul_conj z

/-- Selberg's completed mollified function is continuous on the real line.
The only slightly non-formal point is continuity of `Gammaℝ` on the
critical line: Mathlib exposes an entire reciprocal of `Gammaℝ`, and the
reciprocal is nonzero there, so inversion recovers `Gammaℝ`. -/
theorem continuous_selbergCompletedMollifiedF (delta : ℝ) (X : ℕ) :
    Continuous (selbergCompletedMollifiedF delta X) := by
  have hline : Continuous (fun t : ℝ => ((1 / 2 : ℂ) + I * t)) := by
    fun_prop
  have hGammaInv : Continuous (fun t : ℝ =>
      (Gammaℝ ((1 / 2 : ℂ) + I * t))⁻¹) :=
    differentiable_Gammaℝ_inv.continuous.comp hline
  have hGamma : Continuous (fun t : ℝ =>
      Gammaℝ ((1 / 2 : ℂ) + I * t)) := by
    have h := hGammaInv.inv₀ (fun _t =>
      inv_ne_zero (Gammaℝ_ne_zero_of_re_pos (by norm_num)))
    convert h using 1
    ext t
    simp only [Pi.inv_apply, inv_inv]
  have hCompleted : Continuous hardyCompletedCriticalLine := by
    rw [show hardyCompletedCriticalLine = fun t : ℝ =>
        ‖Gammaℝ ((1 / 2 : ℂ) + I * t)‖ * hardyZ t by
      funext t
      exact hardyCompletedCriticalLine_eq_norm_GammaR_mul_hardyZ t]
    exact hGamma.norm.mul hardyZ_continuous
  have hMollifier : Continuous (fun t : ℝ =>
      selbergMollifier X
        (fun n => (selbergSqrtZetaTaperedCoeff X n : ℂ))
        ((1 / 2 : ℂ) + I * t)) :=
    continuous_selbergMollifier_criticalLine X _
  have hTilt : Continuous (fun t : ℝ =>
      Real.exp ((Real.pi / 4 - delta / 2) * t)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  unfold selbergCompletedMollifiedF
  exact (((continuous_const.mul hCompleted).mul
    (Complex.continuous_normSq.comp hMollifier)).mul hTilt)

/-- Exact conversion from the completed-zeta normalization to Hardy's
function.  This theorem records the global `-1/2` sign explicitly. -/
theorem selbergCompletedMollifiedF_eq_neg_factor_mul_hardyZ
    (delta : ℝ) (X : ℕ) (t : ℝ) :
    selbergCompletedMollifiedF delta X t =
      -(selbergCompletedMollifiedPositiveFactor delta X t) * hardyZ t := by
  rw [selbergCompletedMollifiedF,
    selbergCompletedMollifiedPositiveFactor,
    hardyCompletedCriticalLine_eq_norm_GammaR_mul_hardyZ]
  ring

/-- A negative value of Selberg's completed mollified function corresponds
to a positive value of Hardy's function because of the fixed global sign. -/
theorem hardyZ_pos_of_selbergCompletedMollifiedF_neg
    {delta : ℝ} {X : ℕ} {t : ℝ}
    (h : selbergCompletedMollifiedF delta X t < 0) :
    0 < hardyZ t := by
  rw [selbergCompletedMollifiedF_eq_neg_factor_mul_hardyZ] at h
  have hprod :
      0 < selbergCompletedMollifiedPositiveFactor delta X t * hardyZ t := by
    linarith
  rcases (mul_pos_iff.mp hprod) with hpos | hneg
  · exact hpos.2
  · exact False.elim
      ((not_lt_of_ge
        (selbergCompletedMollifiedPositiveFactor_nonneg delta X t)) hneg.1)

/-- A positive value of Selberg's completed mollified function corresponds
to a negative value of Hardy's function. -/
theorem hardyZ_neg_of_selbergCompletedMollifiedF_pos
    {delta : ℝ} {X : ℕ} {t : ℝ}
    (h : 0 < selbergCompletedMollifiedF delta X t) :
    hardyZ t < 0 := by
  rw [selbergCompletedMollifiedF_eq_neg_factor_mul_hardyZ] at h
  have hprod :
      selbergCompletedMollifiedPositiveFactor delta X t * hardyZ t < 0 := by
    linarith
  rcases (mul_neg_iff.mp hprod) with hpos | hneg
  · exact hpos.2
  · exact False.elim
      ((not_lt_of_ge
        (selbergCompletedMollifiedPositiveFactor_nonneg delta X t)) hneg.1)

/-- A negative-to-positive change of the completed mollified function is a
positive-to-negative change of Hardy's function. -/
theorem hasPosToNegLocalSignChangeAt_hardyZ_of_selbergCompleted_negToPos
    {delta : ℝ} {X : ℕ} {t : ℝ}
    (hchange : HasNegToPosLocalSignChangeAt
      (selbergCompletedMollifiedF delta X) t) :
    HasPosToNegLocalSignChangeAt hardyZ t := by
  constructor
  · intro epsilon hepsilon
    obtain ⟨x, hx, hneg⟩ := hchange.1 epsilon hepsilon
    exact ⟨x, hx, hardyZ_pos_of_selbergCompletedMollifiedF_neg hneg⟩
  · intro epsilon hepsilon
    obtain ⟨x, hx, hpos⟩ := hchange.2 epsilon hepsilon
    exact ⟨x, hx, hardyZ_neg_of_selbergCompletedMollifiedF_pos hpos⟩

/-- A positive-to-negative change of the completed mollified function is a
negative-to-positive change of Hardy's function. -/
theorem hasNegToPosLocalSignChangeAt_hardyZ_of_selbergCompleted_posToNeg
    {delta : ℝ} {X : ℕ} {t : ℝ}
    (hchange : HasPosToNegLocalSignChangeAt
      (selbergCompletedMollifiedF delta X) t) :
    HasNegToPosLocalSignChangeAt hardyZ t := by
  constructor
  · intro epsilon hepsilon
    obtain ⟨x, hx, hpos⟩ := hchange.1 epsilon hepsilon
    exact ⟨x, hx, hardyZ_neg_of_selbergCompletedMollifiedF_pos hpos⟩
  · intro epsilon hepsilon
    obtain ⟨x, hx, hneg⟩ := hchange.2 epsilon hepsilon
    exact ⟨x, hx, hardyZ_pos_of_selbergCompletedMollifiedF_neg hneg⟩

/-- Every local sign change detected by the completed Fourier--Mellin
function is a genuine local sign change of Hardy's `Z` function. -/
theorem hasLocalSignChangeAt_hardyZ_of_selbergCompletedMollifiedF
    {delta : ℝ} {X : ℕ} {t : ℝ}
    (hchange : HasLocalSignChangeAt
      (selbergCompletedMollifiedF delta X) t) :
    HasLocalSignChangeAt hardyZ t := by
  rcases hchange with hchange | hchange
  · exact Or.inr
      (hasPosToNegLocalSignChangeAt_hardyZ_of_selbergCompleted_negToPos
        hchange)
  · exact Or.inl
      (hasNegToPosLocalSignChangeAt_hardyZ_of_selbergCompleted_posToNeg
        hchange)

end HardyTheorem
