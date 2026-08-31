import Mathlib

/-! The exact norm and unit-phase correction of the positive Gamma coefficient. -/

open Complex
open scoped ComplexConjugate

namespace HardyTheorem.AFE

/-- The frequency-independent factor in the positive-phase Gamma boundary value. -/
noncomputable def criticalGammaPrefactor (t : ℝ) : ℂ :=
  let s : ℂ := (1 / 2 : ℂ) + I * t
  ((2 * Real.pi : ℝ) : ℂ) ^ (s - 1) *
    (Complex.exp (I * ((Real.pi / 2 : ℝ) : ℂ) * (1 - s)) * Complex.Gamma (1 - s))

private theorem norm_Gamma_half_sub_I_sq (t : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) - I * t)‖ ^ 2 = Real.pi / Real.cosh (Real.pi * t) := by
  let z : ℂ := (1 / 2 : ℂ) - I * t
  have hz : 1 - z = conj z := by
    apply Complex.ext <;> norm_num [z]
  have hsin : Complex.sin ((Real.pi : ℂ) * z) = (Real.cosh (Real.pi * t) : ℂ) := by
    have harg : (Real.pi : ℂ) * z = (Real.pi : ℂ) / 2 - ((Real.pi * t : ℝ) : ℂ) * I := by
      dsimp only [z]
      push_cast
      ring
    rw [harg, Complex.sin_pi_div_two_sub, Complex.cos_mul_I, ← Complex.ofReal_cosh]
  have h := Complex.Gamma_mul_Gamma_one_sub z
  rw [hz, Complex.Gamma_conj, Complex.mul_conj, hsin, ← Complex.ofReal_div] at h
  have hr := Complex.ofReal_injective h
  simpa only [Complex.normSq_eq_norm_sq, z] using hr

/-- Exact norm: the raw Gamma coefficient is not a unit phase. -/
theorem norm_criticalGammaPrefactor_sq (t : ℝ) :
    ‖criticalGammaPrefactor t‖ ^ 2 = 1 / (1 + Real.exp (-2 * Real.pi * t)) := by
  let s : ℂ := (1 / 2 : ℂ) + I * t
  have hbase : 0 < 2 * Real.pi := by positivity
  have hpow : ‖((2 * Real.pi : ℝ) : ℂ) ^ (s - 1)‖ ^ 2 = 1 / (2 * Real.pi) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hbase]
    have hre : (s - 1).re = -(1 / 2 : ℝ) := by simp [s]; ring
    rw [hre, sq, ← Real.rpow_add hbase]
    norm_num [Real.rpow_neg_one, one_div]
  have hexp : ‖Complex.exp (I * ((Real.pi / 2 : ℝ) : ℂ) * (1 - s))‖ ^ 2 =
      Real.exp (Real.pi * t) := by
    rw [Complex.norm_exp, sq, ← Real.exp_add]
    congr 1
    simp [s]
    ring
  have hgamma : ‖Complex.Gamma (1 - s)‖ ^ 2 = Real.pi / Real.cosh (Real.pi * t) := by
    have hz : 1 - s = (1 / 2 : ℂ) - I * t := by dsimp only [s]; ring
    rw [hz]
    exact norm_Gamma_half_sub_I_sq t
  change ‖((2 * Real.pi : ℝ) : ℂ) ^ (s - 1) *
    (Complex.exp (I * ((Real.pi / 2 : ℝ) : ℂ) * (1 - s)) * Complex.Gamma (1 - s))‖ ^ 2 = _
  rw [norm_mul, norm_mul, mul_pow, mul_pow, hpow, hexp, hgamma]
  calc
    _ = Real.exp (Real.pi * t) / (2 * Real.cosh (Real.pi * t)) := by
      field_simp [Real.pi_ne_zero, (Real.cosh_pos (Real.pi * t)).ne']
    _ = _ := by
      apply (div_eq_div_iff (by positivity : (2 : ℝ) * Real.cosh (Real.pi * t) ≠ 0)
        (by positivity : 1 + Real.exp (-2 * Real.pi * t) ≠ 0)).mpr
      have he : Real.exp (Real.pi * t) * Real.exp (-2 * Real.pi * t) =
          Real.exp (-(Real.pi * t)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [Real.cosh_eq]
      nlinarith [he]

/-- The coefficient is nonzero and has norm at most one at every real height. -/
theorem norm_criticalGammaPrefactor_pos_and_le_one (t : ℝ) :
    0 < ‖criticalGammaPrefactor t‖ ∧ ‖criticalGammaPrefactor t‖ ≤ 1 := by
  have hsq := norm_criticalGammaPrefactor_sq t
  have hp : 0 < 1 / (1 + Real.exp (-2 * Real.pi * t)) := by positivity
  have hle : 1 / (1 + Real.exp (-2 * Real.pi * t)) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith [Real.exp_pos (-2 * Real.pi * t)]
  constructor <;> nlinarith [norm_nonneg (criticalGammaPrefactor t)]

/-- Normalize the actual coefficient; its correction is exponentially small.
The weak AFE needs no identification of this phase with a theta-function phase. -/
theorem exists_unitPhase_close_criticalGammaPrefactor (t : ℝ) :
    ∃ U : ℂ, ‖U‖ = 1 ∧
      ‖criticalGammaPrefactor t - U‖ ≤ Real.exp (-2 * Real.pi * t) := by
  let P := criticalGammaPrefactor t
  let r : ℝ := ‖P‖
  let U : ℂ := P / (r : ℂ)
  have hr0 : 0 < r := (norm_criticalGammaPrefactor_pos_and_le_one t).1
  have hr1 : r ≤ 1 := (norm_criticalGammaPrefactor_pos_and_le_one t).2
  have hU : ‖U‖ = 1 := by
    dsimp only [U]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
    change r / r = 1
    exact div_self hr0.ne'
  have hP : P = (r : ℂ) * U := by
    dsimp only [U]
    field_simp [Complex.ofReal_ne_zero.mpr hr0.ne']
  have hnorm : ‖P - U‖ = 1 - r := by
    have heq : P - U = ((r - 1 : ℝ) : ℂ) * U := by
      calc
        _ = (r : ℂ) * U - U := by rw [← hP]
        _ = _ := by push_cast; ring
    rw [heq, norm_mul, hU, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr hr1)]
    ring
  have hsmall : 1 - r ≤ Real.exp (-2 * Real.pi * t) := by
    have he0 := (Real.exp_pos (-2 * Real.pi * t)).le
    have hsq : r ^ 2 = 1 / (1 + Real.exp (-2 * Real.pi * t)) :=
      norm_criticalGammaPrefactor_sq t
    have hprod : r ^ 2 * (1 + Real.exp (-2 * Real.pi * t)) = 1 :=
      (eq_div_iff (by positivity)).mp hsq
    have hr2 : r ^ 2 ≤ r := by nlinarith [mul_nonneg hr0.le (sub_nonneg.mpr hr1)]
    have hr2one : r ^ 2 ≤ 1 := hr2.trans hr1
    have hmul := mul_le_mul_of_nonneg_right hr2one he0
    nlinarith
  refine ⟨U, hU, ?_⟩
  change ‖P - U‖ ≤ _
  rw [hnorm]
  exact hsmall

end HardyTheorem.AFE
