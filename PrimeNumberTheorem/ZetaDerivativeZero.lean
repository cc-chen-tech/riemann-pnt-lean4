/-
Copyright (c) 2026 Riemann PNT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.NumberTheory.Harmonic.ZetaAsymp

open Complex

namespace PrimeNumberTheorem

local notation "γ" => (Real.eulerMascheroniConstant : ℂ)

/-- The regular factor left after extracting the simple zero of `1 / Gammaℝ`
at the origin. -/
private noncomputable def gammaRInvRegularFactor (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (Real.pi : ℂ) ^ (s / 2) * (Gamma (s / 2 + 1))⁻¹

private lemma gammaRInvRegularFactor_zero : gammaRInvRegularFactor 0 = 1 / 2 := by
  simp [gammaRInvRegularFactor, Gamma_one]

private lemma hasDerivAt_gammaRInvRegularFactor_zero :
    HasDerivAt gammaRInvRegularFactor
      ((Complex.log Real.pi + γ) / 4) 0 := by
  let p : ℂ → ℂ := fun s => (Real.pi : ℂ) ^ (s / 2)
  let g : ℂ → ℂ := fun s => (Gamma (s / 2 + 1))⁻¹
  have hp : HasDerivAt p (Complex.log Real.pi / 2) 0 := by
    have h := ((hasDerivAt_id (0 : ℂ)).div_const 2).const_cpow
      (c := (Real.pi : ℂ)) (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
    convert h using 1 <;> simp <;> ring
  have hinner : HasDerivAt (fun s : ℂ => s / 2 + 1) (1 / 2) 0 :=
    ((hasDerivAt_id (0 : ℂ)).div_const 2).add_const 1
  have hg : HasDerivAt g (γ / 2) 0 := by
    have houter : DifferentiableAt ℂ (fun z : ℂ => (Gamma z)⁻¹) (0 / 2 + 1) :=
      differentiable_one_div_Gamma.differentiableAt
    have houterDeriv : deriv (fun z : ℂ => (Gamma z)⁻¹) (0 / 2 + 1) = γ := by
      norm_num
      rw [deriv_fun_inv'' (c := Gamma)
        (Complex.hasDerivAt_Gamma_one.differentiableAt) (by simp [Gamma_one])]
      simp [Complex.hasDerivAt_Gamma_one.deriv, Gamma_one]
    have hcomp := houter.hasDerivAt.comp 0 hinner
    rw [houterDeriv] at hcomp
    convert hcomp using 1 <;> simp <;> ring
  have hmul := (hp.const_mul (1 / 2 : ℂ)).mul hg
  convert hmul using 1 <;>
    simp [p, g] <;> ring

private lemma inv_Gammaℝ_eq_mul_regularFactor (s : ℂ) :
    (Gammaℝ s)⁻¹ = s * gammaRInvRegularFactor s := by
  rw [show (Gammaℝ s)⁻¹ =
      (Real.pi : ℂ) ^ (s / 2) * (Gamma (s / 2))⁻¹ by
    rw [Gammaℝ_def, mul_inv, ← cpow_neg]
    congr 2
    ring]
  rw [one_div_Gamma_eq_self_mul_one_div_Gamma_add_one]
  dsimp [gammaRInvRegularFactor]
  ring

private noncomputable def zetaAtZeroRegularForm (s : ℂ) : ℂ :=
  s * gammaRInvRegularFactor s *
      (completedRiemannZeta₀ s - 1 / (1 - s)) -
    gammaRInvRegularFactor s

private lemma riemannZeta_eq_zetaAtZeroRegularForm :
    riemannZeta = zetaAtZeroRegularForm := by
  funext s
  by_cases hs : s = 0
  · subst s
    rw [riemannZeta_zero]
    simp [zetaAtZeroRegularForm, gammaRInvRegularFactor_zero]
    ring
  · rw [riemannZeta_def_of_ne_zero hs, div_eq_mul_inv,
      inv_Gammaℝ_eq_mul_regularFactor, completedRiemannZeta_eq]
    dsimp [zetaAtZeroRegularForm]
    field_simp
    ring

private lemma completedRiemannZeta₀_zero :
    completedRiemannZeta₀ 0 =
      (γ - Complex.log (4 * Real.pi)) / 2 + 1 := by
  rw [← completedRiemannZeta₀_one_sub 0]
  simpa using completedRiemannZeta₀_one

private lemma hasDerivAt_zetaAtZeroRegularForm_zero :
    HasDerivAt zetaAtZeroRegularForm
      (-(Complex.log (2 * Real.pi)) / 2) 0 := by
  let h := gammaRInvRegularFactor
  let B : ℂ → ℂ := fun s => completedRiemannZeta₀ s - 1 / (1 - s)
  have hh := hasDerivAt_gammaRInvRegularFactor_zero
  have hB : DifferentiableAt ℂ B 0 := by
    dsimp [B]
    have hden : DifferentiableAt ℂ (fun s : ℂ => 1 - s) 0 := by fun_prop
    have hone : DifferentiableAt ℂ (fun _s : ℂ => (1 : ℂ)) 0 := by fun_prop
    exact differentiable_completedZeta₀.differentiableAt.sub
      (hone.div hden (by norm_num))
  have hmain := (((hasDerivAt_id (0 : ℂ)).mul hh).mul hB.hasDerivAt).sub hh
  apply hmain.congr_deriv
  simp [Function.id_def, B, completedRiemannZeta₀_zero,
    gammaRInvRegularFactor_zero]
  have hlog : Complex.log (4 * Real.pi) + Complex.log Real.pi =
      2 * Complex.log (2 * Real.pi) := by
    have hreal : Real.log (4 * Real.pi) + Real.log Real.pi =
        2 * Real.log (2 * Real.pi) := by
      calc
        _ = Real.log ((4 * Real.pi) * Real.pi) :=
          (Real.log_mul (by positivity : 4 * Real.pi ≠ 0)
            (by positivity : Real.pi ≠ 0)).symm
        _ = Real.log ((2 * Real.pi) ^ 2) := by congr 1; ring
        _ = _ := by rw [Real.log_pow]; norm_num
    have h4 : Complex.log (4 * (Real.pi : ℂ)) =
        (Real.log (4 * Real.pi) : ℂ) := by
      rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul,
        Complex.ofReal_log (by positivity : 0 ≤ 4 * Real.pi)]
    have hpi : Complex.log (Real.pi : ℂ) = (Real.log Real.pi : ℂ) := by
      rw [Complex.ofReal_log (by positivity : 0 ≤ Real.pi)]
    have h2 : Complex.log (2 * (Real.pi : ℂ)) =
        (Real.log (2 * Real.pi) : ℂ) := by
      rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul,
        Complex.ofReal_log (by positivity : 0 ≤ 2 * Real.pi)]
    rw [h4, hpi, h2]
    exact_mod_cast hreal
  calc
    (2⁻¹ : ℂ) * ((γ - Complex.log (4 * Real.pi)) / 2) -
          (Complex.log Real.pi + γ) / 4 =
        -(Complex.log (4 * Real.pi) + Complex.log Real.pi) / 4 := by ring
    _ = -(Complex.log (2 * Real.pi)) / 2 := by rw [hlog]; ring

/-- The classical value `ζ'(0) = -log(2π)/2`. -/
theorem deriv_riemannZeta_zero :
    deriv riemannZeta 0 = -(Real.log (2 * Real.pi) : ℂ) / 2 := by
  rw [riemannZeta_eq_zetaAtZeroRegularForm]
  rw [hasDerivAt_zetaAtZeroRegularForm_zero.deriv]
  congr 2
  simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using
    (Complex.ofReal_log (by positivity : 0 ≤ 2 * Real.pi)).symm

/-- The logarithmic derivative of the Riemann zeta function at zero. -/
theorem deriv_riemannZeta_zero_div_riemannZeta_zero :
    deriv riemannZeta 0 / riemannZeta 0 =
      (Real.log (2 * Real.pi) : ℂ) := by
  rw [deriv_riemannZeta_zero, riemannZeta_zero]
  ring

end PrimeNumberTheorem
