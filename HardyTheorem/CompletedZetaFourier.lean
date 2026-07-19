import HardyTheorem.HardyCompletedCriticalLine
import MathlibAux.MellinLogIntegrability
import Mathlib.Analysis.MellinInversion

open Complex
open scoped FourierTransform

namespace HardyTheorem

/-!
# Fourier representation of the completed zeta function

Mathlib constructs the completed zeta function from a modified Jacobi-theta
Mellin kernel.  On the critical line, the Mellin-to-Fourier change of
variables turns that construction into an exact Fourier transform.
-/

/-- The logarithmic-coordinate kernel whose Fourier transform gives the
pole-removed completed zeta function on the critical line. -/
noncomputable def completedZetaLogKernel (u : ℝ) : ℂ :=
  MathlibAux.logMellinKernel
    (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (1 / 4 : ℝ) u

@[simp]
theorem completedZetaLogKernel_zero : completedZetaLogKernel 0 = 0 := by
  simp [completedZetaLogKernel, MathlibAux.logMellinKernel,
    WeakFEPair.f_modif]

/-- The logarithmic Mellin kernel is even.  This is the theta functional
equation in logarithmic coordinates and is useful for reducing all frequency
estimates to one half-line. -/
theorem completedZetaLogKernel_neg (u : ℝ) :
    completedZetaLogKernel (-u) = completedZetaLogKernel u := by
  have h := (HurwitzZeta.hurwitzEvenFEPair 0).hf_modif_FE
    (Real.exp (-u)) (Real.exp_pos (-u))
  change (HurwitzZeta.hurwitzEvenFEPair 0).f_modif
      (1 / Real.exp (-u)) =
    ((HurwitzZeta.hurwitzEvenFEPair 0).ε *
      (((Real.exp (-u)) ^
        (HurwitzZeta.hurwitzEvenFEPair 0).k : ℝ) : ℂ)) •
        (HurwitzZeta.hurwitzEvenFEPair 0).symm.f_modif
          (Real.exp (-u)) at h
  rw [HurwitzZeta.hurwitzEvenFEPair_zero_symm] at h
  simp only [HurwitzZeta.hurwitzEvenFEPair, one_mul, one_div,
    Real.exp_neg, inv_inv] at h
  have hrpow : (Real.exp u)⁻¹ ^ (2 : ℝ)⁻¹ = Real.exp (-u / 2) := by
    rw [Real.rpow_def_of_pos (inv_pos.mpr (Real.exp_pos u)),
      Real.log_inv, Real.log_exp]
    ring
  rw [hrpow] at h
  have hnamed :
      (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (Real.exp u) =
        (Real.exp (-u / 2) : ℂ) •
          (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (Real.exp u)⁻¹ := by
    simpa [HurwitzZeta.hurwitzEvenFEPair] using h
  unfold completedZetaLogKernel MathlibAux.logMellinKernel
  simp only [neg_neg, neg_mul, one_div]
  rw [show Real.exp (-u) = (Real.exp u)⁻¹ by exact Real.exp_neg u]
  rw [hnamed]
  have hscalar :
      Real.exp (-(4⁻¹ * -u)) * Real.exp (-u / 2) =
        Real.exp (-(4⁻¹ * u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hscalarSmul :
      Real.exp (-(4⁻¹ * -u)) • ((Real.exp (-u / 2) : ℝ) : ℂ) =
        ((Real.exp (-(4⁻¹ * u)) : ℝ) : ℂ) := by
    rw [Complex.real_smul]
    exact_mod_cast hscalar
  let z := (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (Real.exp u)⁻¹
  calc
    Real.exp (-(4⁻¹ * -u)) •
        (((Real.exp (-u / 2) : ℝ) : ℂ) • z) =
        (Real.exp (-(4⁻¹ * -u)) •
          ((Real.exp (-u / 2) : ℝ) : ℂ)) • z :=
      (IsScalarTower.smul_assoc _ _ _).symm
    _ = ((Real.exp (-(4⁻¹ * u)) : ℝ) : ℂ) • z :=
      congrArg (fun c : ℂ => c • z) hscalarSmul
    _ = Real.exp (-(4⁻¹ * u)) • z := by
      simp [Algebra.smul_def]

/-- On the critical line the two elementary pole terms in the completed zeta
function combine into a positive real rational kernel. -/
theorem criticalLine_pole_sum_eq (t : ℝ) :
    1 / ((1 / 2 : ℂ) + I * t) +
        1 / (1 - ((1 / 2 : ℂ) + I * t)) =
      ((1 / (t ^ 2 + 1 / 4) : ℝ) : ℂ) := by
  have hs : (1 / 2 : ℂ) + I * t ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hones : 1 - ((1 / 2 : ℂ) + I * t) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hden : t ^ 2 + (1 / 4 : ℝ) ≠ 0 := by positivity
  rw [one_div_add_one_div hs hones]
  field_simp [hs, hones, hden]
  push_cast
  ring_nf
  simp [I_sq]

set_option maxHeartbeats 400000 in
/-- The completed-zeta Fourier kernel is integrable.  This is the analytic
hypothesis needed to use its pointwise Fourier transform, obtained directly
from the Mellin convergence built into Mathlib's strong functional-equation
pair. -/
theorem integrable_completedZetaLogKernel :
    MeasureTheory.Integrable completedZetaLogKernel := by
  have hmellin : MellinConvergent
      (HurwitzZeta.hurwitzEvenFEPair 0).f_modif ((1 / 4 : ℝ) : ℂ) :=
    ((HurwitzZeta.hurwitzEvenFEPair 0).toStrongFEPair.hasMellin
      ((1 / 4 : ℝ) : ℂ)).1
  simpa only [completedZetaLogKernel] using
    (MathlibAux.integrable_logMellinKernel_of_mellinConvergent
      (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (1 / 4 : ℝ) hmellin)

/-- Exact critical-line Fourier formula for the pole-removed completed zeta
function.  Mathlib's Fourier variable uses the `2 * pi` normalization, hence
the frequency `t / (4 * pi)`. -/
theorem completedRiemannZeta₀_criticalLine_eq_fourier (t : ℝ) :
    completedRiemannZeta₀ ((1 / 2 : ℂ) + I * t) =
      𝓕 completedZetaLogKernel (t / (4 * Real.pi)) / 2 := by
  rw [completedRiemannZeta₀, HurwitzZeta.completedHurwitzZetaEven₀,
    WeakFEPair.Λ₀, mellin_eq_fourier]
  have hkernel :
      (fun u : ℝ =>
        Real.exp (-(((1 / 2 : ℂ) + I * t) / 2).re * u) •
          (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (Real.exp (-u))) =
        completedZetaLogKernel := by
    funext u
    dsimp only [completedZetaLogKernel]
    congr 1
    norm_num
  have hfreq :
      (((1 / 2 : ℂ) + I * t) / 2).im / (2 * Real.pi) =
        t / (4 * Real.pi) := by
    norm_num
    field_simp [Real.pi_ne_zero]
    ring
  rw [hfreq]
  exact congrArg
    (fun f : ℝ → ℂ => 𝓕 f (t / (4 * Real.pi)) / 2) hkernel

/-- Restoring the two elementary pole terms gives the corresponding exact
formula for the meromorphic completed zeta function. -/
theorem completedRiemannZeta_criticalLine_eq_fourier_sub_poles (t : ℝ) :
    completedRiemannZeta ((1 / 2 : ℂ) + I * t) =
      𝓕 completedZetaLogKernel (t / (4 * Real.pi)) / 2 -
        1 / ((1 / 2 : ℂ) + I * t) -
        1 / (1 - ((1 / 2 : ℂ) + I * t)) := by
  rw [completedRiemannZeta_eq,
    completedRiemannZeta₀_criticalLine_eq_fourier]

end HardyTheorem
