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
