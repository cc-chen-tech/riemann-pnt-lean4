import HardyTheorem.CompletedZetaFourier

open Complex
open scoped FourierTransform

namespace HardyTheorem

example (t : ℝ) :
    completedRiemannZeta₀ ((1 / 2 : ℂ) + I * t) =
      𝓕 completedZetaLogKernel (t / (4 * Real.pi)) / 2 :=
  completedRiemannZeta₀_criticalLine_eq_fourier t

example (t : ℝ) :
    completedRiemannZeta ((1 / 2 : ℂ) + I * t) =
      𝓕 completedZetaLogKernel (t / (4 * Real.pi)) / 2 -
        1 / ((1 / 2 : ℂ) + I * t) -
        1 / (1 - ((1 / 2 : ℂ) + I * t)) :=
  completedRiemannZeta_criticalLine_eq_fourier_sub_poles t

end HardyTheorem

#print axioms HardyTheorem.integrable_completedZetaLogKernel

#print axioms HardyTheorem.completedRiemannZeta₀_criticalLine_eq_fourier
#print axioms HardyTheorem.completedRiemannZeta_criticalLine_eq_fourier_sub_poles
