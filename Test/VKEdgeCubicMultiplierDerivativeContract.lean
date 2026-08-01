import PrimeNumberTheorem.VKEdgeDesmoothedLeftAmplitude

open Complex

#check PrimeNumberTheorem.ExplicitFormulaResidues.norm_deriv_cubicKernelMultiplier_le_eight_div_norm

example {rho : ℂ} {h : ℝ} (hh : 0 < h) (hrho : rho ≠ 0)
    (hsmall : h * ‖rho‖ ≤ 1 / 2) :
    ‖deriv (fun z : ℂ =>
        PrimeNumberTheorem.ExplicitFormulaResidues.cubicKernelMultiplier z h) rho‖ ≤
      8 / ‖rho‖ :=
  PrimeNumberTheorem.ExplicitFormulaResidues.norm_deriv_cubicKernelMultiplier_le_eight_div_norm
    hh hrho hsmall
