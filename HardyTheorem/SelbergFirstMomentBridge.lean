import HardyTheorem.SelbergCompletedMollified
import HardyTheorem.SelbergSqrtZetaAbsLower

open Complex

namespace HardyTheorem

/-!
# The exact modulus bridge for Selberg's first moment

The Fourier--Mellin identity uses the reflected product
`zeta(s) * psi(s) * psi(1-s)`.  The first-moment contour argument instead
uses the holomorphic auxiliary product `zeta(s) * psi(s)^2`, whose ordinary
Dirichlet series has constant coefficient one on `re(s) = 2`.

These products need not be equal as complex numbers on the critical line.
Their norms are equal there because the tapered coefficients are real.  The
theorem below records the resulting exact bridge to the already formalized
real function `selbergCompletedMollifiedF`; only the positive archimedean
Gamma factor and the exponential tilt remain.
-/

/-- Exact critical-line modulus identity used by Selberg S4.  In particular,
any lower bound for the absolute mass of the square-root-zeta mollified Hardy
function transfers to the completed Fourier--Mellin function after inserting
the displayed positive weight. -/
theorem abs_selbergCompletedMollifiedF_eq_gamma_tilt_mul_abs_sqrtZeta
    (delta : ℝ) (X : ℕ) (t : ℝ) :
    |selbergCompletedMollifiedF delta X t| =
      (1 / (2 * Real.sqrt (2 * Real.pi))) *
        ‖Gammaℝ ((1 / 2 : ℂ) + I * t)‖ *
        Real.exp ((Real.pi / 4 - delta / 2) * t) *
        |selbergSqrtZetaMollifiedHardyZ X t| := by
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) :=
    Real.sqrt_pos.2 (mul_pos (by norm_num) Real.pi_pos)
  have hcoeff : 0 ≤ (1 / (2 * Real.sqrt (2 * Real.pi)) : ℝ) :=
    (one_div_pos.mpr (mul_pos (by norm_num) hsqrt)).le
  have hgamma : 0 ≤ ‖Gammaℝ ((1 / 2 : ℂ) + I * t)‖ := norm_nonneg _
  have hnormSq : 0 ≤ Complex.normSq
      (selbergMollifier X
        (fun n => (selbergSqrtZetaTaperedCoeff X n : ℂ))
        ((1 / 2 : ℂ) + I * t)) := Complex.normSq_nonneg _
  have hexp : 0 ≤ Real.exp ((Real.pi / 4 - delta / 2) * t) :=
    (Real.exp_pos _).le
  rw [selbergCompletedMollifiedF,
    hardyCompletedCriticalLine_eq_norm_GammaR_mul_hardyZ,
    selbergSqrtZetaMollifiedHardyZ, selbergMollifiedHardyZ]
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_neg,
    abs_of_nonneg hcoeff,
    abs_of_nonneg hgamma, abs_of_nonneg hnormSq, abs_of_nonneg hexp]
  ring

end HardyTheorem
