import HardyTheorem.SelbergSqrtZetaSignedCompleteDenominator

/-!
# The full taper after arithmetic-zeta convolution

On a complete denominator range, convolution with arithmetic zeta changes
the negative logarithmic taper of the square-root-zeta coefficient into the
corresponding positive logarithmic taper of its zeta convolution.  This file
records that identity globally, pointwise, and on a complete coprime ray.
-/

open scoped BigOperators ArithmeticFunction

namespace HardyTheorem

/-- Let `C = zeta * selbergSqrtZetaCoeff`.  Convolution of the full linear
taper with arithmetic zeta is exactly
`C + (log X)⁻¹ • (C pmul log)`. -/
theorem zeta_mul_selbergSqrtZetaFullTapered
    (X : ℕ) :
    (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        selbergSqrtZetaFullTapered X =
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          selbergSqrtZetaCoeff +
        (Real.log X)⁻¹ •
          (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
            selbergSqrtZetaCoeff).pmul ArithmeticFunction.log) := by
  rw [selbergSqrtZetaFullTapered, mul_sub]
  rw [mul_smul_comm, zeta_mul_selbergSqrtZetaLogCoeff]
  simp

/-- Pointwise form of `zeta_mul_selbergSqrtZetaFullTapered`: if
`C = zeta * selbergSqrtZetaCoeff`, then the complete denominator coefficient
at `n` is `C(n) * (1 + log n / log X)`. -/
theorem zeta_mul_selbergSqrtZetaFullTapered_apply
    (X n : ℕ) :
    (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        selbergSqrtZetaFullTapered X) n) =
      (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          selbergSqrtZetaCoeff) n) *
        (1 + Real.log n / Real.log X) := by
  rw [zeta_mul_selbergSqrtZetaFullTapered]
  simp only [ArithmeticFunction.add_apply, ArithmeticFunction.smul_map,
    smul_eq_mul, ArithmeticFunction.pmul_apply,
    ArithmeticFunction.log_apply]
  rw [div_eq_mul_inv]
  ring_nf

/-- On the complete part of a positive coprime ray, the four terms produced
by expanding the two linear tapers recombine exactly into two visible taper
factors: a negative numerator taper and a positive denominator taper. -/
theorem selbergSqrtZetaSignedCoprimeRayComplete_fullTaper_eq_twoFactors
    (N X a b : ℕ) :
    (∑ d ∈
        selbergSqrtZetaSignedCoprimeRayCompleteScaleSupport N X a b,
      (d : ℝ)⁻¹ *
        selbergSqrtZetaFullTapered X (a * d) *
        (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          selbergSqrtZetaFullTapered X) (b * d))) =
      ∑ d ∈
        selbergSqrtZetaSignedCoprimeRayCompleteScaleSupport N X a b,
      (d : ℝ)⁻¹ *
        (selbergSqrtZetaCoeff (a * d) *
          (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
            selbergSqrtZetaCoeff) (b * d))) *
        (1 - Real.log (a * d) / Real.log X) *
        (1 + Real.log (b * d) / Real.log X) := by
  classical
  apply Finset.sum_congr rfl
  intro d _hd
  rw [selbergSqrtZetaFullTapered_apply,
    zeta_mul_selbergSqrtZetaFullTapered_apply]
  simp only [Nat.mul_comm a d, Nat.mul_comm b d]
  simp only [Nat.cast_mul]
  ring_nf

/-- Explicit four-term version of the complete-ray identity.  The zero-log,
two single-log, and double-log terms collapse without estimates to the two
linear taper factors displayed on the right. -/
theorem
    selbergSqrtZetaSignedCoprimeRayComplete_logExpansion_eq_twoFactors
    (N X a b : ℕ) :
    (∑ d ∈
        selbergSqrtZetaSignedCoprimeRayCompleteScaleSupport N X a b,
      (d : ℝ)⁻¹ *
        (selbergSqrtZetaCoeff (a * d) *
            (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
              selbergSqrtZetaCoeff) (b * d)) -
          (Real.log X)⁻¹ *
            (selbergSqrtZetaLogCoeff (a * d) *
                (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
                  selbergSqrtZetaCoeff) (b * d)) +
              selbergSqrtZetaCoeff (a * d) *
                (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
                  selbergSqrtZetaLogCoeff) (b * d))) +
          (Real.log X)⁻¹ ^ 2 *
            selbergSqrtZetaLogCoeff (a * d) *
              (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
                selbergSqrtZetaLogCoeff) (b * d)))) =
      ∑ d ∈
        selbergSqrtZetaSignedCoprimeRayCompleteScaleSupport N X a b,
      (d : ℝ)⁻¹ *
        (selbergSqrtZetaCoeff (a * d) *
          (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
            selbergSqrtZetaCoeff) (b * d))) *
        (1 - Real.log (a * d) / Real.log X) *
        (1 + Real.log (b * d) / Real.log X) := by
  classical
  apply Finset.sum_congr rfl
  intro d _hd
  have hZL := congrArg
    (fun f : ArithmeticFunction ℝ => f (b * d))
    zeta_mul_selbergSqrtZetaLogCoeff
  simp only [ArithmeticFunction.neg_apply,
    ArithmeticFunction.pmul_apply,
    ArithmeticFunction.log_apply] at hZL
  have hL :
      selbergSqrtZetaLogCoeff (a * d) =
        selbergSqrtZetaCoeff (a * d) * Real.log (a * d) := by
    simp [selbergSqrtZetaLogCoeff,
      ArithmeticFunction.pmul_apply,
      ArithmeticFunction.log_apply]
  rw [hL, hZL]
  simp only [Nat.cast_mul]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ring_nf

end HardyTheorem
