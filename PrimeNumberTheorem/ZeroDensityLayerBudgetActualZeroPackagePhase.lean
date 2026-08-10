import PrimeNumberTheorem.ZeroDensityLayerBudgetFinitePhaseNaturalSampling
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualZeroPackageSelectedHeightCarlsonTransfer

/-!
# Phase decomposition of the actual equal-real-part zero package

This file identifies the actual zeta-zero package contribution with a common
real power times a finite Fourier sum.  It is the analytic bridge from the
mean-square zero package to natural-floor sampling.
-/

namespace PrimeNumberTheorem

open ZeroForcedOscillation

/-- The finite phase sum attached to the actual equal-real-part zeta-zero
package. -/
noncomputable def actualEqualRealPartZeroPackagePhase
    (T beta y : ℝ) : ℂ :=
  finitePhaseSum (equalRealPartZeroPackage T beta)
    (fun rho => (analyticOrderNatAt riemannZeta rho : ℂ) / rho)
    Complex.im y

/-- A positive real base raised to a complex power splits into its real
power and its pure phase. -/
theorem ofReal_cpow_eq_rpow_mul_phase
    {x : ℝ} (hx : 0 < x) (rho : ℂ) :
    (x : ℂ) ^ rho =
      ((x ^ rho.re : ℝ) : ℂ) *
        Complex.exp (Complex.I * (rho.im * Real.log x : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr hx.ne')]
  rw [← Complex.ofReal_log hx.le]
  have hexponent :
      (Real.log x : ℂ) * rho =
        (Real.log x * rho.re : ℝ) +
          Complex.I * (rho.im * Real.log x : ℂ) := by
    calc
      (Real.log x : ℂ) * rho =
          (Real.log x : ℂ) *
            ((rho.re : ℂ) + (rho.im : ℂ) * Complex.I) := by
              rw [Complex.re_add_im]
      _ =
          (Real.log x * rho.re : ℝ) +
            Complex.I * (rho.im * Real.log x : ℂ) := by
              push_cast
              ring
  rw [hexponent, Complex.exp_add, ← Complex.ofReal_exp,
    ← Real.rpow_def_of_pos hx]

/-- The actual package contribution factors as `x^beta` times its finite
phase sum. -/
theorem equalRealPartZeroPackageContribution_eq_rpow_mul_phase
    {x T beta : ℝ} (hx : 0 < x) :
    equalRealPartZeroPackageContribution x T beta =
      ((x ^ beta : ℝ) : ℂ) *
        actualEqualRealPartZeroPackagePhase T beta (Real.log x) := by
  rw [equalRealPartZeroPackageContribution,
    actualEqualRealPartZeroPackagePhase, finitePhaseSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho hrho
  have hre : rho.re = beta :=
    (mem_equalRealPartZeroPackage.mp hrho).2.2
  rw [ofReal_cpow_eq_rpow_mul_phase hx rho, hre]
  ring

/-- The complex relative PNT main term of the complete actual package. -/
noncomputable def actualEqualRealPartZeroPackagePNTMain
    (x T beta : ℝ) : ℂ :=
  -(x : ℂ)⁻¹ * equalRealPartZeroPackageContribution x T beta

/-- The relative package main term is exactly the target power amplitude
times the finite phase sum. -/
theorem actualEqualRealPartZeroPackagePNTMain_eq_target_mul_phase
    {x T beta : ℝ} (hx : 0 < x) :
    actualEqualRealPartZeroPackagePNTMain x T beta =
      -(targetZeroPowerAmplitude beta x : ℂ) *
        actualEqualRealPartZeroPackagePhase T beta (Real.log x) := by
  rw [actualEqualRealPartZeroPackagePNTMain,
    equalRealPartZeroPackageContribution_eq_rpow_mul_phase hx]
  simp only [targetZeroPowerAmplitude]
  rw [Real.rpow_sub_one hx.ne']
  push_cast
  field_simp [hx.ne']

/-- Once a dynamic height covers `T`, its visible complex zero sum is the
canonical actual package main term. -/
theorem dynamicVisibleClusterPNTZeroSum_eq_actualZeroPackagePNTMain
    (H : ℝ → ℝ) {x T beta : ℝ} (hTH : T ≤ H x) :
    dynamicVisibleClusterPNTZeroSum H
        (equalRealPartZeroPackage T beta) x =
      actualEqualRealPartZeroPackagePNTMain x T beta := by
  simpa [actualEqualRealPartZeroPackagePNTMain] using
    dynamicVisibleClusterPNTZeroSum_equalRealPartZeroPackage
      H hTH

end PrimeNumberTheorem
