import PrimeNumberTheorem.CarlsonZeroDetector
import HardyTheorem.TwoScaleSelbergMollifier

open Complex

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-!
# Carlson's detector for the two-scale plateau mollifier

This file changes only the finite mollifier inside Carlson's detector.  It
establishes the exact analytic and zero-inclusion interface before any
mean-square or far-right estimate is supplied.
-/

/-- The zeta product error for the two-scale mollifier. -/
noncomputable def twoScaleMollifiedZetaError
    (Y0 Y1 : ℕ) (s : ℂ) : ℂ :=
  riemannZeta s * HardyTheorem.twoScaleSelbergMollifier Y0 Y1 s - 1

/-- Carlson's quadratic zero detector built from the two-scale error. -/
noncomputable def twoScaleCarlsonZeroDetector
    (Y0 Y1 : ℕ) (s : ℂ) : ℂ :=
  1 - twoScaleMollifiedZetaError Y0 Y1 s ^ 2

/-- The pole-free version of the two-scale detector. -/
noncomputable def regularizedTwoScaleCarlsonZeroDetector
    (Y0 Y1 : ℕ) (s : ℂ) : ℂ :=
  let q := ZeroFreeRegion.riemannZetaPoleUnitAtOne s
  let m := HardyTheorem.twoScaleSelbergMollifier Y0 Y1 s
  q * m * (2 * (s - 1) - q * m)

/-- Away from the zeta pole, the two-scale mollified error is analytic. -/
theorem analyticAt_twoScaleMollifiedZetaError_of_ne_one
    (Y0 Y1 : ℕ) {s : ℂ} (hs1 : s ≠ 1) :
    AnalyticAt ℂ (twoScaleMollifiedZetaError Y0 Y1) s := by
  have hzeta : AnalyticAt ℂ riemannZeta s :=
    ZeroFreeRegion.analyticOnNhd_riemannZeta_ne_one s hs1
  have hm : AnalyticAt ℂ
      (HardyTheorem.twoScaleSelbergMollifier Y0 Y1) s :=
    HardyTheorem.analyticAt_twoScaleSelbergMollifier Y0 Y1 s
  unfold twoScaleMollifiedZetaError
  exact (hzeta.mul hm).sub analyticAt_const

/-- Carlson's two-scale detector is analytic away from the zeta pole. -/
theorem analyticAt_twoScaleCarlsonZeroDetector_of_ne_one
    (Y0 Y1 : ℕ) {s : ℂ} (hs1 : s ≠ 1) :
    AnalyticAt ℂ (twoScaleCarlsonZeroDetector Y0 Y1) s := by
  unfold twoScaleCarlsonZeroDetector
  exact analyticAt_const.sub
    ((analyticAt_twoScaleMollifiedZetaError_of_ne_one Y0 Y1 hs1).pow 2)

/-- The regularized detector is analytic on every closed-right sub-half-plane
inside `Re(s)>0`. -/
theorem analyticOnNhd_regularizedTwoScaleCarlsonZeroDetector_re_gt
    {theta : ℝ} (htheta : 0 ≤ theta) (Y0 Y1 : ℕ) :
    AnalyticOnNhd ℂ (regularizedTwoScaleCarlsonZeroDetector Y0 Y1)
      {s : ℂ | theta < s.re} := by
  intro s hs
  have hq : AnalyticAt ℂ ZeroFreeRegion.riemannZetaPoleUnitAtOne s :=
    ZeroFreeRegion.analyticOnNhd_riemannZetaPoleUnitAtOne_re_gt
      htheta s hs
  have hm : AnalyticAt ℂ
      (HardyTheorem.twoScaleSelbergMollifier Y0 Y1) s :=
    HardyTheorem.analyticAt_twoScaleSelbergMollifier Y0 Y1 s
  have hlinear : AnalyticAt ℂ (fun z : ℂ => 2 * (z - 1)) s :=
    analyticAt_const.mul (analyticAt_id.sub analyticAt_const)
  unfold regularizedTwoScaleCarlsonZeroDetector
  exact (hq.mul hm).mul (hlinear.sub (hq.mul hm))

/-- Algebraic factorization exposing every zeta zero. -/
theorem twoScaleCarlsonZeroDetector_factorization
    (Y0 Y1 : ℕ) (s : ℂ) :
    twoScaleCarlsonZeroDetector Y0 Y1 s =
      (riemannZeta s * HardyTheorem.twoScaleSelbergMollifier Y0 Y1 s) *
        (2 - riemannZeta s *
          HardyTheorem.twoScaleSelbergMollifier Y0 Y1 s) := by
  unfold twoScaleCarlsonZeroDetector twoScaleMollifiedZetaError
  ring

/-- Every zeta zero is a zero of the two-scale Carlson detector. -/
theorem twoScaleCarlsonZeroDetector_eq_zero_of_zeta_eq_zero
    {Y0 Y1 : ℕ} {s : ℂ} (hz : riemannZeta s = 0) :
    twoScaleCarlsonZeroDetector Y0 Y1 s = 0 := by
  rw [twoScaleCarlsonZeroDetector_factorization, hz]
  simp

/-- Every nontrivial zeta zero occurs in the two-scale detector with at
least its zeta multiplicity. -/
theorem analyticOrderNatAt_riemannZeta_le_twoScaleCarlsonZeroDetector
    {Y0 Y1 : ℕ} {rho : ℂ} (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    (hrho : RiemannHypothesis.IsNontrivialZero rho) :
    analyticOrderNatAt riemannZeta rho ≤
      analyticOrderNatAt (twoScaleCarlsonZeroDetector Y0 Y1) rho := by
  let m : ℂ → ℂ := HardyTheorem.twoScaleSelbergMollifier Y0 Y1
  let g : ℂ → ℂ := fun s => m s * (2 - riemannZeta s * m s)
  have hrho1 : rho ≠ 1 := by
    intro hone
    have hre := congrArg Complex.re hone
    simp at hre
    linarith [hrho.2.2]
  have hzeta : AnalyticAt ℂ riemannZeta rho :=
    ZeroFreeRegion.analyticOnNhd_riemannZeta_ne_one rho hrho1
  have hm : AnalyticAt ℂ m rho := by
    exact HardyTheorem.analyticAt_twoScaleSelbergMollifier Y0 Y1 rho
  have hcomplement : AnalyticAt ℂ
      (fun s : ℂ => 2 - riemannZeta s * m s) rho :=
    analyticAt_const.sub (hzeta.mul hm)
  have hg : AnalyticAt ℂ g rho := hm.mul hcomplement
  have hzetaFinite : analyticOrderAt riemannZeta rho ≠ ⊤ :=
    ZeroFreeRegion.analyticOrderAt_riemannZeta_ne_top_of_ne_one hrho1
  have hcomplementNe : (2 - riemannZeta rho * m rho : ℂ) ≠ 0 := by
    rw [hrho.1]
    norm_num
  have hcomplementOrder : analyticOrderAt
      (fun s : ℂ => 2 - riemannZeta s * m s) rho = 0 :=
    hcomplement.analyticOrderAt_eq_zero.mpr hcomplementNe
  have hmFinite : analyticOrderAt m rho ≠ ⊤ :=
    HardyTheorem.analyticOrderAt_twoScaleSelbergMollifier_ne_top
      hY0 hY01 rho
  have hgFinite : analyticOrderAt g rho ≠ ⊤ := by
    rw [show analyticOrderAt g rho = analyticOrderAt m rho +
        analyticOrderAt (fun s : ℂ => 2 - riemannZeta s * m s) rho by
      exact analyticOrderAt_mul hm hcomplement,
      hcomplementOrder, add_zero]
    exact hmFinite
  have hfactor : twoScaleCarlsonZeroDetector Y0 Y1 = riemannZeta * g := by
    funext s
    simp only [Pi.mul_apply]
    simpa [g, m, mul_assoc] using
      twoScaleCarlsonZeroDetector_factorization Y0 Y1 s
  rw [hfactor,
    analyticOrderNatAt_mul hzeta hg hzetaFinite hgFinite]
  exact Nat.le_add_right _ _

/-- Away from the removable points, regularization multiplies the original
detector by `(s-1)^2`. -/
theorem regularizedTwoScaleCarlsonZeroDetector_eq_sub_one_sq_mul
    {Y0 Y1 : ℕ} {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    regularizedTwoScaleCarlsonZeroDetector Y0 Y1 s =
      (s - 1) ^ 2 * twoScaleCarlsonZeroDetector Y0 Y1 s := by
  unfold regularizedTwoScaleCarlsonZeroDetector
  rw [ZeroFreeRegion.riemannZetaPoleUnitAtOne_eq_sub_one_mul_riemannZeta
    hs0 hs1,
    twoScaleCarlsonZeroDetector_factorization]
  ring

end CarlsonZeroDensity
end PrimeNumberTheorem
