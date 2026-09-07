import PrimeNumberTheorem.CarlsonTwoScaleDetector

/-!
# Pole-free two-scale mollified zeta error

This is the analytic function used in the local Hilbert-valued three-lines
argument.  It agrees with `((s - 1) / (s + 1)) * (ζ(s) M(s) - 1)` away
from the zeta pole, but is defined through the analytic pole unit at `s = 1`.
-/

open Complex

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- The pole-free version of the two-scale mollified zeta error. -/
noncomputable def poleFreeTwoScaleMollifiedZetaError
    (Y0 Y1 : ℕ) (s : ℂ) : ℂ :=
  (ZeroFreeRegion.riemannZetaPoleUnitAtOne s *
      HardyTheorem.twoScaleSelbergMollifier Y0 Y1 s - (s - 1)) /
    (s + 1)

/-- The pole-free two-scale error is analytic on every right half-plane
contained in `Re(s) > 0`. -/
theorem analyticOnNhd_poleFreeTwoScaleMollifiedZetaError_re_gt
    {theta : ℝ} (htheta : 0 ≤ theta) (Y0 Y1 : ℕ) :
    AnalyticOnNhd ℂ (poleFreeTwoScaleMollifiedZetaError Y0 Y1)
      {s : ℂ | theta < s.re} := by
  intro s hs
  have hq : AnalyticAt ℂ ZeroFreeRegion.riemannZetaPoleUnitAtOne s :=
    ZeroFreeRegion.analyticOnNhd_riemannZetaPoleUnitAtOne_re_gt
      htheta s hs
  have hm : AnalyticAt ℂ
      (HardyTheorem.twoScaleSelbergMollifier Y0 Y1) s :=
    HardyTheorem.analyticAt_twoScaleSelbergMollifier Y0 Y1 s
  have hlinear : AnalyticAt ℂ (fun z : ℂ => z - 1) s :=
    analyticAt_id.sub analyticAt_const
  have hdenAnalytic : AnalyticAt ℂ (fun z : ℂ => z + 1) s :=
    analyticAt_id.add analyticAt_const
  have hden : s + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    change theta < s.re at hs
    linarith
  unfold poleFreeTwoScaleMollifiedZetaError
  exact ((hq.mul hm).sub hlinear).div hdenAnalytic hden

/-- Away from `0`, `1`, and the harmless denominator zero `-1`, the
pole-free definition is exactly the paper's regularizing factor times the
ordinary mollified zeta error. -/
theorem poleFreeTwoScaleMollifiedZetaError_eq_mul
    {Y0 Y1 : ℕ} {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hsneg1 : s ≠ -1) :
    poleFreeTwoScaleMollifiedZetaError Y0 Y1 s =
      (s - 1) / (s + 1) * twoScaleMollifiedZetaError Y0 Y1 s := by
  have hden : s + 1 ≠ 0 := by
    intro h
    apply hsneg1
    linear_combination h
  rw [poleFreeTwoScaleMollifiedZetaError,
    ZeroFreeRegion.riemannZetaPoleUnitAtOne_eq_sub_one_mul_riemannZeta
      hs0 hs1]
  unfold twoScaleMollifiedZetaError
  field_simp [hden]

/-- On every vertical line in the right half-plane, the pole-free error is
continuous as a function of height. -/
theorem continuous_poleFreeTwoScaleMollifiedZetaError_vertical
    {x : ℝ} (hx : 0 < x) (Y0 Y1 : ℕ) :
    Continuous fun t : ℝ =>
      poleFreeTwoScaleMollifiedZetaError Y0 Y1
        ((x : ℂ) + I * (t : ℂ)) := by
  rw [continuous_iff_continuousAt]
  intro t
  let point : ℝ → ℂ := fun u => (x : ℂ) + I * (u : ℂ)
  have hpoint : ContinuousAt point t := by
    dsimp [point]
    fun_prop
  have hre : 0 < (point t).re := by
    simpa [point] using hx
  have hanalytic :
      AnalyticAt ℂ (poleFreeTwoScaleMollifiedZetaError Y0 Y1) (point t) :=
    analyticOnNhd_poleFreeTwoScaleMollifiedZetaError_re_gt
      (theta := 0) le_rfl Y0 Y1 (point t) hre
  simpa [point, Function.comp_def] using hanalytic.continuousAt.comp hpoint

end CarlsonZeroDensity
end PrimeNumberTheorem
