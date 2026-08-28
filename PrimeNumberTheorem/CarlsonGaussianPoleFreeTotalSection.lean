import PrimeNumberTheorem.CarlsonGaussianPoleFreeDerivMajorantBound

/-!
# A totalized Carlson Gaussian section

The analytic argument only needs the section on `1/2 ≤ Re(z) ≤ 4`, while
the generic `MemLp.toLp` differentiation bridge is most convenient for a
family defined on all of `ℂ`.  We therefore extend the section by zero outside
that strip.  On the wide inner strip the extension is locally equal to the
original analytic section, so its pointwise derivative is unchanged.
-/

open Complex Set MeasureTheory Filter

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- The concrete pole-free Carlson section on the controlled strip, extended
by zero outside it. -/
noncomputable def carlsonGaussianPoleFreeSectionTotal
    (Delta w : ℝ) (Y0 Y1 : ℕ) (z : ℂ) (t : ℝ) : ℂ :=
  if z.re ∈ Icc (1 / 2 : ℝ) 4 then
    carlsonGaussianHilbertSection Delta w
      (poleFreeTwoScaleMollifiedZetaError Y0 Y1) z t
  else 0

/-- The totalized family belongs to `L²(ℝ)` at every complex parameter. -/
theorem memLp_carlsonGaussianPoleFreeSectionTotal
    {Delta w : ℝ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1) (z : ℂ) :
    MemLp (carlsonGaussianPoleFreeSectionTotal Delta w Y0 Y1 z) 2 volume := by
  classical
  unfold carlsonGaussianPoleFreeSectionTotal
  split_ifs with hz
  · exact
      memLp_carlsonGaussian_poleFreeTwoScaleMollifiedZetaError_on_half_four
        hDelta hY0 hY01 hz
  · simp

/-- On the wide inner strip, totalization does not change the pointwise
complex derivative of the Gaussian section. -/
theorem hasDerivAt_carlsonGaussianPoleFreeSectionTotal_on_wide_inner_strip
    {Delta w : ℝ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (_hY0 : 1 ≤ Y0) (_hY01 : Y0 < Y1)
    {z : ℂ} (hzre : z.re ∈ Icc (7 / 12 : ℝ) (47 / 12)) (t : ℝ) :
    HasDerivAt
      (fun u : ℂ => carlsonGaussianPoleFreeSectionTotal Delta w Y0 Y1 u t)
      (carlsonGaussianHilbertSectionDeriv Delta w
        (poleFreeTwoScaleMollifiedZetaError Y0 Y1) z t) z := by
  classical
  have hnear : ∀ᶠ u in nhds z, u.re ∈ Icc (1 / 2 : ℝ) 4 := by
    filter_upwards [Metric.ball_mem_nhds z (by norm_num : (0 : ℝ) < 1 / 24)] with u hu
    have hdist : dist u z < (1 / 24 : ℝ) := Metric.mem_ball.mp hu
    have hreDiff : |u.re - z.re| < (1 / 24 : ℝ) := by
      calc
        |u.re - z.re| = |(u - z).re| := by simp
        _ ≤ ‖u - z‖ := Complex.abs_re_le_norm (u - z)
        _ = dist u z := by rw [dist_eq_norm]
        _ < 1 / 24 := hdist
    rw [abs_lt] at hreDiff
    constructor <;> linarith [hzre.1, hzre.2]
  have hEq :
      (fun u : ℂ => carlsonGaussianPoleFreeSectionTotal Delta w Y0 Y1 u t)
        =ᶠ[nhds z]
      (fun u : ℂ => carlsonGaussianHilbertSection Delta w
        (poleFreeTwoScaleMollifiedZetaError Y0 Y1) u t) := by
    filter_upwards [hnear] with u hu
    rw [carlsonGaussianPoleFreeSectionTotal, if_pos hu]
  have hzpos : 0 < (z + I * (t : ℂ)).re := by
    simp only [add_re, mul_re, I_re, ofReal_re, I_im, ofReal_im,
      zero_mul, one_mul, sub_self, add_zero]
    linarith [hzre.1]
  have hanalytic : AnalyticAt ℂ
      (poleFreeTwoScaleMollifiedZetaError Y0 Y1) (z + I * (t : ℂ)) :=
    analyticOnNhd_poleFreeTwoScaleMollifiedZetaError_re_gt
      (theta := 0) le_rfl Y0 Y1 _ hzpos
  have hbase := hasDerivAt_carlsonGaussianHilbertSection
    (Delta := Delta) (w := w) (H := poleFreeTwoScaleMollifiedZetaError Y0 Y1)
    (z := z) (t := t) (ne_of_gt hDelta) hanalytic
  exact hbase.congr_of_eventuallyEq hEq

end CarlsonZeroDensity
end PrimeNumberTheorem
