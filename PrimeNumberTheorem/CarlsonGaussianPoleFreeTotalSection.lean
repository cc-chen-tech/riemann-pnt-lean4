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

/-- At every point of the open controlled strip, totalization is locally
equal to the original Gaussian section and hence has the same derivative. -/
theorem hasDerivAt_carlsonGaussianPoleFreeSectionTotal_on_open_strip
    {Delta w : ℝ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (_hY0 : 1 ≤ Y0) (_hY01 : Y0 < Y1)
    {z : ℂ} (hzleft : 1 / 2 < z.re) (hzright : z.re < 4) (t : ℝ) :
    HasDerivAt
      (fun u : ℂ => carlsonGaussianPoleFreeSectionTotal Delta w Y0 Y1 u t)
      (carlsonGaussianHilbertSectionDeriv Delta w
        (poleFreeTwoScaleMollifiedZetaError Y0 Y1) z t) z := by
  classical
  have hnear : ∀ᶠ u in nhds z, u.re ∈ Icc (1 / 2 : ℝ) 4 := by
    have hopen : IsOpen {u : ℂ | 1 / 2 < u.re ∧ u.re < 4} :=
      (isOpen_lt continuous_const continuous_re).inter
        (isOpen_lt continuous_re continuous_const)
    filter_upwards [hopen.mem_nhds ⟨hzleft, hzright⟩] with u hu
    exact ⟨hu.1.le, hu.2.le⟩
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
    linarith
  have hanalytic : AnalyticAt ℂ
      (poleFreeTwoScaleMollifiedZetaError Y0 Y1) (z + I * (t : ℂ)) :=
    analyticOnNhd_poleFreeTwoScaleMollifiedZetaError_re_gt
      (theta := 0) le_rfl Y0 Y1 _ hzpos
  have hbase := hasDerivAt_carlsonGaussianHilbertSection
    (Delta := Delta) (w := w) (H := poleFreeTwoScaleMollifiedZetaError Y0 Y1)
    (z := z) (t := t) (ne_of_gt hDelta) hanalytic
  exact hbase.congr_of_eventuallyEq hEq

/-- The earlier fixed wide-strip interface, retained as a corollary. -/
theorem hasDerivAt_carlsonGaussianPoleFreeSectionTotal_on_wide_inner_strip
    {Delta w : ℝ} {Y0 Y1 : ℕ}
    (hDelta : 0 < Delta) (hY0 : 1 ≤ Y0) (hY01 : Y0 < Y1)
    {z : ℂ} (hzre : z.re ∈ Icc (7 / 12 : ℝ) (47 / 12)) (t : ℝ) :
    HasDerivAt
      (fun u : ℂ => carlsonGaussianPoleFreeSectionTotal Delta w Y0 Y1 u t)
      (carlsonGaussianHilbertSectionDeriv Delta w
        (poleFreeTwoScaleMollifiedZetaError Y0 Y1) z t) z := by
  apply hasDerivAt_carlsonGaussianPoleFreeSectionTotal_on_open_strip
    hDelta hY0 hY01
  · linarith [hzre.1]
  · linarith [hzre.2]

end CarlsonZeroDensity
end PrimeNumberTheorem
