import HardyTheorem.SelbergS12HighBound

open Complex Filter Set

namespace HardyTheorem

/-!
# Selberg S12: the punctured neighborhood of the pole

Near `s = 1`, the reciprocal of zeta agrees off the center with the analytic
model `(s - 1) / u(s)`, where `u(1) = 1`.  Hence it vanishes linearly along
the punctured one-line.
-/

theorem exists_norm_inv_riemannZeta_oneLine_le_two_mul_abs_near_zero :
    ∃ r : ℝ, 0 < r ∧
      ∀ t : ℝ, t ≠ 0 → |t| < r →
        ‖(riemannZeta ((1 : ℂ) + I * t))⁻¹‖ ≤ 2 * |t| := by
  have hunitAnalytic :
      AnalyticAt ℂ
        (fun s : ℂ => (ZeroFreeRegion.riemannZetaPoleUnitAtOne s)⁻¹) 1 :=
    ZeroFreeRegion.analyticAt_riemannZetaPoleUnitAtOne.inv
      (by rw [ZeroFreeRegion.riemannZetaPoleUnitAtOne_one]; exact one_ne_zero)
  have hunitCont : ContinuousAt
      (fun s : ℂ => ‖(ZeroFreeRegion.riemannZetaPoleUnitAtOne s)⁻¹‖) 1 :=
    hunitAnalytic.continuousAt.norm
  have hunitBound : ∀ᶠ s : ℂ in nhds 1,
      ‖(ZeroFreeRegion.riemannZetaPoleUnitAtOne s)⁻¹‖ ≤ 2 := by
    have hcenter :
        ‖(ZeroFreeRegion.riemannZetaPoleUnitAtOne (1 : ℂ))⁻¹‖ < 2 := by
      rw [ZeroFreeRegion.riemannZetaPoleUnitAtOne_one]
      norm_num
    exact hunitCont.tendsto.eventually (eventually_le_nhds hcenter)
  have heq := ZeroFreeRegion.eventuallyEq_inv_riemannZeta_simpleZeroAtOne
  have heq' : ∀ᶠ s : ℂ in nhds 1,
      s ∈ ({1}ᶜ : Set ℂ) →
        (riemannZeta s)⁻¹ = ZeroFreeRegion.riemannZetaReciprocalModelAtOne s :=
    eventually_nhdsWithin_iff.mp heq
  have hlocal : ∀ᶠ s : ℂ in nhds 1,
      s ≠ 1 →
        (riemannZeta s)⁻¹ = ZeroFreeRegion.riemannZetaReciprocalModelAtOne s ∧
          ‖(ZeroFreeRegion.riemannZetaPoleUnitAtOne s)⁻¹‖ ≤ 2 := by
    filter_upwards [heq', hunitBound] with s hsEq hsBound
    intro hs1
    exact ⟨hsEq (by simpa using hs1), hsBound⟩
  rcases Metric.eventually_nhds_iff.mp hlocal with ⟨r, hr, hlocalr⟩
  refine ⟨r, hr, ?_⟩
  intro t ht0 htr
  let s : ℂ := (1 : ℂ) + I * t
  have hs1 : s ≠ 1 := by
    intro hs
    have him := congrArg Complex.im hs
    simp [s] at him
    exact ht0 him
  have hdist : dist s 1 = |t| := by
    rw [dist_eq_norm]
    simp [s, norm_mul]
  have hsLocal := hlocalr (by simpa [hdist] using htr) hs1
  calc
    ‖(riemannZeta s)⁻¹‖ =
        ‖ZeroFreeRegion.riemannZetaReciprocalModelAtOne s‖ := by
      rw [hsLocal.1]
    _ = ‖s - 1‖ *
        ‖(ZeroFreeRegion.riemannZetaPoleUnitAtOne s)⁻¹‖ := by
      rw [ZeroFreeRegion.riemannZetaReciprocalModelAtOne, norm_mul]
    _ ≤ ‖s - 1‖ * 2 :=
      mul_le_mul_of_nonneg_left hsLocal.2 (norm_nonneg _)
    _ = 2 * |t| := by
      have : ‖s - 1‖ = |t| := by
        simpa [dist_eq_norm] using hdist
      rw [this]
      ring

end HardyTheorem
