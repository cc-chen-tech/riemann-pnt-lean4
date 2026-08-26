import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Slope

open Complex Filter Set
open scoped Topology

namespace HardyTheorem

/-!
# Analytic square roots on simply connected complex domains

The covering-space construction in `Complex.exists_continuousOn_pow_eq` gives a continuous
square root.  On an open complex domain this root is automatically analytic: if `f ^ 2 = g`, then
away from the diagonal

`slope f x y = slope g x y / (f y + f x)`.

Continuity of `f` and nonvanishing of `g` make the denominator tend to the nonzero number
`2 * f x`, so the right-hand side has a complex derivative limit.
-/

theorem analyticOnNhd_of_continuousOn_sq_eq {U : Set ℂ} (hU : IsOpen U)
    {f g : ℂ → ℂ} (hf : ContinuousOn f U) (hg : AnalyticOnNhd ℂ g U)
    (hsq : ∀ z ∈ U, f z ^ 2 = g z) (hg0 : ∀ z ∈ U, g z ≠ 0) :
    AnalyticOnNhd ℂ f U := by
  rw [analyticOnNhd_iff_differentiableOn hU]
  intro x hx
  have hfx : f x ≠ 0 := by
    intro h
    apply hg0 x hx
    rw [← hsq x hx, h, zero_pow (by decide : 2 ≠ 0)]
  have htwofx : f x + f x ≠ 0 := by
    simpa [two_mul] using mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hfx
  have hfc : ContinuousAt f x := hf.continuousAt (hU.mem_nhds hx)
  have hden : Tendsto (fun y ↦ f y + f x) (𝓝[≠] x) (𝓝 (f x + f x)) :=
    (hfc.tendsto.mono_left inf_le_left).add tendsto_const_nhds
  have hgderiv : HasDerivAt g (deriv g x) x :=
    (hg x hx).differentiableAt.hasDerivAt
  have hquot :
      Tendsto (fun y ↦ slope g x y / (f y + f x)) (𝓝[≠] x)
        (𝓝 (deriv g x / (f x + f x))) :=
    hgderiv.tendsto_slope.div hden htwofx
  have hfderiv : HasDerivAt f (deriv g x / (f x + f x)) x := by
    rw [hasDerivAt_iff_tendsto_slope]
    apply Tendsto.congr' _ hquot
    have hUev : ∀ᶠ y in 𝓝[≠] x, y ∈ U :=
      mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hx)
    have hden_ne : ∀ᶠ y in 𝓝[≠] x, f y + f x ≠ 0 :=
      hden.eventually_ne htwofx
    filter_upwards [hUev, eventually_mem_nhdsWithin, hden_ne] with y hyU hyx hsum
    rw [slope_def_field, slope_def_field, ← hsq y hyU, ← hsq x hx]
    field_simp [sub_ne_zero.mpr hyx, hsum]
    ring
  exact hfderiv.differentiableAt.differentiableWithinAt

theorem exists_analyticOnNhd_sq_eq {U : Set ℂ} (hUc : IsSimplyConnected U)
    (hUo : IsOpen U) {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U)
    (hg0 : ∀ z ∈ U, g z ≠ 0) :
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f U ∧ ∀ z, f z ^ 2 = g z := by
  have hzero : 0 ∉ g '' U := by
    rintro ⟨z, hz, hgz⟩
    exact hg0 z hz hgz
  rcases Complex.exists_continuousOn_pow_eq hUc hUo hg.continuousOn hzero
      (by decide : 2 ≠ 0) with ⟨f, hf, hsq⟩
  exact ⟨f, analyticOnNhd_of_continuousOn_sq_eq hUo hf hg
    (fun z _ ↦ hsq z) hg0, hsq⟩

end HardyTheorem
