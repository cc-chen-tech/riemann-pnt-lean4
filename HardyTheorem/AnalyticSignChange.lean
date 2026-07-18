import Mathlib.Analysis.Analytic.Order
import Mathlib.Algebra.Ring.Parity

open Filter Set Topology

namespace HardyTheorem

/-- If a real analytic function changes from negative values immediately to
the left of a zero to positive values immediately to its right, then the
analytic order of that zero is odd. -/
theorem odd_analyticOrderNatAt_of_local_sign_change
    {f : ℝ → ℝ} {c : ℝ}
    (hf : AnalyticAt ℝ f c)
    (hfinite : analyticOrderAt f c ≠ ⊤)
    (hleft : ∀ ε > 0, ∃ x ∈ Set.Ioo (c - ε) c, f x < 0)
    (hright : ∀ ε > 0, ∃ x ∈ Set.Ioo c (c + ε), 0 < f x) :
    Odd (analyticOrderNatAt f c) := by
  by_contra hodd
  have heven : Even (analyticOrderNatAt f c) := Nat.not_odd_iff_even.mp hodd
  obtain ⟨g, hg, hgc, hfactor⟩ :=
    (hf.analyticOrderNatAt_eq_iff hfinite).mp rfl
  rcases lt_or_gt_of_ne hgc with hgcneg | hgcpos
  · have hgneg : ∀ᶠ x in 𝓝 c, g x < 0 :=
      hg.continuousAt.eventually_lt continuousAt_const hgcneg
    have hnonpos : ∀ᶠ x in 𝓝 c, f x ≤ 0 := by
      filter_upwards [hfactor, hgneg] with x hfx hgx
      rw [hfx]
      simpa [smul_eq_mul] using
        mul_nonpos_of_nonneg_of_nonpos (heven.pow_nonneg (x - c)) hgx.le
    rw [Metric.eventually_nhds_iff] at hnonpos
    obtain ⟨ε, hε, hbound⟩ := hnonpos
    obtain ⟨x, hx, hxpos⟩ := hright ε hε
    have hdist : dist x c < ε := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hx.1, hx.2]
    exact (not_lt_of_ge (hbound hdist)) hxpos
  · have hgpos : ∀ᶠ x in 𝓝 c, 0 < g x :=
      continuousAt_const.eventually_lt hg.continuousAt hgcpos
    have hnonneg : ∀ᶠ x in 𝓝 c, 0 ≤ f x := by
      filter_upwards [hfactor, hgpos] with x hfx hgx
      rw [hfx]
      simpa [smul_eq_mul] using
        mul_nonneg (heven.pow_nonneg (x - c)) hgx.le
    rw [Metric.eventually_nhds_iff] at hnonneg
    obtain ⟨ε, hε, hbound⟩ := hnonneg
    obtain ⟨x, hx, hxneg⟩ := hleft ε hε
    have hdist : dist x c < ε := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hx.1, hx.2]
    exact (not_lt_of_ge (hbound hdist)) hxneg

end HardyTheorem
