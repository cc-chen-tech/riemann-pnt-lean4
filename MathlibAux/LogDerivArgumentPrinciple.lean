import ZeroFreeRegion.MeromorphicAux
import MathlibAux.BoundaryRectResidue

open Complex Filter Set Topology
open scoped BigOperators Interval

namespace MathlibAux

/-- The logarithmic derivative of an analytic function counts its finitely many
zeros inside an axis-parallel rectangle, with analytic multiplicity. -/
theorem boundaryRectIntegral_logDeriv_eq_finite_zero_multiplicity_sum
    {f : ℂ → ℂ} {x0 x1 y0 y1 : ℝ}
    (zeros : Finset ℂ) (multiplicity : ℂ → ℕ)
    (hf : AnalyticOnNhd ℂ f ([[x0, x1]] ×ℂ [[y0, y1]]))
    (hzero : ∀ z ∈ ([[x0, x1]] ×ℂ [[y0, y1]]),
      f z = 0 ↔ z ∈ zeros)
    (hinside : ∀ rho ∈ zeros,
      x0 < rho.re ∧ rho.re < x1 ∧ y0 < rho.im ∧ rho.im < y1)
    (horder : ∀ rho ∈ zeros,
      analyticOrderAt f rho = multiplicity rho) :
    boundaryRectIntegral (logDeriv f) x0 x1 y0 y1 =
      (2 * Real.pi * I) *
        ∑ rho ∈ zeros, (multiplicity rho : ℂ) := by
  classical
  let K : Set ℂ := [[x0, x1]] ×ℂ [[y0, y1]]
  let raw : ℂ → ℂ := fun z =>
    logDeriv f z -
      ∑ rho ∈ zeros, (multiplicity rho : ℂ) * (z - rho)⁻¹
  let g := toMeromorphicNFOn raw K
  have hfK : AnalyticOnNhd ℂ f K := by
    simpa [K] using hf
  have hzeroK : ∀ z ∈ K, f z = 0 ↔ z ∈ zeros := by
    simpa [K] using hzero
  have hregular : AnalyticOnNhd ℂ g K := by
    exact
      ZeroFreeRegion.analyticOnNhd_toMeromorphicNFOn_logDeriv_sub_finset_principalParts
        hfK zeros multiplicity hzeroK horder
  have hrawMeromorphic : MeromorphicOn raw K := by
    exact ZeroFreeRegion.meromorphicOn_logDeriv_sub_finset_principalParts
      hfK.meromorphicOn zeros multiplicity
  have hboundary : ∀ z ∈ K,
      ¬(x0 < z.re ∧ z.re < x1 ∧ y0 < z.im ∧ z.im < y1) →
      logDeriv f z =
        g z + ∑ rho ∈ zeros, (z - rho)⁻¹ * (multiplicity rho : ℂ) := by
    intro z hzK hzBoundary
    have hzNotZero : z ∉ zeros := by
      intro hzZero
      exact hzBoundary (hinside z hzZero)
    have hfNe : f z ≠ 0 := by
      intro hfz
      exact hzNotZero ((hzeroK z hzK).mp hfz)
    have hfAnalytic : AnalyticAt ℂ f z := hfK z hzK
    have hlogAnalytic : AnalyticAt ℂ (logDeriv f) z :=
      hfAnalytic.deriv.div hfAnalytic hfNe
    have hsumAnalytic : AnalyticAt ℂ
        (fun w : ℂ =>
          ∑ rho ∈ zeros, (multiplicity rho : ℂ) * (w - rho)⁻¹) z := by
      apply Finset.analyticAt_fun_sum
      intro rho hrho
      have hzr : z ≠ rho := by
        intro h
        subst rho
        exact hzNotZero hrho
      exact analyticAt_const.mul
        ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hzr))
    have hrawAnalytic : AnalyticAt ℂ raw z := by
      simpa [raw] using hlogAnalytic.sub hsumAnalytic
    have hgEq : g z = raw z := by
      rw [show g z = toMeromorphicNFOn raw K z by rfl,
        toMeromorphicNFOn_eq_toMeromorphicNFAt hrawMeromorphic hzK,
        congrFun (toMeromorphicNFAt_eq_self.mpr
          hrawAnalytic.meromorphicNFAt) z]
    have hsumComm :
        (∑ rho ∈ zeros, (multiplicity rho : ℂ) * (z - rho)⁻¹) =
          ∑ rho ∈ zeros, (z - rho)⁻¹ * (multiplicity rho : ℂ) := by
      apply Finset.sum_congr rfl
      intro rho _hrho
      ring
    dsimp [raw] at hgEq
    rw [← hsumComm]
    linear_combination -hgEq
  calc
    boundaryRectIntegral (logDeriv f) x0 x1 y0 y1 =
      boundaryRectIntegral
        (fun z => g z +
          ∑ rho ∈ zeros, (z - rho)⁻¹ * (multiplicity rho : ℂ))
        x0 x1 y0 y1 := by
      apply boundaryRectIntegral_congr_of_eqOn_boundary
      simpa [K] using hboundary
    _ = (2 * Real.pi * I) *
        ∑ rho ∈ zeros, (multiplicity rho : ℂ) :=
      boundaryRectIntegral_eq_finite_simple_pole_residue_sum_of_differentiableOn
        zeros (fun rho => (multiplicity rho : ℂ))
        hregular.differentiableOn hinside

end MathlibAux
