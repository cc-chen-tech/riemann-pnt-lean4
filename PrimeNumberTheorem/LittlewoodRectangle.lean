import MathlibAux.BoundaryRectResidue
import ZeroFreeRegion.MeromorphicAux

open Complex Set
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- Weighted argument-principle identity on an axis-parallel rectangle.

The hypotheses identify all zeros in the closed rectangle and supply their
analytic multiplicities.  Strict interior containment excludes boundary
zeros.  Removing the finite logarithmic principal parts gives an analytic
remainder, so the weighted rectangle residue formula applies without any
simple-zero assumption. -/
theorem boundaryRectIntegral_weighted_logDeriv_eq_zeroMultiplicitySum
    {f : ℂ → ℂ} {x0 x1 y0 y1 : ℝ}
    (poles : Finset ℂ) (multiplicity : ℂ → ℕ) (anchor : ℂ)
    (hf : AnalyticOnNhd ℂ f ([[x0, x1]] ×ℂ [[y0, y1]]))
    (hzero : ∀ z ∈ ([[x0, x1]] ×ℂ [[y0, y1]] : Set ℂ),
      f z = 0 ↔ z ∈ poles)
    (horder : ∀ rho ∈ poles,
      analyticOrderAt f rho = multiplicity rho)
    (hpoles : ∀ rho ∈ poles,
      x0 < rho.re ∧ rho.re < x1 ∧ y0 < rho.im ∧ rho.im < y1) :
    MathlibAux.boundaryRectIntegral
        (fun z : ℂ => (z - anchor) * logDeriv f z)
        x0 x1 y0 y1 =
      (2 * Real.pi * I) *
        ∑ rho ∈ poles, (rho - anchor) * (multiplicity rho : ℂ) := by
  classical
  let U : Set ℂ := [[x0, x1]] ×ℂ [[y0, y1]]
  let raw : ℂ → ℂ := fun z =>
    logDeriv f z -
      ∑ rho ∈ poles, (multiplicity rho : ℂ) * (z - rho)⁻¹
  let regular : ℂ → ℂ := toMeromorphicNFOn raw U
  have hfU : AnalyticOnNhd ℂ f U := by
    simpa [U] using hf
  have hzeroU : ∀ z ∈ U, f z = 0 ↔ z ∈ poles := by
    simpa [U] using hzero
  have hrawMeromorphic : MeromorphicOn raw U := by
    simpa [raw] using
      ZeroFreeRegion.meromorphicOn_logDeriv_sub_finset_principalParts
        hfU.meromorphicOn poles multiplicity
  have hregular : AnalyticOnNhd ℂ regular U := by
    dsimp [regular]
    exact
      ZeroFreeRegion.analyticOnNhd_toMeromorphicNFOn_logDeriv_sub_finset_principalParts
        hfU poles multiplicity hzeroU horder
  have hboundaryNonzero : ∀ z ∈ U,
      ¬(x0 < z.re ∧ z.re < x1 ∧ y0 < z.im ∧ z.im < y1) →
        f z ≠ 0 := by
    intro z hz hnot hzeroz
    exact hnot (hpoles z ((hzeroU z hz).mp hzeroz))
  have hrawAnalyticBoundary : ∀ z ∈ U,
      ¬(x0 < z.re ∧ z.re < x1 ∧ y0 < z.im ∧ z.im < y1) →
        AnalyticAt ℂ raw z := by
    intro z hz hnot
    have hlog : AnalyticAt ℂ (logDeriv f) z :=
      (hfU z hz).deriv.div (hfU z hz) (hboundaryNonzero z hz hnot)
    have hsum : AnalyticAt ℂ
        (fun w : ℂ =>
          ∑ rho ∈ poles, (multiplicity rho : ℂ) * (w - rho)⁻¹) z := by
      apply Finset.analyticAt_fun_sum
      intro rho hrho
      have hzr : z ≠ rho := by
        intro heq
        subst z
        exact hnot (hpoles rho hrho)
      exact analyticAt_const.mul
        ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hzr))
    simpa [raw] using hlog.sub hsum
  have hregularEqBoundary : ∀ z ∈ U,
      ¬(x0 < z.re ∧ z.re < x1 ∧ y0 < z.im ∧ z.im < y1) →
        regular z = raw z := by
    intro z hz hnot
    dsimp [regular]
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hrawMeromorphic hz]
    rw [toMeromorphicNFAt_eq_self.2
      (hrawAnalyticBoundary z hz hnot).meromorphicNFAt]
  have hcontour :
      MathlibAux.boundaryRectIntegral
          (fun z : ℂ => (z - anchor) * logDeriv f z)
          x0 x1 y0 y1 =
        MathlibAux.boundaryRectIntegral
          (fun z : ℂ =>
            (z - anchor) *
              (regular z +
                ∑ rho ∈ poles,
                  (z - rho)⁻¹ * (multiplicity rho : ℂ)))
          x0 x1 y0 y1 := by
    apply MathlibAux.boundaryRectIntegral_congr_of_eqOn_boundary
    intro z hz hnot
    have hzU : z ∈ U := by simpa [U] using hz
    rw [hregularEqBoundary z hzU hnot]
    dsimp [raw]
    have hsumComm :
        (∑ rho ∈ poles,
            (multiplicity rho : ℂ) * (z - rho)⁻¹) =
          ∑ rho ∈ poles,
            (z - rho)⁻¹ * (multiplicity rho : ℂ) := by
      apply Finset.sum_congr rfl
      intro rho hrho
      ring
    rw [hsumComm]
    ring
  rw [hcontour]
  exact
    MathlibAux.boundaryRectIntegral_eq_finite_simple_pole_weighted_residue_sum_of_differentiableOn
      poles (fun rho => (multiplicity rho : ℂ)) anchor
      hregular.differentiableOn hpoles

end CarlsonZeroDensity
end PrimeNumberTheorem
