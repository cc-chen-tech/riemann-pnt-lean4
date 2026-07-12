/-
Copyright (c) 2026 Riemann PNT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import MathlibAux.RectangleResidue
import PrimeNumberTheorem.ExplicitFormulaResidues

open Complex Filter Topology
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

/-- The concrete von Mangoldt explicit-formula integrand satisfies the finite
rectangle residue formula whenever `0`, the zeta pole, and all zeta zeros in
the closed rectangle lie in its interior. -/
theorem exists_rectangleBoundaryIntegral_explicitFormulaIntegrand_eq_residue_sum
    {x : ℝ} (hx : 0 < x) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hzero : (0 : ℂ) ∈ MathlibAux.openRectangle c R)
    (hzeta : ∀ p ∈ MathlibAux.closedRectangle c R,
      p = 1 ∨ riemannZeta p = 0 → p ∈ MathlibAux.openRectangle c R) :
    ∃ (poles : Finset ℂ) (residue : ℂ → ℂ),
      (∀ p ∈ poles, p ∈ MathlibAux.openRectangle c R) ∧
      MathlibAux.rectangleBoundaryIntegral (explicitFormulaIntegrand x) c R =
        (2 * Real.pi * I) * ∑ p ∈ poles, residue p := by
  classical
  have hcompact : IsCompact (MathlibAux.closedRectangle c R) := by
    simpa [MathlibAux.closedRectangle] using
      (isCompact_Icc.reProdIm isCompact_Icc)
  rcases
      exists_finite_explicitFormulaIntegrand_analytic_regularized_remainder
        hx hcompact with
    ⟨poles, residue, hpoles_mem, hpoles_classify, hoff_eq, hregular⟩
  let raw : ℂ → ℂ := fun z =>
    explicitFormulaIntegrand x z -
      ∑ p ∈ poles, (z - p)⁻¹ * residue p
  let g : ℂ → ℂ :=
    toMeromorphicNFOn raw (MathlibAux.closedRectangle c R)
  have hregular' :
      AnalyticOnNhd ℂ g (MathlibAux.closedRectangle c R) := by
    simpa [g, raw] using hregular
  have hpoles : ∀ p ∈ poles, p ∈ MathlibAux.openRectangle c R := by
    intro p hp
    by_cases hp0 : p = 0
    · simpa [hp0] using hzero
    have hpclosed : p ∈ MathlibAux.closedRectangle c R :=
      (hpoles_mem p hp).resolve_left hp0
    rcases hpoles_classify p hp with hp0' | hp1 | hpzeta
    · exact (hp0 hp0').elim
    · exact hzeta p hpclosed (Or.inl hp1)
    · exact hzeta p hpclosed (Or.inr hpzeta)
  have hboundary_eq :
      ∀ z ∈ MathlibAux.closedRectangle c R,
        z ∉ MathlibAux.openRectangle c R →
          explicitFormulaIntegrand x z =
            g z + ∑ p ∈ poles, (z - p)⁻¹ * residue p := by
    intro z hzclosed hzboundary
    have hz_not_pole : z ∉ poles := by
      intro hzpole
      exact hzboundary (hpoles z hzpole)
    have hz_eq := hoff_eq z hzclosed hz_not_pole
    change g z = raw z at hz_eq
    rw [hz_eq]
    simp only [raw]
    ring
  refine ⟨poles, residue, hpoles, ?_⟩
  calc
    MathlibAux.rectangleBoundaryIntegral (explicitFormulaIntegrand x) c R =
        MathlibAux.rectangleBoundaryIntegral
          (fun z : ℂ => g z +
            ∑ p ∈ poles, (z - p)⁻¹ * residue p) c R :=
      MathlibAux.rectangleBoundaryIntegral_congr_of_eqOn_boundary hR hboundary_eq
    _ = (2 * Real.pi * I) * ∑ p ∈ poles, residue p :=
      MathlibAux.rectangleBoundaryIntegral_eq_finite_simple_pole_residue_sum_of_differentiableOn
        hR poles residue hregular'.differentiableOn hpoles

end ExplicitFormulaResidues
end PrimeNumberTheorem
