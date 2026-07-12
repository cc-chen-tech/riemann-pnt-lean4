/-
Copyright (c) 2026 Riemann PNT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import MathlibAux.RectangleResidue
import PrimeNumberTheorem.ExplicitFormulaAux
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
    ⟨poles, residue, hpoles_mem, hpoles_classify, _hpoles_complete,
      _hresidue, hoff_eq, hregular⟩
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

/-- A zeta zero in the square centered at `T - 1` with half-side `T` is in
the open square whenever `T > 1` is a good height.  The vertical sides are
`Re(s) = -1` and `Re(s) = 2T - 1`; the horizontal sides are excluded by
`goodHeight T`. -/
theorem zeta_zero_mem_openRectangle_one_shift_of_goodHeight
    {T : ℝ} (hT : 1 < T) (hgood : ExplicitFormulaAux.goodHeight T)
    {p : ℂ}
    (hpclosed : p ∈ MathlibAux.closedRectangle ((T - 1 : ℝ) : ℂ) T)
    (hpzero : riemannZeta p = 0) :
    p ∈ MathlibAux.openRectangle ((T - 1 : ℝ) : ℂ) T := by
  have hpclosed' := hpclosed
  simp [MathlibAux.closedRectangle, Complex.mem_reProdIm] at hpclosed'
  have hre_bounds := hpclosed'.1
  rw [Set.uIcc_of_le (by linarith : (-1 : ℝ) ≤ T - 1 + T)] at hre_bounds
  have him_bounds := hpclosed'.2
  rw [Set.uIcc_of_le (by linarith : -T ≤ T)] at him_bounds
  have hleft : -1 < p.re := by
    by_contra hnot
    have hre : p.re = -1 := by
      apply le_antisymm
      · linarith
      · exact hre_bounds.1
    have htrivial : ∀ n : ℕ, p ≠ -2 * ((n : ℂ) + 1) := by
      intro n hn
      have hnre := congrArg Complex.re hn
      simp at hnre
      have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    exact
      (PrimeNumberTheorem.riemannZeta_ne_zero_of_re_le_zero
        (by linarith : p.re ≤ 0) htrivial) hpzero
  have hright_of_one : p.re < 1 := by
    by_contra hnot
    exact (riemannZeta_ne_zero_of_one_le_re (le_of_not_gt hnot)) hpzero
  have hright : p.re < 2 * T - 1 := by
    linarith
  have habs_le : |p.im| ≤ T := by
    exact abs_le.mpr him_bounds
  have habs_ne : |p.im| ≠ T := by
    intro habs
    have him_ne : p.im ≠ 0 := by
      intro him
      rw [him, abs_zero] at habs
      linarith
    have htrivial : ∀ n : ℕ, p ≠ -2 * ((n : ℂ) + 1) := by
      intro n hn
      apply him_ne
      have hnim := congrArg Complex.im hn
      simpa using hnim
    have hre_pos : 0 < p.re := by
      by_contra hnot
      exact
        (PrimeNumberTheorem.riemannZeta_ne_zero_of_re_le_zero
          (le_of_not_gt hnot) htrivial) hpzero
    exact (hgood p ⟨hpzero, hre_pos, hright_of_one⟩) habs
  have habs_lt : |p.im| < T := lt_of_le_of_ne habs_le habs_ne
  have him := abs_lt.mp habs_lt
  have hright' : p.re < T - 1 + T := by linarith
  simpa [MathlibAux.openRectangle, Complex.mem_reProdIm] using
    And.intro ⟨hleft, hright'⟩ him

/-- Every good height `T > 1` gives a concrete square contour to which the
finite rectangle residue formula for the explicit-formula integrand applies. -/
theorem exists_rectangleBoundaryIntegral_explicitFormulaIntegrand_eq_residue_sum_of_goodHeight
    {x T : ℝ} (hx : 0 < x) (hT : 1 < T)
    (hgood : ExplicitFormulaAux.goodHeight T) :
    ∃ (poles : Finset ℂ) (residue : ℂ → ℂ),
      (∀ p ∈ poles,
        p ∈ MathlibAux.openRectangle ((T - 1 : ℝ) : ℂ) T) ∧
      MathlibAux.rectangleBoundaryIntegral (explicitFormulaIntegrand x)
          ((T - 1 : ℝ) : ℂ) T =
        (2 * Real.pi * I) * ∑ p ∈ poles, residue p := by
  apply exists_rectangleBoundaryIntegral_explicitFormulaIntegrand_eq_residue_sum
    hx (zero_lt_one.trans hT)
  · simp [MathlibAux.openRectangle, Complex.mem_reProdIm]
    constructor <;> linarith
  · intro p hpclosed hp
    rcases hp with rfl | hpzero
    · simp [MathlibAux.openRectangle, Complex.mem_reProdIm]
      constructor <;> linarith
    · exact zeta_zero_mem_openRectangle_one_shift_of_goodHeight
        hT hgood hpclosed hpzero

/-- There is a strictly increasing sequence of good heights above `1` tending
to infinity.  Each height therefore defines the pole-free square contour used
by the concrete rectangle residue theorem. -/
theorem exists_strictMono_goodHeight_gt_one_tendsto :
    ∃ T : ℕ → ℝ, StrictMono T ∧ Tendsto T atTop atTop ∧
      ∀ n, 1 < T n ∧ ExplicitFormulaAux.goodHeight (T n) := by
  rcases ExplicitFormulaAux.exists_strictMono_goodHeight_tendsto with
    ⟨T, hmono, htend, hgood⟩
  have hevent : ∀ᶠ n in atTop, (2 : ℝ) ≤ T n :=
    (tendsto_atTop.1 htend) 2
  rcases (eventually_atTop.1 hevent) with ⟨N, hN⟩
  let S : ℕ → ℝ := fun n => T (n + N)
  refine ⟨S, ?_, ?_, ?_⟩
  · intro a b hab
    exact hmono (Nat.add_lt_add_right hab N)
  · exact htend.comp (tendsto_add_atTop_nat N)
  · intro n
    refine ⟨lt_of_lt_of_le one_lt_two (hN (n + N) (Nat.le_add_left N n)), ?_⟩
    exact hgood (n + N)

/-- A cofinal sequence of concrete square contours satisfies the finite
rectangle residue formula for the explicit-formula integrand. -/
theorem exists_strictMono_tendsto_rectangleResidueContours
    {x : ℝ} (hx : 0 < x) :
    ∃ T : ℕ → ℝ, StrictMono T ∧ Tendsto T atTop atTop ∧
      ∀ n, 1 < T n ∧ ExplicitFormulaAux.goodHeight (T n) ∧
        ∃ (poles : Finset ℂ) (residue : ℂ → ℂ),
          (∀ p ∈ poles,
            p ∈ MathlibAux.openRectangle (((T n) - 1 : ℝ) : ℂ) (T n)) ∧
          MathlibAux.rectangleBoundaryIntegral (explicitFormulaIntegrand x)
              (((T n) - 1 : ℝ) : ℂ) (T n) =
            (2 * Real.pi * I) * ∑ p ∈ poles, residue p := by
  rcases exists_strictMono_goodHeight_gt_one_tendsto with
    ⟨T, hmono, htend, hT⟩
  refine ⟨T, hmono, htend, ?_⟩
  intro n
  refine ⟨(hT n).1, (hT n).2, ?_⟩
  exact
    exists_rectangleBoundaryIntegral_explicitFormulaIntegrand_eq_residue_sum_of_goodHeight
      hx (hT n).1 (hT n).2

end ExplicitFormulaResidues
end PrimeNumberTheorem
