import Mathlib.Analysis.Complex.RemovableSingularity
import MathlibAux.BoundaryRectResidue

open Complex Set
open scoped BigOperators Interval

namespace MathlibAux

/--
Multiplying a finite simple-pole decomposition by an entire weight evaluates
that weight at each pole in the rectangle residue sum.

The divided slope absorbs the analytic difference
`W z - W p`, so the statement does not assume a residue theorem beyond the
already proved finite-principal-part rectangle formula.
-/
theorem rectangleBoundaryIntegral_mul_analyticWeight_eq_residue_sum
    {g W : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (poles : Finset ℂ) (residue : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g (closedRectangle c R))
    (hW : Differentiable ℂ W)
    (hpoles : ∀ p ∈ poles, p ∈ openRectangle c R) :
    rectangleBoundaryIntegral
        (fun z : ℂ =>
          W z * (g z + ∑ p ∈ poles, (z - p)⁻¹ * residue p))
        c R =
      (2 * Real.pi * I) *
        ∑ p ∈ poles, W p * residue p := by
  classical
  let G : ℂ → ℂ := fun z =>
    W z * g z + ∑ p ∈ poles, dslope W p z * residue p
  have hdslope (p : ℂ) : Differentiable ℂ (dslope W p) := by
    rw [← differentiableOn_univ]
    exact
      (Complex.differentiableOn_dslope
        (isOpen_univ.mem_nhds (Set.mem_univ p))).2 hW.differentiableOn
  have hG : DifferentiableOn ℂ G (closedRectangle c R) := by
    intro z hz
    dsimp [G]
    refine
      ((hW z).differentiableWithinAt.mul (hg z hz)).add
        (DifferentiableWithinAt.fun_sum (u := poles) fun p _ =>
          (hdslope p z).differentiableWithinAt.mul_const (residue p))
  have hboundary :
      ∀ z ∈ closedRectangle c R, z ∉ openRectangle c R →
        W z * (g z + ∑ p ∈ poles, (z - p)⁻¹ * residue p) =
          G z + ∑ p ∈ poles,
            (z - p)⁻¹ * (W p * residue p) := by
    intro z hzclosed hzboundary
    have hzp : ∀ p ∈ poles, z ≠ p := by
      intro p hp h
      subst z
      exact hzboundary (hpoles p hp)
    dsimp [G]
    rw [mul_add, Finset.mul_sum]
    calc
      W z * g z + ∑ p ∈ poles, W z * ((z - p)⁻¹ * residue p) =
          W z * g z + ∑ p ∈ poles,
            (dslope W p z * residue p +
              (z - p)⁻¹ * (W p * residue p)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro p hp
        rw [dslope_of_ne W (hzp p hp)]
        simp only [slope, vsub_eq_sub, smul_eq_mul]
        field_simp [sub_ne_zero.mpr (hzp p hp)]
        ring
      _ = W z * g z + ∑ p ∈ poles, dslope W p z * residue p +
          ∑ p ∈ poles, (z - p)⁻¹ * (W p * residue p) := by
        rw [Finset.sum_add_distrib]
        ring
  calc
    rectangleBoundaryIntegral
        (fun z : ℂ =>
          W z * (g z + ∑ p ∈ poles, (z - p)⁻¹ * residue p))
        c R =
      rectangleBoundaryIntegral
        (fun z : ℂ =>
          G z + ∑ p ∈ poles,
            (z - p)⁻¹ * (W p * residue p))
        c R :=
      rectangleBoundaryIntegral_congr_of_eqOn_boundary hR hboundary
    _ = (2 * Real.pi * I) *
        ∑ p ∈ poles, W p * residue p :=
      rectangleBoundaryIntegral_eq_finite_simple_pole_residue_sum_of_differentiableOn
        hR poles (fun p => W p * residue p) hG hpoles

/--
Axis-parallel version of
`rectangleBoundaryIntegral_mul_analyticWeight_eq_residue_sum`.

Keeping the two vertical sides fixed is essential for Gaussian contour
weights: it avoids an exponentially growing right edge when the height tends
to infinity.
-/
theorem boundaryRectIntegral_mul_analyticWeight_eq_residue_sum
    {g W : ℂ → ℂ} {x0 x1 y0 y1 : ℝ}
    (poles : Finset ℂ) (residue : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g
      ([[x0, x1]] ×ℂ [[y0, y1]]))
    (hW : Differentiable ℂ W)
    (hpoles : ∀ p ∈ poles,
      x0 < p.re ∧ p.re < x1 ∧ y0 < p.im ∧ p.im < y1) :
    boundaryRectIntegral
        (fun z : ℂ =>
          W z * (g z + ∑ p ∈ poles, (z - p)⁻¹ * residue p))
        x0 x1 y0 y1 =
      (2 * Real.pi * I) *
        ∑ p ∈ poles, W p * residue p := by
  classical
  let G : ℂ → ℂ := fun z =>
    W z * g z + ∑ p ∈ poles, dslope W p z * residue p
  have hdslope (p : ℂ) : Differentiable ℂ (dslope W p) := by
    rw [← differentiableOn_univ]
    exact
      (Complex.differentiableOn_dslope
        (isOpen_univ.mem_nhds (Set.mem_univ p))).2 hW.differentiableOn
  have hG : DifferentiableOn ℂ G
      ([[x0, x1]] ×ℂ [[y0, y1]]) := by
    intro z hz
    dsimp [G]
    refine
      ((hW z).differentiableWithinAt.mul (hg z hz)).add
        (DifferentiableWithinAt.fun_sum (u := poles) fun p _ =>
          (hdslope p z).differentiableWithinAt.mul_const (residue p))
  have hboundary :
      ∀ z ∈ ([[x0, x1]] ×ℂ [[y0, y1]] : Set ℂ),
        ¬(x0 < z.re ∧ z.re < x1 ∧ y0 < z.im ∧ z.im < y1) →
        W z * (g z + ∑ p ∈ poles, (z - p)⁻¹ * residue p) =
          G z + ∑ p ∈ poles,
            (z - p)⁻¹ * (W p * residue p) := by
    intro z hzclosed hzboundary
    have hzp : ∀ p ∈ poles, z ≠ p := by
      intro p hp h
      subst z
      exact hzboundary (hpoles p hp)
    dsimp [G]
    rw [mul_add, Finset.mul_sum]
    calc
      W z * g z + ∑ p ∈ poles, W z * ((z - p)⁻¹ * residue p) =
          W z * g z + ∑ p ∈ poles,
            (dslope W p z * residue p +
              (z - p)⁻¹ * (W p * residue p)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro p hp
        rw [dslope_of_ne W (hzp p hp)]
        simp only [slope, vsub_eq_sub, smul_eq_mul]
        field_simp [sub_ne_zero.mpr (hzp p hp)]
        ring
      _ = W z * g z + ∑ p ∈ poles, dslope W p z * residue p +
          ∑ p ∈ poles, (z - p)⁻¹ * (W p * residue p) := by
        rw [Finset.sum_add_distrib]
        ring
  calc
    boundaryRectIntegral
        (fun z : ℂ =>
          W z * (g z + ∑ p ∈ poles, (z - p)⁻¹ * residue p))
        x0 x1 y0 y1 =
      boundaryRectIntegral
        (fun z : ℂ =>
          G z + ∑ p ∈ poles,
            (z - p)⁻¹ * (W p * residue p))
        x0 x1 y0 y1 :=
      boundaryRectIntegral_congr_of_eqOn_boundary hboundary
    _ = (2 * Real.pi * I) *
        ∑ p ∈ poles, W p * residue p :=
      boundaryRectIntegral_eq_finite_simple_pole_residue_sum_of_differentiableOn
        poles (fun p => W p * residue p) hG hpoles

end MathlibAux
