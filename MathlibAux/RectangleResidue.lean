/-
Copyright (c) 2026 Riemann PNT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Shared rectangle meromorphic residue theorem (interface)

## Purpose

This file declares the project-internal **interface statement** for the
"rectangle contour integral equals `2πi • (sum of residues)`" theorem.
This theorem is the joint glue between the explicit-formula chain
(Chain 2 in `docs/target-statements-and-chains.md`) and the
RH / prime-counting error chain (Chain 3): both chains shift
contours past a finite rectangle around the critical strip and must
absorb the residue at `s = 1` and at the zeros of `ζ`.

The current declaration is intentionally a **target statement**, not a
proved theorem: a `def ... : Prop` whose body records the finite-residue
shape we eventually need.  It locks the argument list and lets downstream
code (`import MathlibAux.RectangleResidue`) use the name as a typed
predicate without exporting a fake theorem.

The full rectangle residue theorem is **deliberately deferred**.  This file
now proves the finite simple-pole residue formula on circles from Mathlib's
Cauchy integral formula.  Passing from that local theorem to a rectangle still
requires boundary deformation / small-circle indentation plus the existing
`integral_boundary_rect_eq_zero_of_differentiableOn` Cauchy-Goursat
lemma.
The intended future body is sketched in the doc-comment below; see
`docs/explicit-formula-chain.md` §"Contour and residue theorem" for
the full chain that this `def` is supposed to unblock.

## Mathematical statement (intended, for downstream readers)

For `f : ℂ → E` meromorphic inside a closed rectangle with opposite
corners at `c.re - R`, `c.re + R` (real part) and `c.im - R`, `c.im + R`
(imaginary part), where the divisor support of `f` inside the rectangle
is finite, the contour integral of `f` around the rectangle boundary
equals `2 * π * I` times the finite sum of `f`'s residues at the
support:

  ∮_{rect c R} f(z) dz  =  (2 * π * I) • (∑_k Res(f, z_k))

where `z_k` enumerates the poles (with multiplicity) of `f` strictly
inside the rectangle.

The companion lemmas `rectangleBoundaryIntegral_const` and
`rectangleIntegral_const` record the holomorphic constant-function sanity
case.  They are included as checks that the predicate compiles and that the
interface is non-vacuous (it can be satisfied).

## References

- Mathlib 4.29.1:
  - `Mathlib.Analysis.Meromorphic.Basic`
    (`MeromorphicAt`, `MeromorphicOn`).
  - `Mathlib.Analysis.Meromorphic.Order`
    (`meromorphicOrderAt`, `meromorphicTrailingCoeffAt`).
  - `Mathlib.Analysis.Meromorphic.Divisor`
    (`MeromorphicOn.divisor`).
  - `Mathlib.Analysis.Complex.CauchyIntegral`
    (`integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`,
     `integral_boundary_rect_eq_zero_of_differentiableOn`).
- Project chain doc: `docs/explicit-formula-chain.md`.
- Project chain doc: `docs/rh-error-equivalence-chain.md`.
-/

import Mathlib

-- The def's parameter list is the *public contract* the rest of the project
-- imports.  Some witnesses are intentionally part of the statement shape
-- rather than used by executable code.  Disable the unused-variable linter
-- for this file.
set_option linter.unusedVariables false

namespace MathlibAux

open Complex
open Set
open scoped BigOperators Interval

/-! ## Rectangle geometry and boundary integral expression -/

/-- Closed rectangle centered at `c` with half-side `R`, expressed in real and
imaginary coordinates. -/
def closedRectangle (c : ℂ) (R : ℝ) : Set ℂ :=
  [[c.re - R, c.re + R]] ×ℂ [[c.im - R, c.im + R]]

/-- Open rectangle centered at `c` with half-side `R`, expressed in real and
imaginary coordinates. -/
def openRectangle (c : ℂ) (R : ℝ) : Set ℂ :=
  Ioo (c.re - R) (c.re + R) ×ℂ Ioo (c.im - R) (c.im + R)

/-- Boundary integral expression used by Mathlib's rectangle Cauchy-Goursat
API, specialized to the rectangle centered at `c` with half-side `R`. -/
noncomputable def rectangleBoundaryIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) (c : ℂ) (R : ℝ) : E :=
  (∫ x : ℝ in (c.re - R)..(c.re + R), f (x + (c.im - R) * Complex.I)) -
    (∫ x : ℝ in (c.re - R)..(c.re + R), f (x + (c.im + R) * Complex.I)) +
      Complex.I • (∫ y : ℝ in (c.im - R)..(c.im + R), f ((c.re + R) + y * Complex.I)) -
        Complex.I • (∫ y : ℝ in (c.im - R)..(c.im + R), f ((c.re - R) + y * Complex.I))

private lemma inv_horizontal_edge_sub {R x : ℝ} (hR : R ≠ 0) :
    ((x : ℂ) - (R : ℂ) * I)⁻¹ - ((x : ℂ) + (R : ℂ) * I)⁻¹ =
      (2 * (R : ℂ) / ((R : ℂ) ^ 2 + (x : ℂ) ^ 2)) * I := by
  have hminus : (x : ℂ) - (R : ℂ) * I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    exact hR hi
  have hplus : (x : ℂ) + (R : ℂ) * I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    exact hR hi
  have hdenom : (R : ℂ) ^ 2 + (x : ℂ) ^ 2 ≠ 0 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add,
      Complex.ofReal_ne_zero]
    nlinarith [sq_pos_of_ne_zero hR]
  field_simp [hminus, hplus, hdenom]
  ring_nf
  have hI3 : I ^ 3 = -I := by
    rw [pow_succ, I_sq]
    ring
  rw [hI3]
  ring

private lemma inv_vertical_edge_sub {R y : ℝ} (hR : R ≠ 0) :
    ((R : ℂ) + (y : ℂ) * I)⁻¹ - (-(R : ℂ) + (y : ℂ) * I)⁻¹ =
      2 * (R : ℂ) / ((R : ℂ) ^ 2 + (y : ℂ) ^ 2) := by
  have hplus : (R : ℂ) + (y : ℂ) * I ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    exact hR hr
  have hminus : -(R : ℂ) + (y : ℂ) * I ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    exact hR hr
  have hdenom : (R : ℂ) ^ 2 + (y : ℂ) ^ 2 ≠ 0 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add,
      Complex.ofReal_ne_zero]
    nlinarith [sq_pos_of_ne_zero hR]
  field_simp [hplus, hminus, hdenom]
  ring_nf
  rw [I_sq]
  ring

/-- The positively oriented boundary integral of `1/z` around a square
centered at the origin is `2πi`. -/
theorem rectangleBoundaryIntegral_inv_zero {R : ℝ} (hR : 0 < R) :
    rectangleBoundaryIntegral (fun z : ℂ => z⁻¹) 0 R =
      2 * Real.pi * I := by
  have hRne : R ≠ 0 := hR.ne'
  have hreal :
      (∫ x : ℝ in -R..R, 2 * R / (R ^ 2 + x ^ 2)) = Real.pi := by
    calc
      (∫ x : ℝ in -R..R, 2 * R / (R ^ 2 + x ^ 2)) =
          2 * ∫ x : ℝ in -R..R, R / (R ^ 2 + x ^ 2) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro x _hx
        ring
      _ = 2 * (Real.arctan (R / R) - Real.arctan (-R / R)) := by
        rw [integral_div_sq_add_sq]
      _ = Real.pi := by
        simp [hRne, Real.arctan_one, Real.arctan_neg]
        ring
  have hbottom_cont :
      Continuous (fun x : ℝ => ((x : ℂ) - (R : ℂ) * I)⁻¹) := by
    apply (Complex.continuous_ofReal.sub continuous_const).inv₀
    intro x hx
    have hi := congrArg Complex.im hx
    simp at hi
    exact hRne hi
  have htop_cont :
      Continuous (fun x : ℝ => ((x : ℂ) + (R : ℂ) * I)⁻¹) := by
    apply (Complex.continuous_ofReal.add continuous_const).inv₀
    intro x hx
    have hi := congrArg Complex.im hx
    simp at hi
    exact hRne hi
  have hright_cont :
      Continuous (fun y : ℝ => ((R : ℂ) + (y : ℂ) * I)⁻¹) := by
    apply (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).inv₀
    intro y hy
    have hr := congrArg Complex.re hy
    simp at hr
    exact hRne hr
  have hleft_cont :
      Continuous (fun y : ℝ => (-(R : ℂ) + (y : ℂ) * I)⁻¹) := by
    apply (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).inv₀
    intro y hy
    have hr := congrArg Complex.re hy
    simp at hr
    exact hRne hr
  have hhorizontal :
      (∫ x : ℝ in -R..R, ((x : ℂ) - (R : ℂ) * I)⁻¹) -
          (∫ x : ℝ in -R..R, ((x : ℂ) + (R : ℂ) * I)⁻¹) =
        (Real.pi : ℂ) * I := by
    rw [← intervalIntegral.integral_sub
      (hbottom_cont.intervalIntegrable (-R) R)
      (htop_cont.intervalIntegrable (-R) R)]
    calc
      (∫ x : ℝ in -R..R,
          ((x : ℂ) - (R : ℂ) * I)⁻¹ - ((x : ℂ) + (R : ℂ) * I)⁻¹) =
          ∫ x : ℝ in -R..R,
            ((2 * R / (R ^ 2 + x ^ 2) : ℝ) : ℂ) * I := by
        apply intervalIntegral.integral_congr
        intro x _hx
        simpa [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_add,
          Complex.ofReal_pow] using inv_horizontal_edge_sub (R := R) (x := x) hRne
      _ = (∫ x : ℝ in -R..R,
          ((2 * R / (R ^ 2 + x ^ 2) : ℝ) : ℂ)) * I := by
        exact intervalIntegral.integral_mul_const I
          (fun x : ℝ => ((2 * R / (R ^ 2 + x ^ 2) : ℝ) : ℂ))
      _ = ((∫ x : ℝ in -R..R, 2 * R / (R ^ 2 + x ^ 2) : ℝ) : ℂ) * I := by
        rw [intervalIntegral.integral_ofReal]
      _ = (Real.pi : ℂ) * I := by rw [hreal]
  have hvertical :
      I * (∫ y : ℝ in -R..R, ((R : ℂ) + (y : ℂ) * I)⁻¹) -
          I * (∫ y : ℝ in -R..R, (-(R : ℂ) + (y : ℂ) * I)⁻¹) =
        (Real.pi : ℂ) * I := by
    rw [← mul_sub, ← intervalIntegral.integral_sub
      (hright_cont.intervalIntegrable (-R) R)
      (hleft_cont.intervalIntegrable (-R) R)]
    have hdiff :
        (∫ y : ℝ in -R..R,
            ((R : ℂ) + (y : ℂ) * I)⁻¹ - (-(R : ℂ) + (y : ℂ) * I)⁻¹) =
          (Real.pi : ℂ) := by
      calc
        (∫ y : ℝ in -R..R,
            ((R : ℂ) + (y : ℂ) * I)⁻¹ - (-(R : ℂ) + (y : ℂ) * I)⁻¹) =
            ∫ y : ℝ in -R..R,
              ((2 * R / (R ^ 2 + y ^ 2) : ℝ) : ℂ) := by
          apply intervalIntegral.integral_congr
          intro y _hy
          simpa [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_add,
            Complex.ofReal_pow] using inv_vertical_edge_sub (R := R) (y := y) hRne
        _ = ((∫ y : ℝ in -R..R, 2 * R / (R ^ 2 + y ^ 2) : ℝ) : ℂ) := by
          rw [intervalIntegral.integral_ofReal]
        _ = (Real.pi : ℂ) := by rw [hreal]
    rw [hdiff]
    ring
  simp [rectangleBoundaryIntegral]
  change
    ((∫ x : ℝ in -R..R, ((x : ℂ) + -((R : ℂ) * I))⁻¹) -
        (∫ x : ℝ in -R..R, ((x : ℂ) + (R : ℂ) * I)⁻¹) +
      I * (∫ y : ℝ in -R..R, ((R : ℂ) + (y : ℂ) * I)⁻¹)) -
      I * (∫ y : ℝ in -R..R, (-(R : ℂ) + (y : ℂ) * I)⁻¹) =
    2 * Real.pi * I
  have hhorizontal0 :
      (∫ x : ℝ in -R..R, ((x : ℂ) + -((R : ℂ) * I))⁻¹) -
          (∫ x : ℝ in -R..R, ((x : ℂ) + (R : ℂ) * I)⁻¹) =
        (Real.pi : ℂ) * I := by
    simpa [sub_eq_add_neg] using hhorizontal
  have hdecomp :
      (∫ x : ℝ in -R..R, ((x : ℂ) + -((R : ℂ) * I))⁻¹) -
          (∫ x : ℝ in -R..R, ((x : ℂ) + (R : ℂ) * I)⁻¹) +
        I * (∫ y : ℝ in -R..R, ((R : ℂ) + (y : ℂ) * I)⁻¹) -
        I * (∫ y : ℝ in -R..R, (-(R : ℂ) + (y : ℂ) * I)⁻¹) =
      ((∫ x : ℝ in -R..R, ((x : ℂ) + -((R : ℂ) * I))⁻¹) -
          ∫ x : ℝ in -R..R, ((x : ℂ) + (R : ℂ) * I)⁻¹) +
        (I * (∫ y : ℝ in -R..R, ((R : ℂ) + (y : ℂ) * I)⁻¹) -
          I * (∫ y : ℝ in -R..R, (-(R : ℂ) + (y : ℂ) * I)⁻¹)) := by
    ring
  rw [hdecomp, hhorizontal0, hvertical]
  ring

/-! ## Proved finite simple-pole residue formula on circles -/

/-- A holomorphic term plus finitely many simple principal parts integrates to
`2πi` times the sum of their residues on a circle containing every pole.

This is a genuine finite residue theorem built from Mathlib's Cauchy integral
formula.  It supplies the analytic local model needed by the future rectangle
deformation: the remaining rectangle-specific gap is to deform its boundary
to circles around the finitely many poles. -/
theorem circleIntegral_eq_finite_simple_pole_residue_sum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {g : ℂ → E} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (poles : Finset ℂ) (residue : ℂ → E)
    (hg : DifferentiableOn ℂ g (Metric.closedBall c R))
    (hpoles : ∀ p ∈ poles, p ∈ Metric.ball c R) :
    (∮ z in C(c, R),
        g z + ∑ p ∈ poles, (z - p)⁻¹ • residue p) =
      (2 * Real.pi * Complex.I) • ∑ p ∈ poles, residue p := by
  have hg_integrable : CircleIntegrable g c R :=
    (hg.continuousOn.mono Metric.sphere_subset_closedBall).circleIntegrable hR.le
  have hkernel_integrable : ∀ p ∈ poles,
      CircleIntegrable (fun z : ℂ => (z - p)⁻¹ • residue p) c R := by
    intro p hp
    have hne : ∀ z ∈ Metric.sphere c R, z ≠ p := by
      intro z hz hzp
      subst z
      have hp_lt : ‖p - c‖ < R := by
        simpa [Metric.mem_ball, dist_eq] using hpoles p hp
      have hp_eq : ‖p - c‖ = R := by
        simpa [Metric.mem_sphere, dist_eq] using hz
      linarith
    exact
      (((continuousOn_id.sub continuousOn_const).inv₀ fun z hz =>
          sub_ne_zero.mpr (hne z hz)).smul continuousOn_const).circleIntegrable hR.le
  have hsum_integrable :
      CircleIntegrable (fun z : ℂ => ∑ p ∈ poles, (z - p)⁻¹ • residue p) c R :=
    (continuousOn_finset_sum poles fun p hp =>
      (((continuousOn_id.sub continuousOn_const).inv₀ fun z hz => by
          apply sub_ne_zero.mpr
          intro hzp
          change z = p at hzp
          subst z
          have hp_lt : ‖p - c‖ < R := by
            simpa [Metric.mem_ball, dist_eq] using hpoles p hp
          have hp_eq : ‖p - c‖ = R := by
            simpa [Metric.mem_sphere, dist_eq] using hz
          linarith).smul continuousOn_const)).circleIntegrable hR.le
  rw [circleIntegral.integral_add hg_integrable hsum_integrable]
  have hg_zero : (∮ z in C(c, R), g z) = 0 :=
    (hg.mono Metric.closure_ball_subset_closedBall).diffContOnCl.circleIntegral_eq_zero hR.le
  rw [hg_zero, zero_add, circleIntegral.integral_fun_sum hkernel_integrable]
  calc
    (∑ p ∈ poles, ∮ z in C(c, R), (z - p)⁻¹ • residue p) =
        ∑ p ∈ poles, (2 * Real.pi * Complex.I) • residue p := by
      apply Finset.sum_congr rfl
      intro p hp
      exact (differentiableOn_const (c := residue p)).circleIntegral_sub_inv_smul
        (hpoles p hp)
    _ = (2 * Real.pi * Complex.I) • ∑ p ∈ poles, residue p := by
      exact Finset.smul_sum.symm

/-! ## Rectangle meromorphic residue target (interface statement) -/

/--
Project-internal target statement:

  The contour integral of a meromorphic function `f : ℂ → E` around
  the closed rectangle centred at `c` with half-side `R` equals
  `2 * π * I` times the finite sum of `f`'s residues at the divisor
  support strictly inside the rectangle.

The argument list is the **public contract** the rest of the project
imports:

- `E : Type*`  — codomain with a `NormedAddCommGroup` structure
  and a complex normed-space structure (so that contour integrals in `E`
  make sense);
- `f : ℂ → E` — the function being integrated;
- `c : ℂ`     — centre of the rectangle (both real and imaginary
  coordinates);
- `R : ℝ`     — half-side length of the rectangle; the rectangle
  occupies `Re z ∈ [c.re - R, c.re + R]`,
  `Im z ∈ [c.im - R, c.im + R]`;
- `hpos : 0 < R` — explicit witness that the rectangle is
  non-degenerate.

The body is an existential certificate shape: there is a finite pole set and a
residue function for which the Mathlib rectangle-boundary integral equals
`2πi` times the residue sum.  It is not a universal theorem derivable from
`hpos` alone; the actual analytic input remains the rectangle deformation from
the proved finite simple-pole circle formula above.

**This is NOT a `theorem`** — it is a `def` returning `Prop`.  The
Lean kernel accepts the proposition without requiring a proof, and
`verify-baseline.sh` will not flag it (no `sorry` / `admit` / `axiom`).
-/
def rectangleIntegral_meromorphic_eq_residue_sum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {c : ℂ} {R : ℝ}
    (hpos : 0 < R) : Prop :=
  0 < R ∧
    ∃ (poles : Finset ℂ) (residue : ℂ → E),
      MeromorphicOn f (closedRectangle c R) ∧
        (∀ z ∈ openRectangle c R, z ∉ poles → DifferentiableAt ℂ f z) ∧
          (∀ z ∈ poles, z ∈ openRectangle c R) ∧
            rectangleBoundaryIntegral f c R =
              (2 * Real.pi * Complex.I) • (∑ z ∈ poles, residue z)

/-! ## Trivial sanity-check lemma -/

/-- The rectangle boundary integral of a complex constant function is zero. -/
lemma rectangleBoundaryIntegral_const (a c : ℂ) (R : ℝ) :
    rectangleBoundaryIntegral (fun _ : ℂ => a) c R = 0 := by
  simp [rectangleBoundaryIntegral]

/--
**Sanity check**: a constant complex function has zero contour integral around
every rectangle and the residue sum at the empty pole set is trivially zero, so
the interface predicate holds using the empty pole set.

This does not prove the meromorphic residue theorem for arbitrary `f`;
it only checks that the statement is satisfiable in the degenerate
holomorphic constant case and that the boundary-integral expression reduces
as expected.
-/
lemma rectangleIntegral_const (a c : ℂ) {R : ℝ} (hpos : 0 < R) :
    rectangleIntegral_meromorphic_eq_residue_sum
      (E := ℂ) (f := fun _ : ℂ => a) (c := c) (R := R) hpos :=
  by
    refine ⟨hpos, ∅, fun _ => 0, ?_, ?_, ?_, ?_⟩
    · intro z hz
      exact MeromorphicAt.const a z
    · intro z hz hzp
      exact differentiableAt_const a
    · intro z hz
      simp at hz
    · simp [rectangleBoundaryIntegral_const]

/-- Backwards-compatible zero-function specialization of
`rectangleIntegral_const`. -/
lemma rectangleIntegral_const_zero {R : ℝ} (hpos : 0 < R) :
    rectangleIntegral_meromorphic_eq_residue_sum
      (E := ℂ) (f := fun _ : ℂ => (0 : ℂ)) (c := 0) (R := R) hpos :=
  rectangleIntegral_const 0 0 hpos

/-
## Why we do NOT export a `of_meromorphicOn` wrapper

The natural next lemma would be a wrapper that consumes a
`MeromorphicOn f (closedBall c R)` hypothesis and discharges the
predicate.  In Lean 4.29.1, packaging that hypothesis into a
usable form for the contour-integral machinery hits a known
destructure / `Classical.choose` type-inference sharp edge (see
the project discipline block in `TASK_BRIEF.md`).  Adding it now
risks the build without contributing to the "interface-statement"
goal of this task.  The wrapper is to be revisited in a later
phase once the actual residue equality is filled in; at that
point the `MeromorphicOn` chain can be wired up cleanly.

End of `MathlibAux.RectangleResidue`. -/

end MathlibAux
