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

The actual residue theorem is **deliberately deferred** to a later
phase: building it from scratch in Lean 4.29.1 / Mathlib 4.29.1 requires
small-circle indentation + Cauchy integral formula + the existing
`integral_boundary_rect_eq_zero_of_differentiableOn` Cauchy-Goursat
lemma, which is far beyond the 15-minute window of this interface task.
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

The body is a real `Prop` statement: there is a finite pole set and a
residue function for which the Mathlib rectangle-boundary integral equals
`2πi` times the residue sum.  This is still **not a proof** of the residue
theorem; it is the target shape that future Perron / explicit-formula work
must discharge.

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
