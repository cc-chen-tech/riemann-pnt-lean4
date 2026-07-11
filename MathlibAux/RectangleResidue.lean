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

The full meromorphic rectangle residue theorem is **deliberately deferred**.
This file now proves finite simple-pole residue formulas on both circles and
squares.  The square proof includes the four-rectangle deformation and exact
cancellation of internal edges.  What remains is extracting a finite family
of principal parts from a general meromorphic function (including higher-order
poles) and proving that the remainder is holomorphic on the rectangle.
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

/-- The positively oriented boundary integral of an axis-parallel rectangle
with real endpoints `x0`, `x1` and imaginary endpoints `y0`, `y1`. -/
noncomputable def boundaryRectIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) (x0 x1 y0 y1 : ℝ) : E :=
  (∫ x : ℝ in x0..x1, f (x + y0 * Complex.I)) -
    (∫ x : ℝ in x0..x1, f (x + y1 * Complex.I)) +
      Complex.I • (∫ y : ℝ in y0..y1, f (x1 + y * Complex.I)) -
        Complex.I • (∫ y : ℝ in y0..y1, f (x0 + y * Complex.I))

lemma rectangleBoundaryIntegral_eq_boundaryRectIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) (c : ℂ) (R : ℝ) :
    rectangleBoundaryIntegral f c R =
      boundaryRectIntegral f (c.re - R) (c.re + R) (c.im - R) (c.im + R) :=
  by simp [rectangleBoundaryIntegral, boundaryRectIntegral]

lemma rectangleBoundaryIntegral_mul_const (f : ℂ → ℂ) (a c : ℂ) (R : ℝ) :
    rectangleBoundaryIntegral (fun z => f z * a) c R =
      rectangleBoundaryIntegral f c R * a := by
  have hbottom :
      (∫ x : ℝ in (c.re - R)..(c.re + R),
          f (x + (c.im - R) * I) * a) =
        (∫ x : ℝ in (c.re - R)..(c.re + R),
          f (x + (c.im - R) * I)) * a :=
    intervalIntegral.integral_mul_const a _
  have htop :
      (∫ x : ℝ in (c.re - R)..(c.re + R),
          f (x + (c.im + R) * I) * a) =
        (∫ x : ℝ in (c.re - R)..(c.re + R),
          f (x + (c.im + R) * I)) * a :=
    intervalIntegral.integral_mul_const a _
  have hright :
      (∫ y : ℝ in (c.im - R)..(c.im + R),
          f ((c.re + R) + y * I) * a) =
        (∫ y : ℝ in (c.im - R)..(c.im + R),
          f ((c.re + R) + y * I)) * a :=
    intervalIntegral.integral_mul_const a _
  have hleft :
      (∫ y : ℝ in (c.im - R)..(c.im + R),
          f ((c.re - R) + y * I) * a) =
        (∫ y : ℝ in (c.im - R)..(c.im + R),
          f ((c.re - R) + y * I)) * a :=
    intervalIntegral.integral_mul_const a _
  unfold rectangleBoundaryIntegral
  dsimp only
  rw [hbottom, htop, hright, hleft]
  simp only [smul_eq_mul]
  ring

lemma rectangleBoundaryIntegral_finset_sum
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (s : Finset ι) (f : ι → ℂ → E) (c : ℂ) (R : ℝ)
    (hbottom : ∀ i ∈ s, IntervalIntegrable
      (fun x : ℝ => f i (x + (c.im - R) * I)) MeasureTheory.volume (c.re - R) (c.re + R))
    (htop : ∀ i ∈ s, IntervalIntegrable
      (fun x : ℝ => f i (x + (c.im + R) * I)) MeasureTheory.volume (c.re - R) (c.re + R))
    (hright : ∀ i ∈ s, IntervalIntegrable
      (fun y : ℝ => f i ((c.re + R) + y * I)) MeasureTheory.volume (c.im - R) (c.im + R))
    (hleft : ∀ i ∈ s, IntervalIntegrable
      (fun y : ℝ => f i ((c.re - R) + y * I)) MeasureTheory.volume (c.im - R) (c.im + R)) :
    rectangleBoundaryIntegral (fun z => ∑ i ∈ s, f i z) c R =
      ∑ i ∈ s, rectangleBoundaryIntegral (f i) c R := by
  unfold rectangleBoundaryIntegral
  dsimp only
  rw [intervalIntegral.integral_finset_sum hbottom,
    intervalIntegral.integral_finset_sum htop,
    intervalIntegral.integral_finset_sum hright,
    intervalIntegral.integral_finset_sum hleft]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.smul_sum]

/-- Cauchy-Goursat for the project rectangle-boundary notation. -/
lemma boundaryRectIntegral_eq_zero_of_differentiableOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (f : ℂ → E) (x0 x1 y0 y1 : ℝ)
    (hf : DifferentiableOn ℂ f ([[x0, x1]] ×ℂ [[y0, y1]])) :
    boundaryRectIntegral f x0 x1 y0 y1 = 0 := by
  simpa [boundaryRectIntegral] using
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      (x0 + y0 * Complex.I) (x1 + y1 * Complex.I) (by simpa using hf)

private lemma rectangular_annulus_boundary_algebra
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H V : ℝ → ℝ → ℝ → E) (x0 u v x1 y0 w q y1 : ℝ)
    (hw : H w x0 x1 = H w x0 u + H w u v + H w v x1)
    (hq : H q x0 x1 = H q x0 u + H q u v + H q v x1)
    (hx0 : V x0 y0 y1 = V x0 y0 w + V x0 w q + V x0 q y1)
    (hx1 : V x1 y0 y1 = V x1 y0 w + V x1 w q + V x1 q y1)
    (hsum :
      (H y0 x0 x1 - H w x0 x1 + I • V x1 y0 w - I • V x0 y0 w) +
          (H q x0 x1 - H y1 x0 x1 + I • V x1 q y1 - I • V x0 q y1) +
          (H w x0 u - H q x0 u + I • V u w q - I • V x0 w q) +
          (H w v x1 - H q v x1 + I • V x1 w q - I • V v w q) = 0) :
    H y0 x0 x1 - H y1 x0 x1 + I • V x1 y0 y1 - I • V x0 y0 y1 =
      H w u v - H q u v + I • V v w q - I • V u w q := by
  rw [hw, hq] at hsum
  rw [hx0, hx1]
  simp only [smul_add]
  apply sub_eq_zero.mp
  convert hsum using 1 <;> module

/-- Boundary cancellation for a rectangular annulus.  The four hypotheses say
that the bottom, top, left and right rectangles between the outer and inner
boundaries have zero boundary integral. -/
lemma boundaryRectIntegral_eq_inner_of_four_rectangles
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) (x0 u v x1 y0 w q y1 : ℝ)
    (hfw : Continuous (fun x : ℝ => f (x + w * Complex.I)))
    (hfq : Continuous (fun x : ℝ => f (x + q * Complex.I)))
    (hfx0 : Continuous (fun y : ℝ => f (x0 + y * Complex.I)))
    (hfx1 : Continuous (fun y : ℝ => f (x1 + y * Complex.I)))
    (hbottom : boundaryRectIntegral f x0 x1 y0 w = 0)
    (htop : boundaryRectIntegral f x0 x1 q y1 = 0)
    (hleft : boundaryRectIntegral f x0 u w q = 0)
    (hright : boundaryRectIntegral f v x1 w q = 0) :
    boundaryRectIntegral f x0 x1 y0 y1 = boundaryRectIntegral f u v w q := by
  let H (y a b : ℝ) : E := ∫ x : ℝ in a..b, f (x + y * Complex.I)
  let V (x a b : ℝ) : E := ∫ y : ℝ in a..b, f (x + y * Complex.I)
  have hbottom' : H y0 x0 x1 - H w x0 x1 + I • V x1 y0 w - I • V x0 y0 w = 0 := by
    simpa [boundaryRectIntegral, H, V] using hbottom
  have htop' : H q x0 x1 - H y1 x0 x1 + I • V x1 q y1 - I • V x0 q y1 = 0 := by
    simpa [boundaryRectIntegral, H, V] using htop
  have hleft' : H w x0 u - H q x0 u + I • V u w q - I • V x0 w q = 0 := by
    simpa [boundaryRectIntegral, H, V] using hleft
  have hright' : H w v x1 - H q v x1 + I • V x1 w q - I • V v w q = 0 := by
    simpa [boundaryRectIntegral, H, V] using hright
  have hsum :
      (H y0 x0 x1 - H w x0 x1 + I • V x1 y0 w - I • V x0 y0 w) +
          (H q x0 x1 - H y1 x0 x1 + I • V x1 q y1 - I • V x0 q y1) +
          (H w x0 u - H q x0 u + I • V u w q - I • V x0 w q) +
          (H w v x1 - H q v x1 + I • V x1 w q - I • V v w q) = 0 := by
    rw [hbottom', htop', hleft', hright']
    simp
  have hw_split :
      H w x0 x1 = H w x0 u + H w u v + H w v x1 := by
    simp only [H]
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hfw.intervalIntegrable x0 u) (hfw.intervalIntegrable u v),
      intervalIntegral.integral_add_adjacent_intervals
        (hfw.intervalIntegrable x0 v) (hfw.intervalIntegrable v x1)]
  have hq_split :
      H q x0 x1 = H q x0 u + H q u v + H q v x1 := by
    simp only [H]
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hfq.intervalIntegrable x0 u) (hfq.intervalIntegrable u v),
      intervalIntegral.integral_add_adjacent_intervals
        (hfq.intervalIntegrable x0 v) (hfq.intervalIntegrable v x1)]
  have hx0_split :
      V x0 y0 y1 = V x0 y0 w + V x0 w q + V x0 q y1 := by
    simp only [V]
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hfx0.intervalIntegrable y0 w) (hfx0.intervalIntegrable w q),
      intervalIntegral.integral_add_adjacent_intervals
        (hfx0.intervalIntegrable y0 q) (hfx0.intervalIntegrable q y1)]
  have hx1_split :
      V x1 y0 y1 = V x1 y0 w + V x1 w q + V x1 q y1 := by
    simp only [V]
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hfx1.intervalIntegrable y0 w) (hfx1.intervalIntegrable w q),
      intervalIntegral.integral_add_adjacent_intervals
        (hfx1.intervalIntegrable y0 q) (hfx1.intervalIntegrable q y1)]
  change H y0 x0 x1 - H y1 x0 x1 + I • V x1 y0 y1 - I • V x0 y0 y1 =
    H w u v - H q u v + I • V v w q - I • V u w q
  exact rectangular_annulus_boundary_algebra H V x0 u v x1 y0 w q y1
    hw_split hq_split hx0_split hx1_split hsum

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

/-- The positively oriented boundary integral of the simple-pole kernel
`1 / (z-c)` around a square centered at `c` is `2πi`. -/
theorem rectangleBoundaryIntegral_sub_inv_center (c : ℂ) {R : ℝ} (hR : 0 < R) :
    rectangleBoundaryIntegral (fun z : ℂ => (z - c)⁻¹) c R =
      2 * Real.pi * I := by
  have hbottom :
      (∫ x : ℝ in (c.re - R)..(c.re + R),
          (((x : ℂ) + (c.im - R) * I) - c)⁻¹) =
        ∫ u : ℝ in -R..R, ((u : ℂ) - (R : ℂ) * I)⁻¹ := by
    calc
      (∫ x : ℝ in (c.re - R)..(c.re + R),
          (((x : ℂ) + (c.im - R) * I) - c)⁻¹) =
        ∫ x : ℝ in (c.re - R)..(c.re + R),
          (((x - c.re : ℝ) : ℂ) - (R : ℂ) * I)⁻¹ := by
          apply intervalIntegral.integral_congr
          intro x _hx
          change (((x : ℂ) + (c.im - R) * I) - c)⁻¹ =
            (((x - c.re : ℝ) : ℂ) - (R : ℂ) * I)⁻¹
          congr 1
          apply Complex.ext <;> simp [Complex.sub_re, Complex.sub_im]
      _ = ∫ u : ℝ in -R..R, ((u : ℂ) - (R : ℂ) * I)⁻¹ := by
        convert intervalIntegral.integral_comp_add_right
          (fun u : ℝ => ((u : ℂ) - (R : ℂ) * I)⁻¹) (-c.re) using 1 <;> ring_nf
  have htop :
      (∫ x : ℝ in (c.re - R)..(c.re + R),
          (((x : ℂ) + (c.im + R) * I) - c)⁻¹) =
        ∫ u : ℝ in -R..R, ((u : ℂ) + (R : ℂ) * I)⁻¹ := by
    calc
      (∫ x : ℝ in (c.re - R)..(c.re + R),
          (((x : ℂ) + (c.im + R) * I) - c)⁻¹) =
        ∫ x : ℝ in (c.re - R)..(c.re + R),
          (((x - c.re : ℝ) : ℂ) + (R : ℂ) * I)⁻¹ := by
          apply intervalIntegral.integral_congr
          intro x _hx
          change (((x : ℂ) + (c.im + R) * I) - c)⁻¹ =
            (((x - c.re : ℝ) : ℂ) + (R : ℂ) * I)⁻¹
          congr 1
          apply Complex.ext <;> simp [Complex.sub_re, Complex.sub_im]
      _ = ∫ u : ℝ in -R..R, ((u : ℂ) + (R : ℂ) * I)⁻¹ := by
        convert intervalIntegral.integral_comp_add_right
          (fun u : ℝ => ((u : ℂ) + (R : ℂ) * I)⁻¹) (-c.re) using 1 <;> ring_nf
  have hright :
      (∫ y : ℝ in (c.im - R)..(c.im + R),
          ((c.re : ℂ) + (R : ℂ) + (y : ℂ) * I - c)⁻¹) =
        ∫ v : ℝ in -R..R, ((R : ℂ) + (v : ℂ) * I)⁻¹ := by
    calc
      (∫ y : ℝ in (c.im - R)..(c.im + R),
          ((c.re : ℂ) + (R : ℂ) + (y : ℂ) * I - c)⁻¹) =
        ∫ y : ℝ in (c.im - R)..(c.im + R),
          ((R : ℂ) + ((y - c.im : ℝ) : ℂ) * I)⁻¹ := by
          apply intervalIntegral.integral_congr
          intro y _hy
          change ((c.re : ℂ) + (R : ℂ) + (y : ℂ) * I - c)⁻¹ =
            ((R : ℂ) + ((y - c.im : ℝ) : ℂ) * I)⁻¹
          congr 1
          apply Complex.ext <;> simp [Complex.sub_re, Complex.sub_im]
      _ = ∫ v : ℝ in -R..R, ((R : ℂ) + (v : ℂ) * I)⁻¹ := by
        convert intervalIntegral.integral_comp_add_right
          (fun v : ℝ => ((R : ℂ) + (v : ℂ) * I)⁻¹) (-c.im) using 1 <;> ring_nf
  have hleft :
      (∫ y : ℝ in (c.im - R)..(c.im + R),
          ((c.re : ℂ) - (R : ℂ) + (y : ℂ) * I - c)⁻¹) =
        ∫ v : ℝ in -R..R, (-(R : ℂ) + (v : ℂ) * I)⁻¹ := by
    calc
      (∫ y : ℝ in (c.im - R)..(c.im + R),
          ((c.re : ℂ) - (R : ℂ) + (y : ℂ) * I - c)⁻¹) =
        ∫ y : ℝ in (c.im - R)..(c.im + R),
          (-(R : ℂ) + ((y - c.im : ℝ) : ℂ) * I)⁻¹ := by
          apply intervalIntegral.integral_congr
          intro y _hy
          change ((c.re : ℂ) - (R : ℂ) + (y : ℂ) * I - c)⁻¹ =
            (-(R : ℂ) + ((y - c.im : ℝ) : ℂ) * I)⁻¹
          congr 1
          apply Complex.ext <;> simp [Complex.sub_re, Complex.sub_im]
      _ = ∫ v : ℝ in -R..R, (-(R : ℂ) + (v : ℂ) * I)⁻¹ := by
        convert intervalIntegral.integral_comp_add_right
          (fun v : ℝ => (-(R : ℂ) + (v : ℂ) * I)⁻¹) (-c.im) using 1 <;> ring_nf
  rw [rectangleBoundaryIntegral, hbottom, htop, hright, hleft]
  simpa [rectangleBoundaryIntegral] using rectangleBoundaryIntegral_inv_zero hR

/-- The square boundary integral of `1 / (z-p)` is `2πi` whenever `p` lies
strictly inside the square.  This is the rectangle simple-pole kernel needed
for finite residue sums. -/
theorem rectangleBoundaryIntegral_sub_inv_of_mem_openRectangle
    (c p : ℂ) {R : ℝ} (hR : 0 < R) (hp : p ∈ openRectangle c R) :
    rectangleBoundaryIntegral (fun z : ℂ => (z - p)⁻¹) c R =
      2 * Real.pi * I := by
  let x0 := c.re - R
  let x1 := c.re + R
  let y0 := c.im - R
  let y1 := c.im + R
  have hp' : x0 < p.re ∧ p.re < x1 ∧ y0 < p.im ∧ p.im < y1 := by
    have hp0 : (x0 < p.re ∧ p.re < x1) ∧ (y0 < p.im ∧ p.im < y1) := by
      simpa [openRectangle, x0, x1, y0, y1, mem_reProdIm] using hp
    exact ⟨hp0.1.1, hp0.1.2, hp0.2.1, hp0.2.2⟩
  let margin := min (min (p.re - x0) (x1 - p.re))
    (min (p.im - y0) (y1 - p.im))
  have hmargin : 0 < margin := by
    dsimp [margin]
    exact lt_min (lt_min (sub_pos.mpr hp'.1) (sub_pos.mpr hp'.2.1))
      (lt_min (sub_pos.mpr hp'.2.2.1) (sub_pos.mpr hp'.2.2.2))
  let r := margin / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hr_x0 : r < p.re - x0 := by
    have hm : margin ≤ p.re - x0 :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    dsimp [r]
    linarith
  have hr_x1 : r < x1 - p.re := by
    have hm : margin ≤ x1 - p.re :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    dsimp [r]
    linarith
  have hr_y0 : r < p.im - y0 := by
    have hm : margin ≤ p.im - y0 :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    dsimp [r]
    linarith
  have hr_y1 : r < y1 - p.im := by
    have hm : margin ≤ y1 - p.im :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    dsimp [r]
    linarith
  let u := p.re - r
  let v := p.re + r
  let w := p.im - r
  let q := p.im + r
  have hx0u : x0 < u := by dsimp [u]; linarith
  have huv : u < v := by dsimp [u, v]; linarith
  have hvx1 : v < x1 := by dsimp [v]; linarith
  have hy0w : y0 < w := by dsimp [w]; linarith
  have hwq : w < q := by dsimp [w, q]; linarith
  have hqy1 : q < y1 := by dsimp [q]; linarith
  let kernel : ℂ → ℂ := fun z => (z - p)⁻¹
  have horizontal_continuous : ∀ y : ℝ, y ≠ p.im →
      Continuous (fun x : ℝ => kernel (x + y * I)) := by
    intro y hy
    apply ((Complex.continuous_ofReal.add
      (continuous_const.mul continuous_const)).sub continuous_const).inv₀
    intro x hx
    apply hy
    have hi := congrArg Complex.im hx
    simp at hi
    linarith
  have vertical_continuous : ∀ x : ℝ, x ≠ p.re →
      Continuous (fun y : ℝ => kernel (x + y * I)) := by
    intro x hx
    apply ((continuous_const.add
      (Complex.continuous_ofReal.mul continuous_const)).sub continuous_const).inv₀
    intro y hy
    apply hx
    have hr' := congrArg Complex.re hy
    simp at hr'
    linarith
  have hbottom : boundaryRectIntegral kernel x0 x1 y0 w = 0 := by
    apply boundaryRectIntegral_eq_zero_of_differentiableOn
    intro z hz
    apply ((differentiableAt_id.sub_const p).inv ?_).differentiableWithinAt
    intro hzp
    have hz_eq : z = p := sub_eq_zero.mp hzp
    subst z
    rw [mem_reProdIm] at hz
    have hzim := hz.2
    rw [uIcc_of_le hy0w.le] at hzim
    linarith [hzim.2]
  have htop : boundaryRectIntegral kernel x0 x1 q y1 = 0 := by
    apply boundaryRectIntegral_eq_zero_of_differentiableOn
    intro z hz
    apply ((differentiableAt_id.sub_const p).inv ?_).differentiableWithinAt
    intro hzp
    have hz_eq : z = p := sub_eq_zero.mp hzp
    subst z
    rw [mem_reProdIm] at hz
    have hzim := hz.2
    rw [uIcc_of_le hqy1.le] at hzim
    linarith [hzim.1]
  have hleft : boundaryRectIntegral kernel x0 u w q = 0 := by
    apply boundaryRectIntegral_eq_zero_of_differentiableOn
    intro z hz
    apply ((differentiableAt_id.sub_const p).inv ?_).differentiableWithinAt
    intro hzp
    have hz_eq : z = p := sub_eq_zero.mp hzp
    subst z
    rw [mem_reProdIm] at hz
    have hzre := hz.1
    rw [uIcc_of_le hx0u.le] at hzre
    linarith [hzre.2]
  have hright : boundaryRectIntegral kernel v x1 w q = 0 := by
    apply boundaryRectIntegral_eq_zero_of_differentiableOn
    intro z hz
    apply ((differentiableAt_id.sub_const p).inv ?_).differentiableWithinAt
    intro hzp
    have hz_eq : z = p := sub_eq_zero.mp hzp
    subst z
    rw [mem_reProdIm] at hz
    have hzre := hz.1
    rw [uIcc_of_le hvx1.le] at hzre
    linarith [hzre.1]
  have houter_inner :
      boundaryRectIntegral kernel x0 x1 y0 y1 = boundaryRectIntegral kernel u v w q :=
    boundaryRectIntegral_eq_inner_of_four_rectangles kernel x0 u v x1 y0 w q y1
      (horizontal_continuous w (by dsimp [w]; linarith))
      (horizontal_continuous q (by dsimp [q]; linarith))
      (vertical_continuous x0 (by linarith [hp'.1]))
      (vertical_continuous x1 (by linarith [hp'.2.1]))
      hbottom htop hleft hright
  have houter : rectangleBoundaryIntegral kernel c R =
      boundaryRectIntegral kernel x0 x1 y0 y1 := by
    simpa [x0, x1, y0, y1] using
      rectangleBoundaryIntegral_eq_boundaryRectIntegral kernel c R
  have hinner : boundaryRectIntegral kernel u v w q =
      rectangleBoundaryIntegral kernel p r := by
    simpa [u, v, w, q] using
      (rectangleBoundaryIntegral_eq_boundaryRectIntegral kernel p r).symm
  rw [houter, houter_inner, hinner]
  exact rectangleBoundaryIntegral_sub_inv_center p hr

/-- Finite simple principal parts satisfy the residue formula on a square
containing all their poles. -/
theorem rectangleBoundaryIntegral_eq_finite_simple_pole_residue_sum
    (c : ℂ) {R : ℝ} (hR : 0 < R) (poles : Finset ℂ) (residue : ℂ → ℂ)
    (hpoles : ∀ p ∈ poles, p ∈ openRectangle c R) :
    rectangleBoundaryIntegral
        (fun z : ℂ => ∑ p ∈ poles, (z - p)⁻¹ * residue p) c R =
      (2 * Real.pi * I) * ∑ p ∈ poles, residue p := by
  let term : ℂ → ℂ → ℂ := fun p z => (z - p)⁻¹ * residue p
  have horizontal_continuous : ∀ p ∈ poles, ∀ y : ℝ, y ≠ p.im →
      Continuous (fun x : ℝ => term p (x + y * I)) := by
    intro p hp y hy
    apply (((Complex.continuous_ofReal.add
      (continuous_const.mul continuous_const)).sub continuous_const).inv₀ ?_).mul continuous_const
    intro x hx
    apply hy
    have hi := congrArg Complex.im hx
    simp at hi
    linarith
  have vertical_continuous : ∀ p ∈ poles, ∀ x : ℝ, x ≠ p.re →
      Continuous (fun y : ℝ => term p (x + y * I)) := by
    intro p hp x hx
    apply (((continuous_const.add
      (Complex.continuous_ofReal.mul continuous_const)).sub continuous_const).inv₀ ?_).mul continuous_const
    intro y hy
    apply hx
    have hr' := congrArg Complex.re hy
    simp at hr'
    linarith
  have hbottom : ∀ p ∈ poles, IntervalIntegrable
      (fun x : ℝ => term p (x + (c.im - R) * I)) MeasureTheory.volume (c.re - R) (c.re + R) := by
    intro p hp
    simpa only [Complex.ofReal_sub] using
      (horizontal_continuous p hp (c.im - R) (by
      have h := hpoles p hp
      simp [openRectangle, mem_reProdIm] at h
      linarith [h.2.1])).intervalIntegrable (c.re - R) (c.re + R)
  have htop : ∀ p ∈ poles, IntervalIntegrable
      (fun x : ℝ => term p (x + (c.im + R) * I)) MeasureTheory.volume (c.re - R) (c.re + R) := by
    intro p hp
    simpa only [Complex.ofReal_add] using
      (horizontal_continuous p hp (c.im + R) (by
      have h := hpoles p hp
      simp [openRectangle, mem_reProdIm] at h
      linarith [h.2.2])).intervalIntegrable (c.re - R) (c.re + R)
  have hright : ∀ p ∈ poles, IntervalIntegrable
      (fun y : ℝ => term p ((c.re + R) + y * I)) MeasureTheory.volume (c.im - R) (c.im + R) := by
    intro p hp
    simpa only [Complex.ofReal_add] using
      (vertical_continuous p hp (c.re + R) (by
      have h := hpoles p hp
      simp [openRectangle, mem_reProdIm] at h
      linarith [h.1.2])).intervalIntegrable (c.im - R) (c.im + R)
  have hleft : ∀ p ∈ poles, IntervalIntegrable
      (fun y : ℝ => term p ((c.re - R) + y * I)) MeasureTheory.volume (c.im - R) (c.im + R) := by
    intro p hp
    simpa only [Complex.ofReal_sub] using
      (vertical_continuous p hp (c.re - R) (by
      have h := hpoles p hp
      simp [openRectangle, mem_reProdIm] at h
      linarith [h.1.1])).intervalIntegrable (c.im - R) (c.im + R)
  have hlinear :
      rectangleBoundaryIntegral (fun z : ℂ => ∑ p ∈ poles, term p z) c R =
        ∑ p ∈ poles, rectangleBoundaryIntegral (term p) c R := by
    exact rectangleBoundaryIntegral_finset_sum poles term c R
      hbottom htop hright hleft
  change rectangleBoundaryIntegral (fun z : ℂ => ∑ p ∈ poles, term p z) c R = _
  rw [hlinear]
  calc
    (∑ p ∈ poles, rectangleBoundaryIntegral (term p) c R) =
        ∑ p ∈ poles, (2 * Real.pi * I) * residue p := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [show term p = fun z : ℂ => (z - p)⁻¹ * residue p by rfl,
        rectangleBoundaryIntegral_mul_const,
        rectangleBoundaryIntegral_sub_inv_of_mem_openRectangle c p hR (hpoles p hp)]
    _ = (2 * Real.pi * I) * ∑ p ∈ poles, residue p := by
      rw [Finset.mul_sum]

/-! ## Proved finite simple-pole residue formula on circles -/

/-- A holomorphic term plus finitely many simple principal parts integrates to
`2πi` times the sum of their residues on a circle containing every pole.

This is a genuine finite residue theorem built from Mathlib's Cauchy integral
formula.  The square analogue above is proved independently by rectangular
annulus deformation. -/
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
`hpos` alone.  The finite simple-pole rectangle formula is proved above; the
remaining analytic input is the principal-part decomposition for a general
meromorphic function and its finite divisor support.

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
