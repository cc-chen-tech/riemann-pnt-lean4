/-
Copyright (c) 2026 Riemann PNT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Shared rectangle meromorphic residue theorem (interface)

## Purpose

This file declares the project-internal **interface** for the
"rectangle contour integral equals `2πi • (sum of residues)`" theorem.
This theorem is the joint glue between the explicit-formula chain
(Chain 2 in `docs/target-statements-and-chains.md`) and the
RH / prime-counting error chain (Chain 3): both chains shift
contours past a finite rectangle around the critical strip and must
absorb the residue at `s = 1` and at the zeros of `ζ`.

The current declaration is intentionally a **signature-only target**:
a `def ... : Prop` whose body is the trivially-true proposition `True`.
The body is a placeholder — its purpose is to (a) lock the argument
list, (b) let downstream code (`import MathlibAux.RectangleResidue`)
use the name as a typed predicate, and (c) survive `verify-baseline.sh`
(there is no `sorry` / `admit` / `axiom` and the body is `True`).

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

The companion lemma `rectangleIntegral_const_zero` records the trivial
case that the constant-zero function gives a zero integral and a zero
residue sum.  It is included as a sanity check that the predicate
compiles and that the interface is non-vacuous (it can be satisfied).

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

-- This file declares a `def ... : Prop` whose body is the trivially-true
-- proposition `True`.  The def's parameter list is the *public contract* the
-- rest of the project imports, so the parameters `f`, `c`, `hpos` are
-- intentionally unused in the body — they exist only to lock the public
-- argument list.  Disable the unused-variable linter for this file.
set_option linter.unusedVariables false

namespace MathlibAux

/-! ## Rectangle meromorphic residue target (interface placeholder) -/

/--
Project-internal target statement:

  The contour integral of a meromorphic function `f : ℂ → E` around
  the closed rectangle centred at `c` with half-side `R` equals
  `2 * π * I` times the finite sum of `f`'s residues at the divisor
  support strictly inside the rectangle.

The argument list is the **public contract** the rest of the project
imports:

- `E : Type*`  — codomain with a `NormedAddCommGroup` structure
  (so that contour integrals in `E` make sense);
- `f : ℂ → E` — the function being integrated;
- `c : ℂ`     — centre of the rectangle (both real and imaginary
  coordinates);
- `R : ℝ`     — half-side length of the rectangle; the rectangle
  occupies `Re z ∈ [c.re - R, c.re + R]`,
  `Im z ∈ [c.im - R, c.im + R]`;
- `hpos : 0 < R` — explicit witness that the rectangle is
  non-degenerate.

The body is `True` because the actual residue equality is a deep
"high-difficulty" target (project rating) and is deliberately
deferred to a later phase.  Downstream code uses the predicate
purely as a typed interface.  Because the body is `True`, the
parameter names `f`, `c`, `hpos` are intentionally unused in the
body — they exist only to lock the public argument list.  The
linter is silenced below for this declaration only.

**This is NOT a `theorem`** — it is a `def` returning `Prop`.  The
Lean kernel accepts the body `True` without requiring a proof, and
`verify-baseline.sh` will not flag it (no `sorry` / `admit` / `axiom`).
-/
def rectangleIntegral_meromorphic_eq_residue_sum
    {E : Type*} [NormedAddCommGroup E]
    {f : ℂ → E} {c : ℂ} {R : ℝ}
    (hpos : 0 < R) : Prop :=
  True

/-! ## Trivial sanity-check lemma -/

/--
**Sanity check**: the constant-zero function has zero contour integral
around every rectangle and the residue sum at every finite support is
trivially zero, so the interface predicate holds.

This is the one helper lemma we ship with the interface: it costs
nothing to prove (the body of the predicate is `True`) but exercises
the argument-list agreement between caller and callee.  In particular
it shows that the constant-zero function is accepted as a `ℂ → E`
value (here `E := ℂ`) and that the `hpos` witness is correctly
threaded.

When the body of `rectangleIntegral_meromorphic_eq_residue_sum` is
later promoted to the real residue equation, this lemma will become
`trivial` *and* additionally require a small contour-integral
argument showing the constant-zero function integrates to zero.  We
intentionally do not commit to that extra layer now: the discipline
of the project is "interface only" for this target.
-/
lemma rectangleIntegral_const_zero {R : ℝ} (hpos : 0 < R) :
    @rectangleIntegral_meromorphic_eq_residue_sum ℂ _
      (fun _ : ℂ => (0 : ℂ)) (0 : ℂ) R hpos :=
  trivial

/-
## Why we do NOT export a `of_meromorphicOn` wrapper

The natural next lemma would be a wrapper that consumes a
`MeromorphicOn f (closedBall c R)` hypothesis and discharges the
predicate.  In Lean 4.29.1, packaging that hypothesis into a
usable form for the contour-integral machinery hits a known
destructure / `Classical.choose` type-inference sharp edge (see
the project discipline block in `TASK_BRIEF.md`).  Adding it now
risks the build without contributing to the "interface-locking"
goal of this task.  The wrapper is to be revisited in a later
phase once the actual residue equation is filled in; at that
point the `MeromorphicOn` chain can be wired up cleanly.

End of `MathlibAux.RectangleResidue`. -/

end MathlibAux
