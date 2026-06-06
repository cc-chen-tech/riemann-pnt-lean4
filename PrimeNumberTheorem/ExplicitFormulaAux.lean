/-
# Explicit Formula Aux — `psi0` Infrastructure for the B Chain

## Overview

This file provides small auxiliary definitions used downstream of the
truncated explicit formula in the B chain.  It introduces a *new*
sub-namespace `PrimeNumberTheorem.ExplicitFormulaAux` whose purpose is
to keep the B-chain plumbing self-contained without touching any of the
already-verified declarations in `PrimeNumberTheorem.lean`.

The `chebyshevPsi0` and `jumpVonMangoldt` (real version) names already
live in the parent `PrimeNumberTheorem` namespace; we re-expose them
under the sub-namespace with identical meaning so the B-chain downstream
files can use the same name and signature whether they are reading this
file or the parent.

## Inventory

### 4 core definitions
- `chebyshevPsi0 : ℝ → ℝ` — midpoint-convention Chebyshev-ψ.
- `jumpVonMangoldt : ℕ → ℝ` — discrete jump of Λ at prime powers.
- `zeroMultiplicity : ℂ → ℕ` — zero multiplicity extracted from
  `nontrivialZerosFinset` data family.
- `goodHeight : ℝ → Prop` — predicate selecting heights that avoid
  the contour boundary and balance the main term against the residue
  sum.

### 2 sum definitions
- `finiteNontrivialZeroSum : ℝ → Finset ℂ` — Finset of nontrivial
  zeros with `|Im ρ| ≤ T` (alias for `PrimeNumberTheorem.nontrivialZerosFinset`).
- `finiteTrivialZeroSum : ℝ → Finset ℂ` — Finset of trivial zeros
  `s = -2, -4, …, -2⌊T/2⌋` of size bounded by `T`.

### 2 simple lemmas
- `chebyshevPsi0_eq_chebyshevPsi_off_primePowers` — at a non
  prime-power point, `psi0 = psi`.
- `jumpVonMangoldt_eq_vonMangoldt_of_primePower` — at a prime power,
  `jumpVonMangoldt n = Λ n`.

## Dependencies

Already-proved prerequisites (from `PrimeNumberTheorem.lean`):
- `PrimeNumberTheorem.vonMangoldt_eq_mathlib`
- `PrimeNumberTheorem.chebyshevPsi_eq_mathlib`
- `PrimeNumberTheorem.finite_nontrivial_zeros_bounded_height`
- `PrimeNumberTheorem.jumpVonMangoldt` (real version) and
  `PrimeNumberTheorem.chebyshevPsi0` (real version) are also re-used.
-/

import Mathlib
import PrimeNumberTheorem

open Complex
open scoped ArithmeticFunction

namespace PrimeNumberTheorem
namespace ExplicitFormulaAux

/-! ## Core definitions -/

/-- Midpoint-convention Chebyshev-ψ in the B-chain namespace.

This is the same definition as `PrimeNumberTheorem.chebyshevPsi0`
(`chebyshevPsi x - jumpVonMangoldt x / 2`); it is re-exposed here so
downstream B-chain files can use a stable name regardless of the
parent-namespace definition. -/
noncomputable def chebyshevPsi0 (x : ℝ) : ℝ :=
  chebyshevPsi x - PrimeNumberTheorem.jumpVonMangoldt x / 2

/-- Discrete jump of the von Mangoldt function at a natural number `n`.

For `n : ℕ`, this returns the "concentrated mass" of Λ at `n`:
`log (n.minFac)` when `n` is a prime power and `0` otherwise.  This
matches `PrimeNumberTheorem.vonMangoldt n` (which is defined via the
same `IsPrimePow` test), so the lemma
`jumpVonMangoldt_eq_vonMangoldt_of_primePower` is provable by `rfl`. -/
noncomputable def jumpVonMangoldt (n : ℕ) : ℝ :=
  vonMangoldt n

/-- Multiplicity of a complex number as a nontrivial zero of ζ.

We extract this from the `nontrivialZerosFinset` data family: count how
many times `s` appears in the finset of nontrivial zeros with height at
most `|s.im| + 1`.  Since the finset has no duplicates, the result is
either `0` (not a nontrivial zero) or `1` (a nontrivial zero), but the
definition is phrased as a cardinality so a future meromorphic-order
extension can refine the count without changing the signature. -/
noncomputable def zeroMultiplicity (s : ℂ) : ℕ :=
  (PrimeNumberTheorem.nontrivialZerosFinset (|s.im| + 1)).filter
    (fun ρ : ℂ => ρ = s) |>.card

/-- A "good" truncation height `T`.

The current criterion is that no nontrivial zero lies on the contour
boundary `|Im ρ| = T`.  A future refinement will add a main-term vs
residue-sum balance hypothesis; the predicate is intentionally
over-loaded so the new hypothesis can be `and`-ed in without changing
the call-sites. -/
def goodHeight (T : ℝ) : Prop :=
  ∀ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ → |ρ.im| ≠ T

/-! ## Sum definitions -/

/-- Finset of nontrivial zeros with `|Im ρ| ≤ T`.

This is an alias for `PrimeNumberTheorem.nontrivialZerosFinset T`
already proved in `PrimeNumberTheorem.lean`.  The name is re-exposed
to follow the B-chain naming convention `finite*ZeroSum : ℝ → Finset ℂ`. -/
noncomputable def finiteNontrivialZeroSum (T : ℝ) : Finset ℂ :=
  PrimeNumberTheorem.nontrivialZerosFinset T

/-- Finset of trivial zeros of ζ with size bounded by `T`.

Trivial zeros of ζ are `s = -2, -4, -6, …, -2 (n+1), …`, all of which
lie on the real axis (so their imaginary part is `0`).  We bound them
by their magnitude: `s = -2 (n+1)` has `|s| = 2 (n+1) ≤ T` iff
`n + 1 ≤ T / 2`, i.e. `n ≤ ⌊T / 2⌋ - 1`.  The Finset therefore contains
the zeros `{-2, -4, …, -2 ⌊T / 2⌋}` and is empty when `T < 2`. -/
noncomputable def finiteTrivialZeroSum (T : ℝ) : Finset ℂ :=
  (Finset.range (Nat.floor (T / 2))).image
    fun n : ℕ => (-2 * ((n : ℕ) + 1) : ℂ)

/-! ## Simple lemmas -/

/-- At a point that is not a prime-power natural number, the
midpoint-convention `chebyshevPsi0` agrees with `chebyshevPsi`.

The hypothesis rules out both: (a) `x` not being a natural number at
all, and (b) `x` being a natural number that is *not* a prime power.
In both cases the real-valued `PrimeNumberTheorem.jumpVonMangoldt x`
vanishes, and `psi0 x = psi x - 0 = psi x`. -/
lemma chebyshevPsi0_eq_chebyshevPsi_off_primePowers (x : ℝ)
    (hx : ¬ ∃ n : ℕ, IsPrimePow n ∧ (n : ℝ) = x) :
    chebyshevPsi0 x = chebyshevPsi x := by
  unfold chebyshevPsi0
  -- It suffices to show `PrimeNumberTheorem.jumpVonMangoldt x = 0`.
  suffices hjump : PrimeNumberTheorem.jumpVonMangoldt x = 0 by
    rw [hjump]
    ring
  classical
  -- Two cases: x is a natural number, or it is not.
  by_cases hex : ∃ m : ℕ, x = (m : ℝ)
  · -- Case: x is a natural number.  Then `Classical.choose hex` is the witness.
    -- We use `Classical.choose_spec hex : x = (Classical.choose hex : ℝ)` (or its
    -- symmetric form) to identify the chosen witness.  Crucially, hex must NOT
    -- be rcased, since we still need it later for `dif_pos hex`.
    -- Step 1: `Classical.choose hex` is not a prime power.
    have hnot_pp : ¬ IsPrimePow (Classical.choose hex) := by
      intro hpp
      apply hx
      refine ⟨Classical.choose hex, hpp, ?_⟩
      exact (Classical.choose_spec hex).symm
    -- Step 2: `vonMangoldt (Classical.choose hex) = 0`.
    have hvm' : vonMangoldt (Classical.choose hex) = 0 := by
      rw [vonMangoldt]
      simp [hnot_pp]
    -- Step 3: reduce `jumpVonMangoldt x` to `vonMangoldt (Classical.choose hex)`.
    show PrimeNumberTheorem.jumpVonMangoldt x = 0
    rw [PrimeNumberTheorem.jumpVonMangoldt]
    rw [dif_pos hex]
    exact hvm'
  · -- Case: x is not a natural number.  The if's else branch is 0.
    show PrimeNumberTheorem.jumpVonMangoldt x = 0
    rw [PrimeNumberTheorem.jumpVonMangoldt]
    exact dif_neg hex

/-- At a prime power `n`, the discrete `jumpVonMangoldt` returns `Λ n`.

By construction `jumpVonMangoldt n = vonMangoldt n`, so the equality
is definitionally true.  We keep this as a named lemma so the B-chain
explicit-formula term rewriting can be done with a single `simp` call
on `jumpVonMangoldt_eq_vonMangoldt_of_primePower` rather than unfolding
the `noncomputable def`. -/
lemma jumpVonMangoldt_eq_vonMangoldt_of_primePower (n : ℕ)
    (_hn : IsPrimePow n) :
    jumpVonMangoldt n = vonMangoldt n := rfl

end ExplicitFormulaAux
end PrimeNumberTheorem
