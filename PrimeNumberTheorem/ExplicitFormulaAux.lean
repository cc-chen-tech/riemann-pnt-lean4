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

### Support lemmas
- `goodHeight_iff_no_zero_at_height` and
  `not_goodHeight_iff_exists_zero_at_height` — boundary-height
  normalizations.
- `nontrivial_zero_mem_self_height`,
  `zeroMultiplicity_eq_one_of_mem`, and
  `zeroMultiplicity_eq_zero_of_not_mem` — current finite-truncation
  multiplicity bookkeeping.
- `mem_finiteTrivialZeroSum_iff`,
  `finiteTrivialZeroSum_im_eq_zero_of_mem`,
  `finiteTrivialZeroSum_re_lt_zero_of_mem`,
  `finiteTrivialZeroSum_re_le_neg_two_of_mem`,
  `finiteTrivialZeroSum_ne_zero_of_mem`,
  `finiteTrivialZeroSum_abs_im_eq_zero_of_mem`,
  `finiteTrivialZeroSum_not_isNontrivialZero_of_mem`, and
  `finiteTrivialZeroSum_card_le` — finite trivial-zero support facts.
- `finiteTrivialZeroSum_two_le_norm_of_mem` and
  `finiteTrivialZeroSum_inv_norm_le_half_of_mem` — denominator-estimate
  forms for retained finite trivial zeros.
- `norm_trivial_zero_contribution_le_half_rpow_re` — single-term norm bound
  for retained finite trivial-zero contributions.
- `norm_trivial_zero_contribution_le_half_rpow_neg_two` — the `x >= 1`
  specialization using `Re(s) <= -2`.
- `norm_finiteTrivialZeroSum_contribution_le_half_sum_rpow_re` — finite-sum
  norm bound for retained finite trivial-zero contributions.
- `norm_finiteTrivialZeroSum_contribution_le_card_mul_half_rpow_neg_two` —
  finite-sum `x >= 1` bound using only the truncation cardinality.
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

/-! ## Boundary-height normalization -/

/-- A good height is exactly a height that no nontrivial zero reaches on the
horizontal contour boundary. -/
lemma goodHeight_iff_no_zero_at_height (T : ℝ) :
    goodHeight T ↔
      ¬ ∃ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ ∧ |ρ.im| = T := by
  constructor
  · intro hgood hbad
    rcases hbad with ⟨ρ, hρ, hheight⟩
    exact (hgood ρ hρ) hheight
  · intro hnone ρ hρ hheight
    exact hnone ⟨ρ, hρ, hheight⟩

/-- Failure of `goodHeight` is the existence of a nontrivial zero on the
horizontal contour boundary. -/
lemma not_goodHeight_iff_exists_zero_at_height (T : ℝ) :
    ¬ goodHeight T ↔
      ∃ ρ : ℂ, RiemannHypothesis.IsNontrivialZero ρ ∧ |ρ.im| = T := by
  classical
  rw [goodHeight_iff_no_zero_at_height]
  exact not_not

/-! ## Sum definitions -/

/-- Finset of nontrivial zeros with `|Im ρ| ≤ T`.

This is an alias for `PrimeNumberTheorem.nontrivialZerosFinset T`
already proved in `PrimeNumberTheorem.lean`.  The name is re-exposed
to follow the B-chain naming convention `finite*ZeroSum : ℝ → Finset ℂ`. -/
noncomputable def finiteNontrivialZeroSum (T : ℝ) : Finset ℂ :=
  PrimeNumberTheorem.nontrivialZerosFinset T

/-- A nontrivial zero belongs to the self-height truncation used by
`zeroMultiplicity`. -/
lemma nontrivial_zero_mem_self_height {ρ : ℂ}
    (hρ : RiemannHypothesis.IsNontrivialZero ρ) :
    ρ ∈ finiteNontrivialZeroSum (|ρ.im| + 1) := by
  unfold finiteNontrivialZeroSum
  exact PrimeNumberTheorem.nontrivial_zero_mem_nontrivialZerosFinset hρ
    (by linarith)

/-- The current finset-based multiplicity is `1` for members of its
self-height truncation. -/
lemma zeroMultiplicity_eq_one_of_mem {s : ℂ}
    (hs : s ∈ finiteNontrivialZeroSum (|s.im| + 1)) :
    zeroMultiplicity s = 1 := by
  classical
  change s ∈ PrimeNumberTheorem.nontrivialZerosFinset (|s.im| + 1) at hs
  unfold zeroMultiplicity
  let S : Finset ℂ :=
    PrimeNumberTheorem.nontrivialZerosFinset (|s.im| + 1)
  have hfilter : S.filter (fun ρ : ℂ => ρ = s) = {s} := by
    ext ρ
    by_cases hρs : ρ = s
    · subst hρs
      simp [S, hs]
    · simp [hρs]
  simp [S, hfilter]

/-- The current finset-based multiplicity is `0` away from its self-height
truncation. -/
lemma zeroMultiplicity_eq_zero_of_not_mem {s : ℂ}
    (hs : s ∉ finiteNontrivialZeroSum (|s.im| + 1)) :
    zeroMultiplicity s = 0 := by
  classical
  change s ∉ PrimeNumberTheorem.nontrivialZerosFinset (|s.im| + 1) at hs
  unfold zeroMultiplicity
  let S : Finset ℂ :=
    PrimeNumberTheorem.nontrivialZerosFinset (|s.im| + 1)
  have hfilter : S.filter (fun ρ : ℂ => ρ = s) = ∅ := by
    ext ρ
    by_cases hρs : ρ = s
    · subst hρs
      simp [S, hs]
    · simp [hρs]
  simp [S, hfilter]

/-- Finset of trivial zeros of ζ with size bounded by `T`.

Trivial zeros of ζ are `s = -2, -4, -6, …, -2 (n+1), …`, all of which
lie on the real axis (so their imaginary part is `0`).  We bound them
by their magnitude: `s = -2 (n+1)` has `|s| = 2 (n+1) ≤ T` iff
`n + 1 ≤ T / 2`, i.e. `n ≤ ⌊T / 2⌋ - 1`.  The Finset therefore contains
the zeros `{-2, -4, …, -2 ⌊T / 2⌋}` and is empty when `T < 2`. -/
noncomputable def finiteTrivialZeroSum (T : ℝ) : Finset ℂ :=
  (Finset.range (Nat.floor (T / 2))).image
    fun n : ℕ => (-2 * ((n : ℕ) + 1) : ℂ)

/-- Membership in the finite trivial-zero truncation is exactly being one of
the displayed negative even integers in the chosen range. -/
lemma mem_finiteTrivialZeroSum_iff {s : ℂ} {T : ℝ} :
    s ∈ finiteTrivialZeroSum T ↔
      ∃ n : ℕ, n < Nat.floor (T / 2) ∧
        (-2 * ((n : ℕ) + 1) : ℂ) = s := by
  constructor
  · intro hs
    rw [finiteTrivialZeroSum, Finset.mem_image] at hs
    rcases hs with ⟨n, hn, hns⟩
    exact ⟨n, Finset.mem_range.mp hn, hns⟩
  · rintro ⟨n, hn, hns⟩
    rw [finiteTrivialZeroSum, Finset.mem_image]
    exact ⟨n, Finset.mem_range.mpr hn, hns⟩

/-- Elements of the finite trivial-zero truncation lie on the real axis. -/
lemma finiteTrivialZeroSum_im_eq_zero_of_mem {s : ℂ} {T : ℝ}
    (hs : s ∈ finiteTrivialZeroSum T) :
    s.im = 0 := by
  rcases mem_finiteTrivialZeroSum_iff.mp hs with ⟨n, _hn, hns⟩
  rw [← hns]
  simp

/-- Elements of the finite trivial-zero truncation have negative real part. -/
lemma finiteTrivialZeroSum_re_lt_zero_of_mem {s : ℂ} {T : ℝ}
    (hs : s ∈ finiteTrivialZeroSum T) :
    s.re < 0 := by
  rcases mem_finiteTrivialZeroSum_iff.mp hs with ⟨n, _hn, hns⟩
  rw [← hns]
  norm_num
  exact_mod_cast Nat.succ_pos n

/-- Retained trivial zeros have real part at most `-2`. -/
lemma finiteTrivialZeroSum_re_le_neg_two_of_mem {s : ℂ} {T : ℝ}
    (hs : s ∈ finiteTrivialZeroSum T) :
    s.re ≤ -2 := by
  rcases mem_finiteTrivialZeroSum_iff.mp hs with ⟨n, _hn, hns⟩
  rw [← hns]
  norm_num

/-- The number of retained trivial zeros is at most the floor cutoff. -/
lemma finiteTrivialZeroSum_card_le (T : ℝ) :
    (finiteTrivialZeroSum T).card ≤ Nat.floor (T / 2) := by
  unfold finiteTrivialZeroSum
  simpa using
    (Finset.card_image_le :
      ((Finset.range (Nat.floor (T / 2))).image
        (fun n : ℕ => (-2 * ((n : ℕ) + 1) : ℂ))).card ≤
          (Finset.range (Nat.floor (T / 2))).card)

/-- Retained trivial zeros are never the origin.  This is the small
denominator-safety fact needed before forming explicit-formula terms
`x^s / s` over the trivial-zero truncation. -/
lemma finiteTrivialZeroSum_ne_zero_of_mem {s : ℂ} {T : ℝ}
    (hs : s ∈ finiteTrivialZeroSum T) :
    s ≠ 0 := by
  have hneg : s.re < 0 := finiteTrivialZeroSum_re_lt_zero_of_mem hs
  intro hs0
  rw [hs0] at hneg
  norm_num at hneg

/-- Absolute-height normalization for retained trivial zeros.  They all lie
on the real axis, so their imaginary height is exactly zero. -/
lemma finiteTrivialZeroSum_abs_im_eq_zero_of_mem {s : ℂ} {T : ℝ}
    (hs : s ∈ finiteTrivialZeroSum T) :
    |s.im| = 0 := by
  rw [finiteTrivialZeroSum_im_eq_zero_of_mem hs]
  simp

/-- Retained trivial zeros have norm at least `2`. -/
lemma finiteTrivialZeroSum_two_le_norm_of_mem {s : ℂ} {T : ℝ}
    (hs : s ∈ finiteTrivialZeroSum T) :
    2 ≤ ‖s‖ := by
  have hre : s.re ≤ -2 := finiteTrivialZeroSum_re_le_neg_two_of_mem hs
  have habs : 2 ≤ |s.re| := by
    rw [abs_of_nonpos (by linarith : s.re ≤ 0)]
    linarith
  exact le_trans habs (Complex.abs_re_le_norm s)

/-- The reciprocal norm of a retained trivial zero is at most `1/2`. -/
lemma finiteTrivialZeroSum_inv_norm_le_half_of_mem {s : ℂ} {T : ℝ}
    (hs : s ∈ finiteTrivialZeroSum T) :
    ‖s‖⁻¹ ≤ (1 / 2 : ℝ) := by
  have hnorm : (2 : ℝ) ≤ ‖s‖ := finiteTrivialZeroSum_two_le_norm_of_mem hs
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hnorm
  simpa [one_div] using h

/-- A retained trivial-zero contribution has denominator at least `2`, so its
norm is bounded by half of the usual `x ^ Re(s)` amplitude. -/
lemma norm_trivial_zero_contribution_le_half_rpow_re {s : ℂ} {T x : ℝ}
    (hs : s ∈ finiteTrivialZeroSum T) (hx : 0 < x) :
    ‖(x : ℂ) ^ s / s‖ ≤ (1 / 2 : ℝ) * x ^ s.re := by
  rw [PrimeNumberTheorem.norm_zero_contribution_eq s hx]
  have hx_nonneg : 0 ≤ x ^ s.re :=
    Real.rpow_nonneg (le_of_lt hx) s.re
  have hinv : ‖s‖⁻¹ ≤ (1 / 2 : ℝ) :=
    finiteTrivialZeroSum_inv_norm_le_half_of_mem hs
  calc
    x ^ s.re / ‖s‖ = x ^ s.re * ‖s‖⁻¹ := by
      rw [div_eq_mul_inv]
    _ ≤ x ^ s.re * (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hinv hx_nonneg
    _ = (1 / 2 : ℝ) * x ^ s.re := by ring

/-- For `x >= 1`, each retained trivial-zero contribution is bounded by the
first trivial-zero amplitude `x^(-2)` times the denominator factor `1/2`. -/
lemma norm_trivial_zero_contribution_le_half_rpow_neg_two {s : ℂ} {T x : ℝ}
    (hs : s ∈ finiteTrivialZeroSum T) (hx : 1 ≤ x) :
    ‖(x : ℂ) ^ s / s‖ ≤ (1 / 2 : ℝ) * x ^ (-2 : ℝ) := by
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hterm := norm_trivial_zero_contribution_le_half_rpow_re hs hx_pos
  have hre : s.re ≤ -2 := finiteTrivialZeroSum_re_le_neg_two_of_mem hs
  have hrpow : x ^ s.re ≤ x ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx hre
  have hmul : (1 / 2 : ℝ) * x ^ s.re ≤ (1 / 2 : ℝ) * x ^ (-2 : ℝ) :=
    mul_le_mul_of_nonneg_left hrpow (by norm_num)
  exact le_trans hterm hmul

/-- Finite retained trivial-zero contributions are bounded by the sum of the
single-term `x ^ Re(s)` amplitudes.  This is still only the finite truncation,
not the infinite trivial-zero correction. -/
lemma norm_finiteTrivialZeroSum_contribution_le_half_sum_rpow_re
    (T x : ℝ) (hx : 0 < x) :
    ‖∑ s ∈ finiteTrivialZeroSum T, (x : ℂ) ^ s / s‖ ≤
      ∑ s ∈ finiteTrivialZeroSum T, (1 / 2 : ℝ) * x ^ s.re := by
  calc
    ‖∑ s ∈ finiteTrivialZeroSum T, (x : ℂ) ^ s / s‖
        ≤ ∑ s ∈ finiteTrivialZeroSum T, ‖(x : ℂ) ^ s / s‖ :=
          norm_sum_le _ _
    _ ≤ ∑ s ∈ finiteTrivialZeroSum T, (1 / 2 : ℝ) * x ^ s.re := by
          exact Finset.sum_le_sum (fun s hs =>
            norm_trivial_zero_contribution_le_half_rpow_re hs hx)

/-- For `x >= 1`, the finite retained trivial-zero contribution is bounded by
the number of retained trivial zeros times the first trivial-zero amplitude. -/
lemma norm_finiteTrivialZeroSum_contribution_le_card_mul_half_rpow_neg_two
    (T x : ℝ) (hx : 1 ≤ x) :
    ‖∑ s ∈ finiteTrivialZeroSum T, (x : ℂ) ^ s / s‖ ≤
      ((finiteTrivialZeroSum T).card : ℝ) * ((1 / 2 : ℝ) * x ^ (-2 : ℝ)) := by
  calc
    ‖∑ s ∈ finiteTrivialZeroSum T, (x : ℂ) ^ s / s‖
        ≤ ∑ s ∈ finiteTrivialZeroSum T, ‖(x : ℂ) ^ s / s‖ :=
          norm_sum_le _ _
    _ ≤ ∑ _s ∈ finiteTrivialZeroSum T, (1 / 2 : ℝ) * x ^ (-2 : ℝ) := by
          exact Finset.sum_le_sum (fun s hs =>
            norm_trivial_zero_contribution_le_half_rpow_neg_two hs hx)
    _ = ((finiteTrivialZeroSum T).card : ℝ) *
        ((1 / 2 : ℝ) * x ^ (-2 : ℝ)) := by
          simp [mul_comm, mul_assoc]

/-- Retained trivial zeros are disjoint from the nontrivial-zero strip
predicate.  This records the separation between the finite trivial-zero
correction and the nontrivial-zero sum used in the explicit-formula chain. -/
lemma finiteTrivialZeroSum_not_isNontrivialZero_of_mem {s : ℂ} {T : ℝ}
    (hs : s ∈ finiteTrivialZeroSum T) :
    ¬ RiemannHypothesis.IsNontrivialZero s := by
  intro hnontrivial
  exact (not_lt_of_ge (le_of_lt (finiteTrivialZeroSum_re_lt_zero_of_mem hs)))
    hnontrivial.2.1

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
