# Classical PNT Error Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove the real-variable de la Vallee Poussin estimate
`|chebyshevPsi x - x| <= C * x * exp (-c * sqrt (log x))` for all sufficiently large `x`.

**Architecture:** Start from the proved moving-height midpoint bound in
`PNTFiniteZeroSum.lean`. First absorb its polynomial square-root-log factors
into a weaker exponential. Then absorb the von Mangoldt half-jump and transfer
the natural-point estimate to real inputs using Mathlib's floor identity for
`Chebyshev.psi`.

**Tech Stack:** Lean 4.29.1, Mathlib asymptotics, filters, real logarithm and
exponential estimates.

## Global Constraints

- Do not add `sorry`, `admit`, custom axioms, or `def ... : Prop` placeholders.
- The final result must concern right-continuous `chebyshevPsi` on real inputs.
- A natural-sample or midpoint-only theorem does not complete this stage.
- Keep the de la Vallee Poussin-form `psi` remainder separate from RH-scale
  error claims and from any claim of numerically explicit constants.

---

### Task 1: Final theorem contract

**Files:**
- Create: `Test/ClassicalPNTErrorContract.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes: `PrimeNumberTheorem.chebyshevPsi`
- Produces: a compile-time contract for
  `PrimeNumberTheorem.exists_abs_chebyshevPsi_sub_id_le_exp_neg_sqrt_log`

- [x] Add a contract requiring
  ```lean
  example :
      exists c C X : Real, 0 < c /\ 0 <= C /\ forall x : Real, X <= x ->
        |chebyshevPsi x - x| <=
          C * x * Real.exp (-c * Real.sqrt (Real.log x)) :=
    exists_abs_chebyshevPsi_sub_id_le_exp_neg_sqrt_log
  ```
- [x] Run `lake build Test.ClassicalPNTErrorContract` and verify that it fails
  because the module or declaration does not exist.

### Task 2: Natural-sample exponential cleanup

**Files:**
- Create: `PrimeNumberTheorem/ClassicalPNTError.lean`

**Interfaces:**
- Consumes:
  `ExplicitFormulaAux.exists_nat_abs_chebyshevPsi0_sub_id_le_exp_sqrt_log`
- Produces:
  `exists_nat_abs_chebyshevPsi0_sub_id_le_exp_neg_sqrt_log`

- [x] Choose `c = min a (1/2) / 2`, so `0 < c`, `c < a`, and `c < 1/2`.
- [x] Use `tendsto_pntSqrtLog_pow_mul_exp_neg_mul_atTop_nhds_zero` with
  decay rates `a-c` and `1/2-c` to make both polynomial factors eventually at
  most `1` after factoring out `exp (-c*u)`.
- [x] Combine the two terms to prove, for all sufficiently large natural `m`,
  ```lean
  |chebyshevPsi0 (m : Real) - m| <=
    (2 * C) * m * Real.exp (-c * pntSqrtLog m).
  ```

### Task 3: Remove midpoint convention

**Files:**
- Modify: `PrimeNumberTheorem/ClassicalPNTError.lean`

**Interfaces:**
- Consumes: `jumpVonMangoldt_natCast_nonneg_le_log`
- Produces: `exists_nat_abs_chebyshevPsi_sub_id_le_exp_neg_sqrt_log`

- [x] Prove that `log m` is eventually bounded by
  `m * exp (-c' * pntSqrtLog m)` after replacing `c` by `c/2`.
- [x] Apply `chebyshevPsi0 = chebyshevPsi - jumpVonMangoldt/2` and the triangle
  inequality to absorb the half-jump into the same exponential scale.
- [x] Run the focused module build.

### Task 4: Transfer from naturals to reals

**Files:**
- Modify: `PrimeNumberTheorem/ClassicalPNTError.lean`
- Modify: `RiemannPNT.lean`

**Interfaces:**
- Consumes: `Chebyshev.psi_eq_psi_coe_floor`
- Produces:
  `exists_abs_chebyshevPsi_sub_id_le_exp_neg_sqrt_log`

- [x] Set `m = Nat.floor x`, use `psi x = psi m`, and bound `|x-m| <= 1`.
- [x] For sufficiently large `x`, prove `m >= sqrt x`; hence
  `sqrt (log m) >= (1/2) * sqrt (log x)`.
- [x] Weaken the decay constant once more to compare the natural majorant with
  `x * exp (-c * sqrt (log x))`, and absorb the floor error `1`.
- [x] Export the final theorem through `RiemannPNT.API`.

### Task 5: Verification and publication boundary

**Files:**
- Modify: `Test/MultiplicityAxiomAudit.lean`
- Modify: `scripts/check_axiom_allowlist.py`
- Modify: `README.md`
- Modify: `docs/mathematical-contributions.md`

**Interfaces:**
- Consumes: final Task 4 theorem
- Produces: audited repository-level de la Vallee Poussin-form Chebyshev claim

- [x] Run the focused contract, target inventory, chain-gap checks, Python
  tests, axiom allowlist, and default `lake build`.
- [x] State explicitly that this proves the classical de la Vallee Poussin-form `psi` error,
  not RH, the RH-scale error, or the `Re(s)=1/3` zero exclusion.
- [x] Obtain an independent proof review.
