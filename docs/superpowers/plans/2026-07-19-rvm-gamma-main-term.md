# Riemann-von Mangoldt Gamma Main Term Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Convert the verified vertical Gamma phase estimate into the exact normalized Riemann-von Mangoldt main term and a constant-free two-height estimate.

**Architecture:** A focused Riemann-von Mangoldt module defines the standard scalar main term, proves its exact relation to `HardyTheorem.thetaModel`, rescales the existing phase theorem by `pi`, and subtracts two heights to cancel the unknown phase constant. Contracts fix both public estimates and an axiom audit fixes the trust boundary.

**Tech Stack:** Lean 4, Mathlib real analysis, existing `HardyTheorem.VerticalGammaAsymptotic`, Lake focused builds.

## Global Constraints

- Do not claim an exact count/phase identity or an `O(log T)` zeta boundary estimate.
- Do not evaluate the holomorphic Gamma summand around a closed positive-height rectangle as a nonzero main term.
- Add no `sorry`, `admit`, `axiom`, or unproved `Prop` target.
- Use `lake -Kjobs=1 build ...` for focused verification.
- Axiom audits may list only `propext`, `Classical.choice`, and `Quot.sound`.

---

### Task 1: Normalized One-Height Gamma Main Term

**Files:**
- Create: `Test/RiemannVonMangoldtGammaMainTermContract.lean`
- Create: `PrimeNumberTheorem/RiemannVonMangoldt/GammaMainTerm.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes: `HardyTheorem.thetaModel` and `HardyTheorem.exists_verticalGammaUnwrappedPhase_sub_thetaModel_tendsto_const_inv`.
- Produces: `riemannVonMangoldtMainTerm`, `thetaModel_div_pi_eq_riemannVonMangoldtMainTerm_sub_eighth`, and `exists_verticalGammaPhase_div_pi_sub_mainTerm_tendsto_const_inv`.

- [ ] **Step 1: Add a failing contract and Lake roots**

The contract states the definition equation, the exact `thetaModel / pi`
normalization, and

```lean
example : ∃ kappa C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
    |HardyTheorem.verticalGammaUnwrappedPhase T / Real.pi -
        riemannVonMangoldtMainTerm T - kappa| ≤ C / T :=
  exists_verticalGammaPhase_div_pi_sub_mainTerm_tendsto_const_inv
```

Register the source and contract roots, then run
`lake -Kjobs=1 build Test.RiemannVonMangoldtGammaMainTermContract`.
Expected: failure because the source module does not exist.

- [ ] **Step 2: Implement the standard main term and exact normalization**

Define

```lean
noncomputable def riemannVonMangoldtMainTerm (T : ℝ) : ℝ :=
  T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) -
    T / (2 * Real.pi)
```

Expand this definition and `HardyTheorem.thetaModel`, use
`Real.pi_ne_zero`, and close the exact normalization by field algebra.

- [ ] **Step 3: Rescale the existing phase estimate**

Obtain `kappa`, `C`, and the existing error estimate. Choose the new constant
`kappa / pi - 1 / 8` and new bound `C / pi`. Rewrite the expression under the
absolute value as

```text
(verticalGammaUnwrappedPhase T - thetaModel T - kappa) / pi
```

and use `abs_div`, `abs_of_pos Real.pi_pos`, and division monotonicity.

- [ ] **Step 4: Run GREEN checks and commit**

```bash
lake -Kjobs=1 build PrimeNumberTheorem.RiemannVonMangoldt.GammaMainTerm
lake -Kjobs=1 build Test.RiemannVonMangoldtGammaMainTermContract
git add lakefile.lean PrimeNumberTheorem/RiemannVonMangoldt/GammaMainTerm.lean Test/RiemannVonMangoldtGammaMainTermContract.lean
git commit -m "feat(zeta): normalize Riemann-von Mangoldt Gamma main term"
```

### Task 2: Constant-Free Two-Height Estimate and Audit

**Files:**
- Modify: `Test/RiemannVonMangoldtGammaMainTermContract.lean`
- Modify: `PrimeNumberTheorem/RiemannVonMangoldt/GammaMainTerm.lean`
- Create: `Test/RiemannVonMangoldtGammaMainTermAxiomAudit.lean`
- Modify: `PrimeNumberTheorem/RiemannVonMangoldt.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes: `exists_verticalGammaPhase_div_pi_sub_mainTerm_tendsto_const_inv`.
- Produces: `exists_verticalGammaPhase_difference_sub_mainTerm_difference_le_inv_sum`.

- [ ] **Step 1: Add the failing two-height contract**

```lean
example : ∃ C : ℝ, 0 ≤ C ∧ ∀ U T : ℝ, 1 ≤ U → 1 ≤ T →
    |(HardyTheorem.verticalGammaUnwrappedPhase T -
          HardyTheorem.verticalGammaUnwrappedPhase U) / Real.pi -
        (riemannVonMangoldtMainTerm T - riemannVonMangoldtMainTerm U)| ≤
      C / U + C / T :=
  exists_verticalGammaPhase_difference_sub_mainTerm_difference_le_inv_sum
```

Run the contract and expect an unknown-identifier failure.

- [ ] **Step 2: Prove the difference estimate**

Subtract the normalized one-height expressions at `T` and `U`, rewrite the
left side as the difference of their errors, apply `abs_sub`, and combine the
two `C / height` bounds. No new analytic estimate is introduced.

- [ ] **Step 3: Add aggregate import and axiom audit**

Import `GammaMainTerm` from `PrimeNumberTheorem/RiemannVonMangoldt.lean`. The
audit prints axioms for the exact normalization, one-height estimate, and
two-height estimate. Register the audit root.

- [ ] **Step 4: Verify and commit**

```bash
lake -Kjobs=1 build Test.RiemannVonMangoldtGammaMainTermContract
lake -Kjobs=1 build Test.RiemannVonMangoldtGammaMainTermAxiomAudit
lake -Kjobs=1 build PrimeNumberTheorem.RiemannVonMangoldt
rg -n '\b(sorry|admit|axiom)\b' PrimeNumberTheorem/RiemannVonMangoldt/GammaMainTerm.lean Test/RiemannVonMangoldtGammaMainTermContract.lean Test/RiemannVonMangoldtGammaMainTermAxiomAudit.lean
git diff --check
git add lakefile.lean PrimeNumberTheorem/RiemannVonMangoldt.lean PrimeNumberTheorem/RiemannVonMangoldt/GammaMainTerm.lean Test/RiemannVonMangoldtGammaMainTermContract.lean Test/RiemannVonMangoldtGammaMainTermAxiomAudit.lean
git commit -m "feat(zeta): bound Gamma phase differences by the main term"
```
