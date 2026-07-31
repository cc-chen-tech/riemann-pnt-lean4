# Joint-Slope Full-Transfer Obstruction Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove that multiple polynomial-height costs combine through their maximum slope and show why Carlson's subunit density slope alone cannot improve the current full PNT transfer threshold.

**Architecture:** A focused arithmetic module lifts Stack147 from one slope to two, specializes the maximum to Carlson plus the unit low-kernel cost, and supplies a strict positive-parameter counterexample to the invalid converse implication. Contract and axiom-audit modules lock the result.

**Tech Stack:** Lean 4, Mathlib ordered-field arithmetic, Stack147 weighted optimizer, Stack148 Carlson slope.

## Global Constraints

- Modify only `ZeroDensityLayerBudgetJointSlopeOptimalPolynomialHeightWindow*.lean` and this stack's spec/plan files.
- Do not add a sigma-only PNT facade unless the exact full-transfer margin is proved.
- Do not modify protected complementary-zero, Sharp/localized-pi-over-two, or VK-edge modules.
- Do not claim a new Carlson estimate, RH, or an unconditional Omega theorem.
- Compile serially with `nice -n 10` and the existing overlay.

---

### Task 1: Prove the effective-maximum slope theorem

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointSlopeOptimalPolynomialHeightWindow.lean`
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointSlopeOptimalPolynomialHeightWindowContract.lean`

**Interfaces:**
- Consumes: Stack147 weighted optimizer definitions and minimax theorem.
- Produces: `jointPolynomialHeightConstraints_iff_effectiveSlope`, `jointPolynomialHeightCommonSafetyMargin_le_optimal`, and `jointOptimalPolynomialHeightWindow_equalMargins`.

- [ ] **Step 1: Define the effective slope as `max q k` and alias the weighted optimizer parameters.**

- [ ] **Step 2: Prove the conjunction of two budgets is equivalent to the maximum-slope budget for nonnegative outer exponent.**

- [ ] **Step 3: Reuse Stack147 to prove the joint minimax upper bound and equal-margin attainment.**

### Task 2: Specialize to Carlson plus the low-kernel cost

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointSlopeOptimalPolynomialHeightWindow.lean`

**Interfaces:**
- Consumes: `carlsonPolynomialDensitySlope` and the existing unit-slope optimizer.
- Produces: `carlsonFullTransferEffectiveSlope_eq_one`, `carlsonFullTransferJointOptimizer_eq_unweighted`, and both margin implication theorems.

- [ ] **Step 1: Prove Carlson's slope is strictly below one for `1/2 < sigma < 1`.**

- [ ] **Step 2: Prove the joint effective slope equals one and recover all four unweighted optimizer parameters.**

- [ ] **Step 3: Prove the full-transfer margin implies the Carlson-density margin.**

- [ ] **Step 4: Construct positive `outer` and `epsilon` where the Carlson-density margin holds but the full-transfer margin fails.**

### Task 3: Verify, audit, and publish Stack149

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointSlopeOptimalPolynomialHeightWindowAxiomAudit.lean`
- Create: `docs/superpowers/specs/2026-08-01-joint-slope-full-transfer-obstruction-design.md`
- Create: `docs/superpowers/plans/2026-08-01-joint-slope-full-transfer-obstruction.md`

**Interfaces:**
- Consumes: all public Stack149 theorems.
- Produces: an audited obstruction theorem and a bounded stacked draft PR based on Stack148.

- [ ] **Step 1: Compile implementation, contract, and audit serially through the overlay.**

Expected: all commands exit zero without warnings.

- [ ] **Step 2: Confirm every audited theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.**

- [ ] **Step 3: Commit docs and Lean files separately, push, and create a draft PR based on Stack148.**
