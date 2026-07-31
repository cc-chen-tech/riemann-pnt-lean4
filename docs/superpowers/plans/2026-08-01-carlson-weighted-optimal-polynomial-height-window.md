# Carlson-Weighted Optimal Polynomial-Height Window Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Specialize the weighted polynomial-height optimizer to Carlson's exact classical density slope and expose its improved critical-real-part threshold.

**Architecture:** One focused Lean module names the Carlson slope, proves the exact feasibility equivalence and threshold comparison, then reuses Stack147 to construct the strict window and selected-height certificate. Independent contract and axiom-audit modules lock the public and logical boundaries.

**Tech Stack:** Lean 4, Mathlib ordered-field arithmetic, existing Carlson asymptotic exponent, Stack147 weighted optimizer.

## Global Constraints

- Modify only `ZeroDensityLayerBudgetCarlsonWeightedOptimalPolynomialHeightWindow*.lean` and this stack's spec/plan files.
- Do not modify protected complementary-zero, Sharp/localized-pi-over-two, or VK-edge modules.
- Reuse, but do not claim to strengthen, the formalized Carlson exponent `4 * sigma * (1 - sigma)`.
- Do not claim RH or an unconditional Omega theorem.
- Compile serially with `nice -n 10` and the existing overlay.

---

### Task 1: Prove the exact Carlson-weighted threshold

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetCarlsonWeightedOptimalPolynomialHeightWindow.lean`
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetCarlsonWeightedOptimalPolynomialHeightWindowContract.lean`

**Interfaces:**
- Consumes: `weightedPolynomialHeightFeasibilityGap` and Stack147's weighted optimizer definitions.
- Produces: `carlsonPolynomialDensitySlope`, `carlsonWeightedPolynomialCriticalRealPart`, and `carlsonWeightedPolynomialHeightFeasibilityGap_pos_iff`.

- [ ] **Step 1: Lock the slope, critical point, feasibility iff, and location theorem signatures in the contract.**

- [ ] **Step 2: Prove nonnegativity and positivity of `4 * sigma * (1 - sigma)` on the required ranges.**

- [ ] **Step 3: Prove the feasibility-gap iff by multiplying through the positive denominator.**

- [ ] **Step 4: Prove the critical point lies strictly between `sigma` and `1`.**

### Task 2: Quantify the improvement and install the selected height

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetCarlsonWeightedOptimalPolynomialHeightWindow.lean`

**Interfaces:**
- Consumes: `weightedOptimalPolynomialHeightWindow_spec` and `weightedOptimalPolynomialSelectedHeight_spec`.
- Produces: `carlsonWeightedPolynomialCriticalRealPart_lt_criticalHalf`, `carlsonWeightedOptimalPolynomialHeightWindow_spec`, and `carlsonWeightedOptimalPolynomialSelectedHeight_spec`.

- [ ] **Step 1: Derive `q(sigma) < 1` from the positive square `(2 sigma - 1)^2`.**

- [ ] **Step 2: Prove the exact critical quotient is below `(1 + sigma) / 2`.**

- [ ] **Step 3: Specialize the weighted strict-window theorem using the feasibility iff.**

- [ ] **Step 4: Specialize the selected-height growth and actual remainder certificate.**

### Task 3: Verify, audit, and publish Stack148

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetCarlsonWeightedOptimalPolynomialHeightWindowAxiomAudit.lean`
- Create: `docs/superpowers/specs/2026-08-01-carlson-weighted-optimal-polynomial-height-window-design.md`
- Create: `docs/superpowers/plans/2026-08-01-carlson-weighted-optimal-polynomial-height-window.md`

**Interfaces:**
- Consumes: all public Stack148 theorems.
- Produces: a direct axiom report and a bounded stacked draft PR based on Stack147.

- [ ] **Step 1: Compile implementation, contract, and audit serially through the overlay.**

Expected: all commands exit zero without warnings.

- [ ] **Step 2: Confirm every audited theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.**

- [ ] **Step 3: Commit docs and Lean files separately, push, and create a draft PR based on Stack147.**
