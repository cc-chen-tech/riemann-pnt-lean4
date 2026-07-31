# Actual Zero-Package Automatic Energy-Boundary Budget Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Construct an actual height package and smoothing window whose positive energy automatically dominates its Carlson boundary tail.

**Architecture:** Anchor the comparison at half the positive diagonal energy of an initial seed-containing package, shrink the boundary tail using stack97, use diagonal monotonicity, and then retain the anchor with stack96.

**Tech Stack:** Lean 4, finite sums, real square roots, actual zeta package energy, Carlson boundary capture.

## Global Constraints

- Add only the automatic energy-boundary budget module, contract, audit, and docs.
- Keep nonempty seed and global right-edge cap explicit.
- Do not compose with the PNT oscillation facade in this PR.

---

### Task 1: Diagonal-energy monotonicity

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualZeroPackageAutomaticEnergyBoundaryBudget.lean`

**Interfaces:**
- Consumes: inclusion between two equal-real-part packages.
- Produces: `actualEqualRealPartZeroPackageDiagonalEnergy_mono_of_subset`.

- [ ] **Step 1:** unfold diagonal energy as a nonnegative finite sum.
- [ ] **Step 2:** apply finite-sum monotonicity under subset inclusion.

### Task 2: Automatic non-circular budget

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualZeroPackageAutomaticEnergyBoundaryBudgetContract.lean`
- Create: `Test/ZeroDensityLayerBudgetActualZeroPackageAutomaticEnergyBoundaryBudgetAxiomAudit.lean`

**Interfaces:**
- Consumes: Task 1, stack96 quantitative energy, and stack97 finite-height capture.
- Produces: `exists_actualZeroPackage_energy_boundaryBudget`.

- [ ] **Step 1:** form a nonempty initial package containing the seed.
- [ ] **Step 2:** fix the positive anchor at half its diagonal energy.
- [ ] **Step 3:** capture the boundary below `q * sqrt(anchor) / 2`.
- [ ] **Step 4:** choose a window whose package energy exceeds the anchor.
- [ ] **Step 5:** compare square roots and conclude the automatic budget.
- [ ] **Step 6:** compile main, contract, and audit serially.
- [ ] **Step 7:** commit docs and Lean code separately and publish a draft PR based on stack97.
