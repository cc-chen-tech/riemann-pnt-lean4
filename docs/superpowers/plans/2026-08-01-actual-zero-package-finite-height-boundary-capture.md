# Actual Zero-Package Finite-Height Boundary Capture Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Produce an actual finite-height equal-real-part package with arbitrarily small Carlson outside-boundary mass.

**Architecture:** First bound all ordinates of a finite target-line seed by their finite absolute-ordinate sum. Then invoke the existing target-line Carlson selector and enlarge its output to the corresponding height package using boundary-mass antitonicity.

**Tech Stack:** Lean 4, Mathlib finite sums, existing actual zeta package and Carlson boundary capture interfaces.

## Global Constraints

- Add only the finite-height capture module, contract, audit, and docs.
- Retain the global outside real-part cap as an explicit hypothesis.
- Do not make any energy or oscillation claim in this PR.

---

### Task 1: Finite seed height containment

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualZeroPackageFiniteHeightBoundaryCapture.lean`

**Interfaces:**
- Consumes: `IsTargetRealPartNontrivialZeroSeed` and `mem_equalRealPartZeroPackage`.
- Produces: `exists_height_targetLineSeed_subset_equalRealPartZeroPackage`.

- [ ] **Step 1:** choose the sum of absolute ordinates as height.
- [ ] **Step 2:** prove nonnegativity and pointwise ordinate bounds.
- [ ] **Step 3:** prove package membership for every seed element.

### Task 2: Actual package boundary capture

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualZeroPackageFiniteHeightBoundaryCaptureContract.lean`
- Create: `Test/ZeroDensityLayerBudgetActualZeroPackageFiniteHeightBoundaryCaptureAxiomAudit.lean`

**Interfaces:**
- Consumes: Task 1, target-line finite-seed selector, and boundary-mass antitonicity.
- Produces: `exists_actualZeroPackage_boundaryMass_lt` plus its contract and audit.

- [ ] **Step 1:** obtain a target-line extension with mass below `epsilon`.
- [ ] **Step 2:** embed it into one height package.
- [ ] **Step 3:** transfer the real-part cap and boundary estimate.
- [ ] **Step 4:** compile main, contract, and audit serially.
- [ ] **Step 5:** commit docs and Lean code separately and publish a draft PR based on stack96.
