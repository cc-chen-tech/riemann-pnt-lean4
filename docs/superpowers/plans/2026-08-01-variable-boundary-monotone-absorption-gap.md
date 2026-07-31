# Variable-Boundary Monotone Absorption-or-Gap Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Derive absorption-or-gap and visible Carlson-tail decay automatically from a cofinal height and monotone pointwise right edge.

**Architecture:** Analyze each fixed indexed zero after it becomes permanently visible, split on whether the monotone boundary ever moves strictly right, and feed the resulting dichotomy into stack101.

**Tech Stack:** Lean 4, Mathlib filters and monotone sequences, actual zeta package membership, stack101 dominated tail.

## Global Constraints

- Add only the monotone absorption-gap module, contract, audit, and docs.
- Do not construct or modify the protected finite-height maximum-real-part module.
- Do not claim a complete PNT residual theorem or RH.

---

### Task 1: Fixed-zero dichotomy

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetVariableBoundaryMonotoneAbsorptionGap.lean`

**Interfaces:**
- Consumes: cofinality of `H`, monotonicity of `beta` on natural samples, and the indexed visible right edge.
- Produces: `variableBoundaryAbsorptionOrGap_of_monotone`.

- [ ] **Step 1:** obtain eventual visibility of a fixed zero.
- [ ] **Step 2:** split on the existence of a later strict boundary crossing.
- [ ] **Step 3:** construct a permanent half-gap in the crossing branch.
- [ ] **Step 4:** prove package absorption in the no-crossing branch.

### Task 2: Automatic tail consequence

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetVariableBoundaryMonotoneAbsorptionGapContract.lean`
- Create: `Test/ZeroDensityLayerBudgetVariableBoundaryMonotoneAbsorptionGapAxiomAudit.lean`

**Interfaces:**
- Produces: `variableBoundaryVisibleNormalizedKernelTail_tendsto_zero_of_monotone`.

- [ ] **Step 1:** instantiate stack101 with the automatic absorption-or-gap theorem.
- [ ] **Step 2:** compile main, contract, and audit serially.
- [ ] **Step 3:** commit docs and Lean code separately and publish a draft PR based on stack101.
