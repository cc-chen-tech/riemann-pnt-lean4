# Actual Zero-Package Quantitative Energy Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Choose a positive smoothing window whose actual zero-package energy exceeds any strict target below its diagonal energy.

**Architecture:** Reuse the existing diagonal/off-diagonal decomposition and replace the positivity gap `D` by `D - d`.

**Tech Stack:** Lean 4, Mathlib ordered-field arithmetic, existing finite package energy definitions.

## Global Constraints

- Add only the quantitative-energy module, contract, audit, and task docs.
- Do not introduce any new zero or phase assumptions.
- Keep the theorem independent of Carlson transfer details.

---

### Task 1: Quantitative window selection

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualZeroPackageQuantitativeEnergy.lean`

**Interfaces:**
- Consumes: `actualEqualRealPartZeroPackageEnergy` and its diagonal/off-diagonal decomposition.
- Produces: `exists_actualEqualRealPartZeroPackageEnergy_gt` and the diagonal-half corollary.

- [ ] **Step 1:** define local abbreviations `D`, `B`, `gap`, and `L`.
- [ ] **Step 2:** prove `B / L < D - d` from `d < D`.
- [ ] **Step 3:** rewrite the energy and conclude `d < energy`.
- [ ] **Step 4:** instantiate `d = D / 2` under `0 < D`.

### Task 2: Contract and audit

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualZeroPackageQuantitativeEnergyContract.lean`
- Create: `Test/ZeroDensityLayerBudgetActualZeroPackageQuantitativeEnergyAxiomAudit.lean`

**Interfaces:**
- Consumes: Task 1 declarations.
- Produces: public type checks and axiom reports.

- [ ] **Step 1:** compile the main module with the local olean overlay.
- [ ] **Step 2:** compile contract and audit serially.
- [ ] **Step 3:** commit docs separately from Lean code and publish a bounded draft PR based on stack95.
