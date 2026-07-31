# Variable-Boundary Visible Residual Assembly Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Produce the complete moving-target normalized explicit-formula residual from the visible Carlson tail and reusable fixed-exponent analytic remainders.

**Architecture:** Name the exact pointwise majorization bridge between the signed finite complement and the nonnegative visible tail. Use squeeze convergence for the complement, stack103 denominator domination for fixed analytic terms, and stack100's exact decomposition for final assembly.

**Tech Stack:** Lean 4, Mathlib filters, the stack100 variable-boundary decomposition, stack101 visible Carlson tail, and stack103 amplitude domination.

## Global Constraints

- Modify only `ZeroDensityLayerBudget*.lean`, matching audits, and this task's documentation.
- Do not modify the protected complementary-bound or VK-edge modules.
- Keep the finite-sum/indexing majorization as an explicit hypothesis until separately proved.
- Do not claim a moving-package witness, unconditional `Omega_+-`, or RH.
- Run at most one Lean process at a time.

---

### Task 1: Visible complement majorization transfer

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetVariableBoundaryVisibleResidualAssembly.lean`

**Interfaces:**
- Consumes: `variableBoundaryVisibleNormalizedKernelTail_tendsto_zero` and eventual pointwise majorization.
- Produces: `VariableBoundaryVisibleComplementMajorized` and `variableBoundaryVisibleComplement_targetAmplitudeNegligible`.

- [ ] **Step 1:** Define the eventual normalized absolute-value majorization proposition.
- [ ] **Step 2:** Establish nonnegativity of the normalized complement from eventual target-amplitude positivity.
- [ ] **Step 3:** Apply order convergence using the visible-tail upper bound.

### Task 2: Exact moving residual assembly

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetVariableBoundaryVisibleResidualAssembly.lean`

**Interfaces:**
- Consumes: eventual `beta0 <= beta(m)`, a fixed-`beta0` contour certificate, and the visible-complement majorization transfer.
- Produces: `actualVariableBoundaryExplicitFormulaResidual_targetAmplitudeNegligible`.

- [ ] **Step 1:** Promote the closed real-axis estimate through stack103.
- [ ] **Step 2:** Promote the fixed-exponent contour certificate through stack103.
- [ ] **Step 3:** Add both analytic terms to the moving complement estimate.
- [ ] **Step 4:** Rewrite with stack100's exact explicit-formula decomposition.

### Task 3: Contract, audit, and publication

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetVariableBoundaryVisibleResidualAssemblyContract.lean`
- Create: `Test/ZeroDensityLayerBudgetVariableBoundaryVisibleResidualAssemblyAxiomAudit.lean`

**Interfaces:**
- Consumes: the stack104 public declarations.
- Produces: signature checks and axiom reports.

- [ ] **Step 1:** Add focused `#check` declarations.
- [ ] **Step 2:** Add focused `#print axioms` declarations.
- [ ] **Step 3:** Compile all three targets sequentially with the overlay.
- [ ] **Step 4:** Commit exact task paths and publish a stacked Draft PR based on stack103.
