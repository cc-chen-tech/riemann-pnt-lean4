# Variable-Boundary Visible Carlson Tail Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove dominated-convergence decay of the currently visible Carlson high-zero tail normalized at a moving boundary exponent.

**Architecture:** Delete invisible and package-member zeros, establish pointwise decay from absorption-or-gap, dominate visible terms by Carlson weights using the pointwise right edge, and identify the weighted model with actual normalized zeta kernels.

**Tech Stack:** Lean 4, Mathlib filters and infinite sums, Carlson summability, Pintz kernel normalization.

## Global Constraints

- Add only the variable-boundary visible-tail module, contract, audit, and docs.
- Never apply the current boundary to invisible zeros.
- Keep absorption-or-gap explicit in this PR.
- Do not claim a complete PNT residual theorem or RH.

---

### Task 1: Visible weighted model

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetVariableBoundaryVisibleCarlsonTail.lean`

**Interfaces:**
- Produces: the indexed visible-right-edge predicate, absorption-or-gap predicate, visible weighted term, nonnegativity, pointwise decay, and summable domination.

- [ ] **Step 1:** define the two structural predicates and visible term.
- [ ] **Step 2:** prove term nonnegativity.
- [ ] **Step 3:** bound each fixed term by a decaying `m^(-delta)` majorant.
- [ ] **Step 4:** bound all visible terms by the Carlson summable weight.
- [ ] **Step 5:** apply dominated convergence to the weighted tail.

### Task 2: Actual zeta-kernel identification

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetVariableBoundaryVisibleCarlsonTailContract.lean`
- Create: `Test/ZeroDensityLayerBudgetVariableBoundaryVisibleCarlsonTailAxiomAudit.lean`

**Interfaces:**
- Produces: `variableBoundaryVisibleNormalizedKernelTail` and its convergence theorem.

- [ ] **Step 1:** define the actual visible normalized kernel tail.
- [ ] **Step 2:** prove termwise equality with the weighted model at positive natural scales.
- [ ] **Step 3:** transfer convergence and compile contract/audit.
- [ ] **Step 4:** commit docs and Lean code separately and publish a draft PR based on stack100.
