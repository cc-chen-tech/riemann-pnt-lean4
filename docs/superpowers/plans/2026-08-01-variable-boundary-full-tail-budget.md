# Variable-Boundary Full-Tail Budget Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Derive the complete moving signed-complement decay from the correct two-sided positive-tail cost, a low-strip majorant, and a real-ordinate tail.

**Architecture:** Define moving positive and real normalized tails, prove the pointwise conjugation budget using existing full-tail inequalities, then squeeze against the sum of the low, visible, and real majorants. Reuse stack103 and stack100 for the final exact explicit-formula residual.

**Tech Stack:** Lean 4, Mathlib filters, stack100 variable explicit formula, stack101 visible tail, stack103 amplitude domination, and existing actual full-tail conjugation inequalities.

## Global Constraints

- Modify only `ZeroDensityLayerBudget*.lean`, matching audits, and this task's documentation.
- Do not modify protected complementary-bound or VK-edge files.
- Preserve the factor `2` from conjugation and keep real ordinates explicit.
- Do not claim the remaining positive-tail indexing bridge, both oscillation signs, or RH.
- Run at most one Lean process at a time.

---

### Task 1: Pointwise full-tail budget

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetVariableBoundaryFullTailBudget.lean`

**Interfaces:**
- Consumes: existing signed-to-full-tail and full-to-two-positive-plus-real inequalities.
- Produces: moving positive/real normalized sums and `abs_variableBoundaryComplement_div_le_two_positive_add_real`.

- [ ] **Step 1:** Define the two moving normalized tail functions.
- [ ] **Step 2:** prove conjugation invariance of the pointwise variable boundary package by the existing equal-real-part theorem.
- [ ] **Step 3:** divide the chained tail inequality by the positive moving amplitude.

### Task 2: Decay and exact residual assembly

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetVariableBoundaryFullTailBudget.lean`

**Interfaces:**
- Consumes: positive-tail majorization, low decay, visible-tail decay, and real-tail decay.
- Produces: complete complement negligibility and exact variable-boundary residual negligibility.

- [ ] **Step 1:** define `VariableBoundaryVisiblePositiveTailMajorized`.
- [ ] **Step 2:** squeeze the signed complement below the convergent combined majorant.
- [ ] **Step 3:** promote fixed analytic terms through stack103.
- [ ] **Step 4:** rewrite with stack100's exact decomposition.

### Task 3: Contract, audit, and publication

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetVariableBoundaryFullTailBudgetContract.lean`
- Create: `Test/ZeroDensityLayerBudgetVariableBoundaryFullTailBudgetAxiomAudit.lean`

**Interfaces:**
- Consumes: stack105 declarations.
- Produces: signature and axiom audits.

- [ ] **Step 1:** add focused `#check` and `#print axioms` declarations.
- [ ] **Step 2:** compile implementation, contract, and audit sequentially.
- [ ] **Step 3:** commit exact paths and publish a stacked Draft PR based on stack104.
