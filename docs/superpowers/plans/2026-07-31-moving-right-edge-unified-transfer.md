# Moving Right-Edge Unified Transfer Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Derive an actual half-target-amplitude PNT witness from a moving right-edge cluster witness with fully automatic two-height parameters and no zero cap.

**Architecture:** Combine the exact moving-cluster explicit-formula split with closed-axis, selected-height remainder, and moving-complement negligibility. Then invoke the existing two-height selector at anchor `1 / 2`.

**Tech Stack:** Lean 4, moving Carlson complement majorant, selected uniform good heights, actual multiplicity-aware explicit formula.

## Global Constraints

- Create only `ZeroDensityLayerBudgetActualMovingRightEdgeUnifiedTransfer*.lean`, its audit, and task documentation.
- Do not modify `ZeroForcedOscillationComplementaryBound.lean`.
- Do not modify VK-edge or sharp-oscillation files.
- Keep the moving visible-cluster witness explicit.

---

### Task 1: Fixed-parameter lower transfer

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingRightEdgeUnifiedTransfer.lean`

**Interfaces:**
- Produces: `automaticGoodHeight_twoHeight_movingRightEdgeNaturalPointLowerTransfer` and `unified_automaticGoodHeight_twoHeight_movingRightEdgeNaturalTargetTransfer`.

- [x] **Step 1: obtain selected-height nonnegative and polynomial-envelope bounds**

- [x] **Step 2: instantiate moving complement negligibility**

- [x] **Step 3: combine the three residuals with the exact moving formula**

- [x] **Step 4: add fixed-rate actual PNT convergence**

### Task 2: Fully automatic parameter selection

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingRightEdgeUnifiedTransfer.lean`

**Interfaces:**
- Produces: `exists_automaticGoodHeight_movingRightEdgeNaturalTargetTransfer`.

- [x] **Step 1: prove the anchor `1 / 2` is feasible from `2 / 3 < beta`**

- [x] **Step 2: select all two-height and contour parameters**

- [x] **Step 3: return the moving unified transfer for every good-height selection**

### Task 3: Contract, audit, and publication

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingRightEdgeUnifiedTransferContract.lean`
- Create: `Test/ZeroDensityLayerBudgetActualMovingRightEdgeUnifiedTransferAxiomAudit.lean`

- [x] **Step 1: compile implementation and contract directly**

- [x] **Step 2: run the focused axiom audit**

- [ ] **Step 3: commit documentation and code separately**

- [ ] **Step 4: push and create a draft PR based on stack79**
