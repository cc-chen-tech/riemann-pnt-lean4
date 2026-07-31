# Positive Outside-Cluster Cap Transfer Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the overly strong global positive-zero cap in the automatic actual transfer by a cap only on zeros outside the distinguished cluster.

**Architecture:** Define a minimal positive outside-cluster cap, prove it is preserved when the real-ordinate zero slice is adjoined, and reuse the existing automatic two-height actual PNT transfer with the lifted cap.

**Tech Stack:** Lean 4, automatic good-height transfer, actual Carlson two-height decomposition, explicit-formula PNT error.

## Global Constraints

- Create only `ZeroDensityLayerBudgetActualPositiveOutsideClusterCapUnifiedTransfer*.lean`, its audit, and task documentation.
- Do not modify `ZeroForcedOscillationComplementaryBound.lean`.
- Do not modify VK-edge or sharp-oscillation files.
- Keep the visible-cluster witness explicit.

---

### Task 1: Minimal cap interface

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualPositiveOutsideClusterCapUnifiedTransfer.lean`

**Interfaces:**
- Produces: `PositiveOutsideClusterRealPartCap`, global-cap specialization, cluster monotonicity, and adjoin preservation.

- [x] **Step 1: define the positive outside-cluster cap**

- [x] **Step 2: prove every global positive-zero cap specializes to it**

- [x] **Step 3: prove cluster enlargement and real-ordinate adjoin preserve it**

### Task 2: Automatic actual transfer

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualPositiveOutsideClusterCapUnifiedTransfer.lean`

**Interfaces:**
- Consumes: `PositiveOutsideClusterRealPartCap S theta`.
- Produces: `exists_automaticGoodHeight_positiveOutsideClusterRealPartCapNaturalTargetTransfer`.

- [x] **Step 1: select the automatic two-height parameters**

- [x] **Step 2: close the positive selected-height strip from the lifted cap**

- [x] **Step 3: close the real-ordinate residual by adjoin**

- [x] **Step 4: run the actual bidirectional PNT transfer**

### Task 3: Contract, audit, and publication

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualPositiveOutsideClusterCapUnifiedTransferContract.lean`
- Create: `Test/ZeroDensityLayerBudgetActualPositiveOutsideClusterCapUnifiedTransferAxiomAudit.lean`

- [x] **Step 1: compile implementation and contract directly**

- [x] **Step 2: run the focused axiom audit**

- [x] **Step 3: commit documentation and code separately**

- [x] **Step 4: push and create a draft PR based on stack75**
