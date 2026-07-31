# Moving Right-Edge Exceptional Cluster Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Define the scale-dependent right-edge exceptional zero cluster and prove its automatic local cap and exact actual explicit-formula decomposition.

**Architecture:** At each height, take the finite right-edge zero finset and adjoin the fixed real-ordinate zero slice. Reuse existing membership, conjugation, and explicit-formula identities pointwise.

**Tech Stack:** Lean 4, finite nontrivial-zero sets, actual explicit formula, moving truncation heights.

## Global Constraints

- Create only `ZeroDensityLayerBudgetActualMovingRightEdgeExceptionalCluster*.lean`, its audit, and task documentation.
- Do not modify `ZeroForcedOscillationComplementaryBound.lean`.
- Do not modify VK-edge or sharp-oscillation files.
- Do not claim moving-complement negligibility in this module.

---

### Task 1: Moving cluster geometry

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingRightEdgeExceptionalCluster.lean`

**Interfaces:**
- Produces: moving cap predicate, moving right-edge cluster, height monotonicity, conjugation invariance, real-ordinate capture, and automatic strict outside cap.

- [x] **Step 1: define the moving positive outside-cluster cap**

- [x] **Step 2: define the moving right-edge exceptional cluster**

- [x] **Step 3: prove height monotonicity and pointwise conjugation invariance**

- [x] **Step 4: prove real-ordinate capture and automatic strict outside cap**

### Task 2: Exact moving explicit formula

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingRightEdgeExceptionalCluster.lean`

**Interfaces:**
- Produces: moving visible main, moving signed complement, and `relativeChebyshevPsi0Error_eq_movingRightEdgeCluster_add_actualResiduals`.

- [x] **Step 1: define the moving main and complement**

- [x] **Step 2: specialize the existing pointwise cluster decomposition**

### Task 3: Contract, audit, and publication

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingRightEdgeExceptionalClusterContract.lean`
- Create: `Test/ZeroDensityLayerBudgetActualMovingRightEdgeExceptionalClusterAxiomAudit.lean`

- [x] **Step 1: compile implementation and contract directly**

- [x] **Step 2: run the focused axiom audit**

- [x] **Step 3: commit documentation and code separately**

- [x] **Step 4: push and create a draft PR based on stack77**
