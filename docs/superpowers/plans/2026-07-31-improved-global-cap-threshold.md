# Improved Global Cap Threshold Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove the exact improved real-part cap threshold enabled by global sigma optimization.

**Architecture:** Express optimizer feasibility through a strictly decreasing balance map. Evaluate the contour boundary at the old canonical density threshold, then prove an exact iff between positive global contour gap and the new cap bound.

**Tech Stack:** Lean 4, strict real inequalities, globally optimized two-height Carlson ceiling.

## Global Constraints

- Modify only `ZeroDensityLayerBudget*.lean` and task design/plan files.
- Do not modify `ZeroForcedOscillationComplementaryBound.lean`.
- Do not modify VK-edge or sharp-oscillation files.
- State the result as an improvement internal to the formalized Carlson model.

---

### Task 1: Balance map and improved threshold

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightImprovedGlobalCapThreshold.lean`

**Interfaces:**
- Consumes: the unique optimizer and global ceiling.
- Produces: `jointTwoHeightSigmaBalanceValue`, its strict antitonicity, and `jointTwoHeightImprovedGlobalCapThreshold`.

- [ ] **Step 1: define the balance value**

- [ ] **Step 2: prove strict decrease**

- [ ] **Step 3: define the new cap threshold at the canonical density point**

- [ ] **Step 4: prove old threshold < new threshold < beta**

### Task 2: Exact contour-gap criterion

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightImprovedGlobalCapThreshold.lean`

**Interfaces:**
- Produces: `contourFloor_lt_jointTwoHeightGlobalOuterExponentCeiling_iff`.

- [ ] **Step 1: rewrite the global ceiling at the optimizer**

- [ ] **Step 2: convert the contour condition to `sigmaOpt < canonicalThreshold`**

- [ ] **Step 3: compare balance values and derive the exact theta criterion**

- [ ] **Step 4: construct a positive eta from every positive contour gap**

### Task 3: Contract, audit, and publication

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightImprovedGlobalCapThresholdContract.lean`
- Create: `Test/ZeroDensityLayerBudgetJointTwoHeightImprovedGlobalCapThresholdAxiomAudit.lean`

**Interfaces:**
- Consumes: the improved threshold theorem chain.
- Produces: focused declaration and axiom evidence.

- [ ] **Step 1: compile implementation and contract directly**

- [ ] **Step 2: audit threshold strictness, exact iff, and eta existence**

- [ ] **Step 3: commit docs and code separately**

- [ ] **Step 4: push and create a draft PR based on stack61**
