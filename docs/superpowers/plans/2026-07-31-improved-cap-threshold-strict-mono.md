# Improved Cap Threshold Strict Monotonicity Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove the improved cap threshold strictly increases from `1 / 2` to `1`.

**Architecture:** Use the explicit threshold formula from stack65. First prove strict decrease of the canonical density exponent, transfer it through the increasing rational slope, and then compare the positive deficit products.

**Tech Stack:** Lean 4, strict real inequalities, explicit Carlson threshold formulas.

## Global Constraints

- Modify only `ZeroDensityLayerBudget*.lean` and task design/plan files.
- Do not modify `ZeroForcedOscillationComplementaryBound.lean`.
- Do not modify VK-edge or sharp-oscillation files.

---

### Task 1: Strict monotonicity

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightImprovedCapThresholdStrictMono.lean`

**Interfaces:**
- Produces: strict decrease of the canonical density exponent and strict increase of the improved threshold.

- [ ] **Step 1: factor the density-exponent difference**

- [ ] **Step 2: compare the rational balanced slopes**

- [ ] **Step 3: prove strict decrease of the cap deficit**

- [ ] **Step 4: conclude strict increase of the threshold**

### Task 2: Endpoint and range theorems

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightImprovedCapThresholdStrictMono.lean`

**Interfaces:**
- Produces: endpoint values and interval membership.

- [ ] **Step 1: evaluate at `2 / 3`**

- [ ] **Step 2: evaluate at `1`**

- [ ] **Step 3: prove the open-interval range**

### Task 3: Contract, audit, and publication

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightImprovedCapThresholdStrictMonoContract.lean`
- Create: `Test/ZeroDensityLayerBudgetJointTwoHeightImprovedCapThresholdStrictMonoAxiomAudit.lean`

- [ ] **Step 1: compile implementation and contract directly**

- [ ] **Step 2: run the focused axiom audit**

- [ ] **Step 3: commit docs and code separately**

- [ ] **Step 4: push and create a draft PR based on stack66**
