# Unique Optimal Target Exponent Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Construct the unique inverse target exponent for every prescribed cap in `(1 / 2, 1)`.

**Architecture:** Use a denominator-cleared polynomial for existence by IVT, strict threshold monotonicity for uniqueness, and a regime-guarded classical choice for the canonical interface.

**Tech Stack:** Lean 4, real polynomial continuity, intermediate value theorem, strict monotonicity.

## Global Constraints

- Modify only `ZeroDensityLayerBudget*.lean` and task design/plan files.
- Do not modify `ZeroForcedOscillationComplementaryBound.lean`.
- Do not modify VK-edge or sharp-oscillation files.

---

### Task 1: Inverse existence

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightUniqueOptimalTargetExponent.lean`

**Interfaces:**
- Produces: the inverse polynomial, optimizer predicate, and existence theorem.

- [ ] **Step 1: define the denominator-cleared polynomial**

- [ ] **Step 2: prove continuity and endpoint signs**

- [ ] **Step 3: apply IVT and exclude endpoints**

- [ ] **Step 4: recover the threshold equation**

### Task 2: Uniqueness and canonical choice

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightUniqueOptimalTargetExponent.lean`

**Interfaces:**
- Produces: uniqueness, `ExistsUnique`, canonical inverse, and specification.

- [ ] **Step 1: contradict unequal inverse points by strict monotonicity**

- [ ] **Step 2: combine existence and uniqueness**

- [ ] **Step 3: define the canonical inverse and prove its specification**

### Task 3: Contract, audit, and publication

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightUniqueOptimalTargetExponentContract.lean`
- Create: `Test/ZeroDensityLayerBudgetJointTwoHeightUniqueOptimalTargetExponentAxiomAudit.lean`

- [ ] **Step 1: compile implementation and contract directly**

- [ ] **Step 2: run the focused axiom audit**

- [ ] **Step 3: commit docs and code separately**

- [ ] **Step 4: push and create a draft PR based on stack67**
