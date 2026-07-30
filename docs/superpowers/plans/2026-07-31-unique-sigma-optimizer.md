# Unique Sigma Optimizer Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove that the balancing density threshold from stack57 is unique.

**Architecture:** Add a strict arithmetic layer above the exact optimizer module. Prove strict antitonicity of the density exponent and balanced slope, compare the balance products at two ordered thresholds, and combine at-most-one with the existing IVT existence theorem.

**Tech Stack:** Lean 4, strict real inequalities, Carlson balanced slope.

## Global Constraints

- Modify only `ZeroDensityLayerBudget*.lean` and task design/plan files.
- Do not modify `ZeroForcedOscillationComplementaryBound.lean`.
- Do not modify VK-edge or sharp-oscillation files.
- Do not claim a closed-form optimizer.

---

### Task 1: Strict slope arithmetic

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightUniqueSigmaOptimizer.lean`

**Interfaces:**
- Consumes: stack57's density exponent and balanced slope.
- Produces: `carlsonTwoHeightDensityExponent_strictAntiOn_half` and `targetAmplitudeCarlsonTwoHeightBalancedSlope_strictAntiOn_half_one`.

- [ ] **Step 1: Prove strict decrease of the quadratic density exponent**

- [ ] **Step 2: Cross multiply the balanced rational slopes**

### Task 2: Optimizer uniqueness

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightUniqueSigmaOptimizer.lean`

**Interfaces:**
- Produces: `IsJointTwoHeightSigmaOptimizer.unique` and `existsUnique_jointTwoHeightSigmaOptimizer`.

- [ ] **Step 1: Split unequal thresholds by order**

- [ ] **Step 2: Prove the balance product strictly decreases**

- [ ] **Step 3: Contradict the two balance equations**

- [ ] **Step 4: Combine with stack57 existence**

### Task 3: Contract, audit, and publication

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightUniqueSigmaOptimizerContract.lean`
- Create: `Test/ZeroDensityLayerBudgetJointTwoHeightUniqueSigmaOptimizerAxiomAudit.lean`

**Interfaces:**
- Consumes: strict monotonicity and uniqueness.
- Produces: focused API and axiom evidence.

- [ ] **Step 1: Add declaration checks and axiom prints**

- [ ] **Step 2: Compile implementation, contract, and audit directly**

- [ ] **Step 3: Commit docs and code separately**

- [ ] **Step 4: Push and create a draft PR based on stack57**
