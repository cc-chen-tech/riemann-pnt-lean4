# Global Optimal Truncation Parameters Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Package the unique sigma optimizer as the global truncation ceiling and realize every strictly suboptimal exponent with full transfer margins.

**Architecture:** Add a canonical-choice layer above stack58 and compose it with stack54's strict-margin constructor. Keep the optimal-value proof and the realizability theorem separate so the open analytic constraints remain explicit.

**Tech Stack:** Lean 4, unique choice, optimized two-height Carlson parameters.

## Global Constraints

- Modify only `ZeroDensityLayerBudget*.lean` and task design/plan files.
- Do not modify `ZeroForcedOscillationComplementaryBound.lean`.
- Do not modify VK-edge or sharp-oscillation files.
- Preserve the strict loss `eta`; do not claim ceiling attainment.

---

### Task 1: Canonical optimizer and global ceiling

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightGlobalOptimalTruncationParameters.lean`

**Interfaces:**
- Consumes: `existsUnique_jointTwoHeightSigmaOptimizer`.
- Produces: `jointTwoHeightOptimalDensityThreshold`, its specification, and `jointTwoHeightGlobalOuterExponentCeiling`.

- [ ] **Step 1: Define the optimizer with a regime-guarded unique choice**

- [ ] **Step 2: Prove the optimizer specification**

- [ ] **Step 3: Define and rewrite the global ceiling**

- [ ] **Step 4: Prove every admissible fixed-sigma ceiling is bounded by it**

### Task 2: Globally near-optimal realization

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightGlobalOptimalTruncationParameters.lean`

**Interfaces:**
- Consumes: `exists_jointTwoHeightNearOptimalTruncationParameters`.
- Produces: `exists_jointTwoHeightGloballyNearOptimalTruncationParameters`.

- [ ] **Step 1: Fix sigma to the canonical optimizer**

- [ ] **Step 2: translate the global eta gap to the fixed-sigma gap**

- [ ] **Step 3: invoke the strict-margin constructor**

- [ ] **Step 4: preserve `alpha = globalCeiling - eta` exactly**

### Task 3: Contract, audit, and publication

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightGlobalOptimalTruncationParametersContract.lean`
- Create: `Test/ZeroDensityLayerBudgetJointTwoHeightGlobalOptimalTruncationParametersAxiomAudit.lean`

**Interfaces:**
- Consumes: the canonical optimizer and globally near-optimal constructor.
- Produces: focused declaration and axiom evidence.

- [ ] **Step 1: compile implementation and contract directly**

- [ ] **Step 2: audit optimizer specification, global dominance, and realization**

- [ ] **Step 3: commit docs and code separately**

- [ ] **Step 4: push and create a draft PR based on stack58**
