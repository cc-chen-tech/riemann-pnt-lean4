# Near-Optimal Truncation Parameters Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Produce a full transfer-ready two-height parameter tuple at any prescribed positive distance below the optimized outer-height ceiling.

**Architecture:** First extract balanced cuts and epsilons from a feasible fixed exponent. Then instantiate the endpoint-optimized ceiling at `alpha = ceiling - eta`.

**Tech Stack:** Lean 4, balanced Carlson exponent identities, optimized prescribed-cap ceiling.

## Global Constraints

- Modify only `ZeroDensityLayerBudget*.lean` and task design/plan files.
- Do not modify `ZeroForcedOscillationComplementaryBound.lean`.
- Do not modify VK-edge or sharp-oscillation files.
- Preserve the exact identity `alpha = ceiling - eta`.

---

### Task 1: Margin extraction

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightNearOptimalTruncationParameters.lean`

**Interfaces:**
- Consumes: `IsJointTwoHeightOuterExponentFeasible`.
- Produces: `exists_jointTwoHeightStrictMargins_of_outerExponentFeasible`.

- [ ] **Step 1: Define balanced cuts and half-negative epsilons**

- [ ] **Step 2: Prove positivity and cut bounds**

- [ ] **Step 3: Rewrite both Carlson exponents by the balanced identities**

### Task 2: Near-optimal tuple

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightNearOptimalTruncationParameters.lean`

**Interfaces:**
- Consumes: the optimized prescribed-cap ceiling.
- Produces: `exists_jointTwoHeightNearOptimalTruncationParameters`.

- [ ] **Step 1: Set `alpha = ceiling - eta`**

- [ ] **Step 2: Prove contour compatibility and strict below-ceiling position**

- [ ] **Step 3: Obtain `tau` from prescribed-cap feasibility**

- [ ] **Step 4: Attach all cuts and strict margins**

### Task 3: Contract, audit, and publication

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightNearOptimalTruncationParametersContract.lean`
- Create: `Test/ZeroDensityLayerBudgetJointTwoHeightNearOptimalTruncationParametersAxiomAudit.lean`

**Interfaces:**
- Consumes: both new theorems.
- Produces: focused API and axiom evidence.

- [ ] **Step 1: Add contract and audit**

- [ ] **Step 2: Compile directly with minimal `.olean` files**

- [ ] **Step 3: Commit docs and code separately**

- [ ] **Step 4: Open a draft PR based on stack53**

