# Midpoint Sigma Strict Improvement Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove that an explicit interior density threshold strictly improves the cap-aligned outer-height exponent.

**Architecture:** Add one arithmetic module above the optimized prescribed-cap ceiling. It defines the midpoint threshold, proves strict improvement, and constructs a transfer-ready feasible parameter tuple without changing any analytic or oscillation module.

**Tech Stack:** Lean 4, real inequalities, optimized two-height Carlson ceiling.

## Global Constraints

- Modify only `ZeroDensityLayerBudget*.lean` and task design/plan files.
- Do not modify `ZeroForcedOscillationComplementaryBound.lean`.
- Do not modify VK-edge or sharp-oscillation files.
- State strict improvement honestly; do not claim global sigma optimality.

---

### Task 1: Midpoint arithmetic

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightMidpointSigmaImprovement.lean`

**Interfaces:**
- Consumes: `jointTwoHeightPrescribedCapOuterExponentCeiling`.
- Produces: `jointTwoHeightMidpointDensityThreshold` and `jointTwoHeightPrescribedCapOuterExponentCeiling_midpoint_gt_capAligned`.

- [ ] **Step 1: Define the midpoint threshold**

```lean
noncomputable def jointTwoHeightMidpointDensityThreshold
    (theta : ℝ) : ℝ :=
  ((1 / 2 : ℝ) + theta) / 2
```

- [ ] **Step 2: Prove the strict endpoint inequalities**

Use `linarith` from `1 / 2 < theta`.

- [ ] **Step 3: Prove both ceiling components beat the baseline**

Use `max sigma theta = theta` and
`targetAmplitudeCarlsonTwoHeightBalancedSlope sigma < 1 / 2`.

### Task 2: Transfer-ready parameter construction

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightMidpointSigmaImprovement.lean`

**Interfaces:**
- Consumes: the strict midpoint ceiling improvement.
- Produces: `exists_jointTwoHeightStrictlyImprovedMidpointSigmaParameters`.

- [ ] **Step 1: Choose alpha between the baseline and ceiling**

```lean
let alpha :=
  (2 * (beta - theta) +
    jointTwoHeightPrescribedCapOuterExponentCeiling beta sigma theta) / 2
```

- [ ] **Step 2: Prove contour compatibility**

Derive `1 - beta < 2 * (beta - theta)` from
`theta < (3 * beta - 1) / 2`.

- [ ] **Step 3: Construct tau and numerical feasibility**

Invoke
`jointTwoHeightPrescribedCapOuterExponentFeasible_of_lt_ceiling`.

### Task 3: Contract, audit, and publication

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightMidpointSigmaImprovementContract.lean`
- Create: `Test/ZeroDensityLayerBudgetJointTwoHeightMidpointSigmaImprovementAxiomAudit.lean`

**Interfaces:**
- Consumes: the midpoint theorem chain.
- Produces: focused API and axiom evidence.

- [ ] **Step 1: Add declaration checks**

- [ ] **Step 2: Add axiom prints for the two substantive theorems**

- [ ] **Step 3: Compile the three modules directly**

- [ ] **Step 4: Commit docs and code separately**

- [ ] **Step 5: Push and open a draft PR based on stack55**
