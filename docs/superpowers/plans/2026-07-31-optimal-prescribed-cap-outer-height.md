# Optimal Prescribed-Cap Outer-Height Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Compute the exact supremal common outer-height exponent after optimizing over every strip endpoint above a prescribed real-part cap.

**Architecture:** Existentially quantify the endpoint in a feasibility predicate, define the minimum optimized ceiling, construct the endpoint by a midpoint, and prove the converse upper bound.

**Tech Stack:** Lean 4, Mathlib ordered real arithmetic, balanced Carlson exponent API.

## Global Constraints

- Modify only `ZeroDensityLayerBudget*.lean` and task design/plan files.
- Do not modify `ZeroForcedOscillationComplementaryBound.lean`.
- Do not modify VK-edge or sharp-oscillation files.
- Preserve strict endpoint inequalities and the closed unit outer-height cap.

---

### Task 1: Prescribed-cap feasibility and ceiling

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightOptimalPrescribedCapOuterExponent.lean`

**Interfaces:**
- Produces: `IsJointTwoHeightPrescribedCapOuterExponentFeasible` and `jointTwoHeightPrescribedCapOuterExponentCeiling`.

- [ ] **Step 1: Define feasibility existentially over `tau`**

- [ ] **Step 2: Define the optimized ceiling using `max sigma theta`**

### Task 2: Constructive and converse optimality

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightOptimalPrescribedCapOuterExponent.lean`

**Interfaces:**
- Produces: `jointTwoHeightPrescribedCapOuterExponentFeasible_of_lt_ceiling` and `le_jointTwoHeightPrescribedCapOuterExponentCeiling_of_feasible`.

- [ ] **Step 1: Construct `tau` as the midpoint of its exact interval**

- [ ] **Step 2: Prove the resulting fixed-endpoint exponents are feasible**

- [ ] **Step 3: Recover the optimized ceiling bound from every feasible endpoint**

### Task 3: Exact contour criterion

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightOptimalPrescribedCapOuterExponent.lean`

**Interfaces:**
- Produces the ceiling and arithmetic iff theorems.

- [ ] **Step 1: Prove contour-compatible existence iff the floor is below the ceiling**

- [ ] **Step 2: Prove the exact arithmetic form**

### Task 4: Contract, audit, and publication

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightOptimalPrescribedCapOuterExponentContract.lean`
- Create: `Test/ZeroDensityLayerBudgetJointTwoHeightOptimalPrescribedCapOuterExponentAxiomAudit.lean`

**Interfaces:**
- Consumes: all new APIs.
- Produces: focused compile and axiom evidence.

- [ ] **Step 1: Add contract and audit**

- [ ] **Step 2: Compile directly with minimal `.olean` files**

- [ ] **Step 3: Commit docs and code separately**

- [ ] **Step 4: Open a draft PR based on stack52**

