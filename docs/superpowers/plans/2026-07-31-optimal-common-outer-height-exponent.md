# Optimal Common Outer-Height Exponent Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove an explicit supremal outer-height exponent for the joint low-layer and Carlson transfer.

**Architecture:** Encode the three numerical constraints in one feasibility predicate, define their minimum ceiling, and prove both order directions plus the exact contour-floor existence criterion.

**Tech Stack:** Lean 4, Mathlib linear orders and real arithmetic, balanced Carlson exponent API.

## Global Constraints

- Modify only `ZeroDensityLayerBudget*.lean` and task design/plan files.
- Do not modify `ZeroForcedOscillationComplementaryBound.lean`.
- Do not modify VK-edge or sharp-oscillation files.
- Preserve the closed `alpha <= 1` endpoint in the optimality theorem.

---

### Task 1: Feasibility and ceiling definitions

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightOptimalOuterExponent.lean`

**Interfaces:**
- Produces: `IsJointTwoHeightOuterExponentFeasible` and `jointTwoHeightOuterExponentCeiling`.

- [ ] **Step 1: Define the feasibility predicate**

- [ ] **Step 2: Define the minimum of the unit, low-layer, and Carlson ceilings**

### Task 2: Supremal optimality

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightOptimalOuterExponent.lean`

**Interfaces:**
- Produces: `jointTwoHeightOuterExponentFeasible_of_lt_ceiling` and `le_jointTwoHeightOuterExponentCeiling_of_feasible`.

- [ ] **Step 1: Prove strict points below the ceiling are feasible**

- [ ] **Step 2: Prove every feasible point is bounded by the ceiling**

### Task 3: Exact contour feasibility

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightOptimalOuterExponent.lean`

**Interfaces:**
- Produces: `exists_contourCompatible_jointTwoHeightOuterExponent_iff` and `exists_contourCompatible_jointTwoHeightOuterExponent_iff_arithmetic`.

- [ ] **Step 1: Prove existence iff the contour floor is below the ceiling**

- [ ] **Step 2: Rewrite the ceiling inequality as the three exact arithmetic conditions**

### Task 4: Contract, audit, and publication

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightOptimalOuterExponentContract.lean`
- Create: `Test/ZeroDensityLayerBudgetJointTwoHeightOptimalOuterExponentAxiomAudit.lean`

**Interfaces:**
- Consumes: all definitions and theorems.
- Produces: focused API and axiom evidence.

- [ ] **Step 1: Add contract and axiom audit**

- [ ] **Step 2: Compile directly with minimal `.olean` files**

- [ ] **Step 3: Commit docs and code separately**

- [ ] **Step 4: Open a draft PR based on stack51**

