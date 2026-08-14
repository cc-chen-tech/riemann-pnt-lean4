# Exact Sigma Optimizer Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Construct and prove global optimality of the density threshold balancing the low-layer and Carlson ceilings.

**Architecture:** Add one arithmetic optimization module above stack56. First prove antitonicity of the Carlson density and balanced slope, then construct a balance point by IVT on a denominator-cleared polynomial, and finally compare every competing threshold to that point.

**Tech Stack:** Lean 4, real polynomial inequalities, continuity, intermediate value theorem, optimized two-height ceiling.

## Global Constraints

- Modify only `ZeroDensityLayerBudget*.lean` and task design/plan files.
- Do not modify `ZeroForcedOscillationComplementaryBound.lean`.
- Do not modify VK-edge or sharp-oscillation files.
- Do not claim a closed-form optimizer or uniqueness unless separately proved.

---

### Task 1: Slope antitonicity

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightExactSigmaOptimizer.lean`

**Interfaces:**
- Consumes: `carlsonTwoHeightDensityExponent` and `targetAmplitudeCarlsonTwoHeightBalancedSlope`.
- Produces: `carlsonTwoHeightDensityExponent_antitoneOn_half_one` and `targetAmplitudeCarlsonTwoHeightBalancedSlope_antitoneOn_half_one`.

- [ ] **Step 1: Factor the density-exponent difference**

Use nonnegativity of
`(sigma₂ - sigma₁) * (sigma₁ + sigma₂ - 1)`.

- [ ] **Step 2: Compare the balanced rational slopes**

Cross multiply positive denominators and use
`(q₁ - q₂) * (q₁ + q₂ + q₁ * q₂) ≥ 0`.

### Task 2: Balance-point existence

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightExactSigmaOptimizer.lean`

**Interfaces:**
- Produces: `jointTwoHeightSigmaBalancePolynomial`, `IsJointTwoHeightSigmaOptimizer`, and `exists_jointTwoHeightSigmaOptimizer`.

- [ ] **Step 1: Define the denominator-cleared polynomial**

- [ ] **Step 2: Prove global continuity with `fun_prop`**

- [ ] **Step 3: Evaluate the signs at `1 / 2` and `theta`**

- [ ] **Step 4: Apply `intermediate_value_Icc'`**

- [ ] **Step 5: Recover the balanced-slope equation**

### Task 3: Exact global ceiling optimality

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightExactSigmaOptimizer.lean`

**Interfaces:**
- Produces: `jointTwoHeightPrescribedCapOuterExponentCeiling_eq_of_sigmaOptimizer` and `jointTwoHeightPrescribedCapOuterExponentCeiling_le_at_sigmaOptimizer`.

- [ ] **Step 1: Rewrite the optimizer ceiling**

Prove it equals `min 1 (2 * (beta - sigmaOpt))`.

- [ ] **Step 2: Compare thresholds left of the optimizer**

Use balanced-slope antitonicity and the Carlson component.

- [ ] **Step 3: Compare thresholds right of the optimizer**

Use the decreasing low-layer component.

- [ ] **Step 4: Include the unit cap with `le_min`**

### Task 4: Contract, audit, and publication

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightExactSigmaOptimizerContract.lean`
- Create: `Test/ZeroDensityLayerBudgetJointTwoHeightExactSigmaOptimizerAxiomAudit.lean`

**Interfaces:**
- Consumes: the exact optimizer theorem chain.
- Produces: focused API and axiom evidence.

- [ ] **Step 1: Add focused declaration checks**

- [ ] **Step 2: Audit the existence, formula, and global optimality theorems**

- [ ] **Step 3: Compile implementation, contract, and audit directly**

- [ ] **Step 4: Commit docs and code separately**

- [ ] **Step 5: Push and create a draft PR based on stack56**
