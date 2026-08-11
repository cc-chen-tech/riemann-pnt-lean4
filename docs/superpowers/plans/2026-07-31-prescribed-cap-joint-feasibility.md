# Prescribed-Cap Joint Feasibility Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Select joint two-height parameters with a prescribed ceiling `theta < tau`.

**Architecture:** First factor the common-`alpha` construction for fixed feasible endpoints. Then choose `sigma` and `tau` so both `sigma` and `theta` lie below the Carlson feasibility ceiling.

**Tech Stack:** Lean 4, Mathlib ordered-field arithmetic, existing balanced Carlson exponent API.

## Global Constraints

- Modify only `ZeroDensityLayerBudget*.lean` and task design/plan files.
- Do not modify `ZeroForcedOscillationComplementaryBound.lean`.
- Do not modify VK-edge or sharp-oscillation files.
- Keep the global real-part ceiling as an explicit hypothesis.

---

### Task 1: Fixed-endpoint common outer height

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightPrescribedCapFeasibility.lean`

**Interfaces:**
- Consumes: feasible `sigma` and `tau`.
- Produces: `exists_jointTwoHeightTargetAmplitudeMargins_of_endpoints`.

- [ ] **Step 1: Build the low and high outer-height ceilings**

- [ ] **Step 2: Cap by `1` and choose a common midpoint `alpha`**

- [ ] **Step 3: Generate both balanced cuts and strict margins**

### Task 2: Prescribed-cap endpoint selection

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightPrescribedCapFeasibility.lean`

**Interfaces:**
- Consumes: `theta < (3 * beta - 1) / 2`.
- Produces: `exists_jointTwoHeightTargetAmplitudeParameters_above_cap`.

- [ ] **Step 1: Choose `sigma` below the canonical threshold**

- [ ] **Step 2: Prove the Carlson `tau` ceiling exceeds the threshold**

- [ ] **Step 3: Choose `tau` above `max sigma theta`**

- [ ] **Step 4: Apply the fixed-endpoint theorem**

### Task 3: Contract, audit, and publication

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightPrescribedCapFeasibilityContract.lean`
- Create: `Test/ZeroDensityLayerBudgetJointTwoHeightPrescribedCapFeasibilityAxiomAudit.lean`

**Interfaces:**
- Consumes: both new theorems.
- Produces: focused direct-compilation and axiom evidence.

- [ ] **Step 1: Add `#check` contract entries**

- [ ] **Step 2: Add `#print axioms` entries**

- [ ] **Step 3: Validate directly with minimal `.olean` files**

- [ ] **Step 4: Commit docs and code separately**

- [ ] **Step 5: Open a draft PR based on stack46**
