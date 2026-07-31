# Theta-Only Target Asymptotic Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove the theta-side cubic excess of the inverse optimal target and the linear excess of the midpoint strict target.

**Architecture:** First establish convergence of the canonical inverse target to one from below. Compose the existing beta-side cubic limit with that inverse, prove the source and target gaps are asymptotically equal, and derive both normalized theta-side limits.

**Tech Stack:** Lean 4, Mathlib filters and one-sided limits, existing improved-cap inverse and cubic-deficit theorems.

## Global Constraints

- Create only `ZeroDensityLayerBudgetJointTwoHeightThetaOnlyTargetAsymptotic*.lean`, its audit, and task documentation.
- Do not modify `ZeroForcedOscillationComplementaryBound.lean`.
- Do not modify VK-edge or sharp-oscillation files.
- Preserve the exact asymptotic constant `36`.

---

### Task 1: Inverse and normalization limits

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightThetaOnlyTargetAsymptotic.lean`

**Interfaces:**
- Consumes: `jointTwoHeightOptimalTargetExponent_spec` and `tendsto_jointTwoHeightImprovedGlobalCapThreshold_cubicDeficit`.
- Produces: one-sided inverse convergence, gap-ratio convergence, theta-side cubic excess, and midpoint linear excess.

- [x] **Step 1: prove the canonical inverse target tends to one from below**

- [x] **Step 2: compose the beta-side cubic deficit with the inverse**

- [x] **Step 3: prove `(1 - betaStar theta) / (1 - theta) -> 1`**

- [x] **Step 4: transfer the cubic normalization to `(1 - theta)^3`**

- [x] **Step 5: prove the midpoint strict target has normalized linear excess `1 / 2`**

### Task 2: Contract, audit, and publication

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightThetaOnlyTargetAsymptoticContract.lean`
- Create: `Test/ZeroDensityLayerBudgetJointTwoHeightThetaOnlyTargetAsymptoticAxiomAudit.lean`

- [x] **Step 1: compile the implementation directly**

- [x] **Step 2: compile the declaration contract**

- [x] **Step 3: run the focused axiom audit**

- [x] **Step 4: commit documentation and code separately**

- [x] **Step 5: push and create a draft PR based on stack71**
