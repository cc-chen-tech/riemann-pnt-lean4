# Canonical Strict Target Exponent Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Define a canonical strictly feasible target exponent above the unique inverse boundary.

**Architecture:** Take the midpoint between the unique optimal boundary exponent and one. Use interval arithmetic plus strict monotonicity of the improved threshold to prove the full strict-feasibility specification.

**Tech Stack:** Lean 4, unique inverse target exponent, strict threshold monotonicity.

## Global Constraints

- Modify only `ZeroDensityLayerBudget*.lean` and task design/plan files.
- Do not modify `ZeroForcedOscillationComplementaryBound.lean`.
- Do not modify VK-edge or sharp-oscillation files.

---

### Task 1: Canonical strict target parameter

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightCanonicalStrictTargetExponent.lean`

**Interfaces:**
- Consumes: `jointTwoHeightOptimalTargetExponent` and threshold strict monotonicity.
- Produces: the midpoint target exponent and complete strict-feasibility specification.

- [ ] **Step 1: define the midpoint exponent**

- [ ] **Step 2: prove boundary < midpoint < one**

- [ ] **Step 3: prove theta < boundary < midpoint**

- [ ] **Step 4: prove the strict improved-threshold inequality**

### Task 2: Projection lemmas

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightCanonicalStrictTargetExponent.lean`

- [ ] **Step 1: expose lower and upper target bounds**

- [ ] **Step 2: expose theta < beta**

- [ ] **Step 3: expose theta < improved threshold**

### Task 3: Contract, audit, and publication

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightCanonicalStrictTargetExponentContract.lean`
- Create: `Test/ZeroDensityLayerBudgetJointTwoHeightCanonicalStrictTargetExponentAxiomAudit.lean`

- [ ] **Step 1: compile implementation and contract directly**

- [ ] **Step 2: run the focused axiom audit**

- [ ] **Step 3: commit docs and code separately**

- [ ] **Step 4: push and create a draft PR based on stack68**
