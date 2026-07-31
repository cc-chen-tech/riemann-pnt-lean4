# Cubic Strict Target Exponent Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Construct an automatic strict target exponent that is pointwise sharper than the midpoint selector and has theta-side cubic excess constant `73 / 2`.

**Architecture:** Interpolate from the inverse boundary toward one using coefficient `(1 - theta)^2 / 2`. Prove global strict feasibility from coefficient bounds and improved-threshold monotonicity, then combine the stack72 cubic and gap-ratio limits.

**Tech Stack:** Lean 4, Mathlib real inequalities and filters, stack72 theta-only target asymptotics.

## Global Constraints

- Create only `ZeroDensityLayerBudgetJointTwoHeightCubicStrictTargetExponent*.lean`, its audit, and task documentation.
- Do not modify `ZeroForcedOscillationComplementaryBound.lean`.
- Do not modify VK-edge or sharp-oscillation files.
- Preserve a strict improved-cap inequality for every `theta` in `(1 / 2, 1)`.

---

### Task 1: Cubic strict selector

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightCubicStrictTargetExponent.lean`

**Interfaces:**
- Consumes: the canonical inverse boundary, midpoint strict selector, improved-threshold strict monotonicity, and stack72 theta-only limits.
- Produces: `jointTwoHeightCubicStrictTargetExponent`, its strict-feasibility specification, and its cubic excess limit.

- [x] **Step 1: define the cubic interpolation selector**

- [x] **Step 2: prove it lies strictly between the inverse boundary and midpoint**

- [x] **Step 3: prove it remains below one and has strict improved-cap slack**

- [x] **Step 4: prove its theta-side cubic excess tends to `73 / 2`**

### Task 2: Contract, audit, and publication

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightCubicStrictTargetExponentContract.lean`
- Create: `Test/ZeroDensityLayerBudgetJointTwoHeightCubicStrictTargetExponentAxiomAudit.lean`

- [x] **Step 1: compile implementation and contract directly**

- [x] **Step 2: run the focused axiom audit**

- [x] **Step 3: commit documentation and code separately**

- [x] **Step 4: push and create a draft PR based on stack72**
