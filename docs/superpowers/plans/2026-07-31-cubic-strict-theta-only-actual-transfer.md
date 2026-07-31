# Cubic Strict Theta-Only Actual Transfer Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Run the actual theta-only unified transfer at the cubic-strict target exponent.

**Architecture:** Obtain strict target feasibility from stack73, pass it to the existing improved-cap actual transfer, and return every optimized parameter together with the pointwise comparison against the midpoint selector.

**Tech Stack:** Lean 4, stack73 cubic-strict selector, existing actual improved-cap Pintz-Carlson-explicit-formula transfer.

## Global Constraints

- Create only `ZeroDensityLayerBudgetActualThetaOnlyCubicStrictUnifiedTransfer*.lean`, its audit, and task documentation.
- Do not modify `ZeroForcedOscillationComplementaryBound.lean`.
- Do not modify VK-edge or sharp-oscillation files.
- Keep the visible-cluster witness explicit.

---

### Task 1: Cubic-strict actual transfer

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualThetaOnlyCubicStrictUnifiedTransfer.lean`

**Interfaces:**
- Consumes: `jointTwoHeightCubicStrictTargetExponent_spec` and `exists_improvedCapAutomaticGoodHeight_globalRealPartBoundNaturalTargetTransfer`.
- Produces: `exists_thetaOnlyCubicStrictAutomaticGoodHeight_globalRealPartBoundNaturalTargetTransfer`.

- [x] **Step 1: select the inverse boundary and cubic-strict target**

- [x] **Step 2: pass strict feasibility to the improved-cap actual transfer**

- [x] **Step 3: return all optimized parameters and actual PNT transfer conclusions**

### Task 2: Contract, audit, and publication

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualThetaOnlyCubicStrictUnifiedTransferContract.lean`
- Create: `Test/ZeroDensityLayerBudgetActualThetaOnlyCubicStrictUnifiedTransferAxiomAudit.lean`

- [x] **Step 1: compile implementation and contract directly**

- [x] **Step 2: run the focused axiom audit**

- [x] **Step 3: commit documentation and code separately**

- [x] **Step 4: push and create a draft PR based on stack73**
