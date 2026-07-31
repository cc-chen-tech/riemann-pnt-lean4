# Cubic Strict Theta-Only Reverse Zero-Free Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Derive finite-height right-edge zero freedom from the cubic-strict theta-only actual transfer and a `q < 1 / 2` actual-error bound.

**Architecture:** Specialize stack74 to the right-edge finset at its cubic-strict beta, normalize the upper-bound hypothesis to that beta, and apply the established half-amplitude contradiction.

**Tech Stack:** Lean 4, cubic-strict theta-only actual transfer, target-amplitude witnesses, quantitative reverse finite-height transfer.

## Global Constraints

- Create only `ZeroDensityLayerBudgetActualThetaOnlyCubicStrictQuantitativeReverseZeroFree*.lean`, its audit, and task documentation.
- Do not modify `ZeroForcedOscillationComplementaryBound.lean`.
- Do not modify VK-edge or sharp-oscillation files.
- Keep the visible-cluster witness explicit.

---

### Task 1: Cubic-strict reverse theorem

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualThetaOnlyCubicStrictQuantitativeReverseZeroFree.lean`

**Interfaces:**
- Consumes: stack74 cubic-strict actual transfer and the existing coefficient contradiction.
- Produces: `exists_thetaOnlyCubicStrictAutomaticGoodHeight_globalRealPartBound_eventualUpper_finiteHeightZeroFree`.

- [x] **Step 1: specialize the cubic-strict transfer to the right-edge finset**

- [x] **Step 2: align the automatic beta in the eventual upper bound**

- [x] **Step 3: contradict nonempty-cluster half-amplitude witnesses**

- [x] **Step 4: conclude finite-height right-edge zero freedom**

### Task 2: Contract, audit, and publication

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualThetaOnlyCubicStrictQuantitativeReverseZeroFreeContract.lean`
- Create: `Test/ZeroDensityLayerBudgetActualThetaOnlyCubicStrictQuantitativeReverseZeroFreeAxiomAudit.lean`

- [x] **Step 1: compile implementation and contract directly**

- [x] **Step 2: run the focused axiom audit**

- [x] **Step 3: commit documentation and code separately**

- [x] **Step 4: push and create a draft PR based on stack74**
