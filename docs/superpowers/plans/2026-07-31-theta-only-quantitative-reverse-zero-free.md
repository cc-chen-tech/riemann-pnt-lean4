# Theta-Only Quantitative Reverse Zero-Free Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Derive finite-height right-edge zero freedom from a theta-only automatic transfer and a `q < 1 / 2` actual-error bound.

**Architecture:** Specialize stack70 to the right-edge finset at its automatically selected beta, normalize the user upper bound to that local beta, and apply the established half-amplitude contradiction.

**Tech Stack:** Lean 4, theta-only parameter selection, actual target-amplitude witnesses, quantitative reverse transfer.

## Global Constraints

- Modify only `ZeroDensityLayerBudget*.lean` and task design/plan files.
- Do not modify `ZeroForcedOscillationComplementaryBound.lean`.
- Do not modify VK-edge or sharp-oscillation files.
- Keep the visible-cluster witness explicit.

---

### Task 1: Theta-only reverse theorem

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualThetaOnlyQuantitativeReverseZeroFree.lean`

**Interfaces:**
- Consumes: stack70 theta-only transfer and the coefficient contradiction.
- Produces: `exists_thetaOnlyAutomaticGoodHeight_globalRealPartBound_eventualUpper_finiteHeightZeroFree`.

- [x] **Step 1: specialize the theta-only transfer to the selected right-edge finset**

- [x] **Step 2: align the canonical beta in the upper-bound hypothesis**

- [x] **Step 3: contradict nonempty-cluster half-amplitude witnesses**

- [x] **Step 4: conclude finite-height zero freedom**

### Task 2: Contract, audit, and publication

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualThetaOnlyQuantitativeReverseZeroFreeContract.lean`
- Create: `Test/ZeroDensityLayerBudgetActualThetaOnlyQuantitativeReverseZeroFreeAxiomAudit.lean`

- [x] **Step 1: compile implementation and contract directly**

- [x] **Step 2: run the focused axiom audit**

- [x] **Step 3: commit docs and code separately**

- [x] **Step 4: push and create a draft PR based on stack70**
