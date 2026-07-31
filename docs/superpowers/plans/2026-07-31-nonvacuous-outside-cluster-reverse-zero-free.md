# Nonvacuous Outside-Cluster Reverse Zero-Free Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Exclude a finite-height right-edge zero cluster using a `q < 1 / 2` actual-error bound while imposing the real-part cap only outside that cluster.

**Architecture:** Specialize the stack76 outside-cluster transfer to the concrete right-edge zero finset, apply the established coefficient contradiction to the resulting half-amplitude witness, and convert finset emptiness to `FiniteHeightRightEdgeZeroFree`.

**Tech Stack:** Lean 4, positive outside-cluster cap transfer, actual PNT target-amplitude witnesses, finite-height zeta-zero finsets.

## Global Constraints

- Create only `ZeroDensityLayerBudgetActualPositiveOutsideClusterCapQuantitativeReverseZeroFree*.lean`, its audit, and task documentation.
- Do not modify `ZeroForcedOscillationComplementaryBound.lean`.
- Do not modify VK-edge or sharp-oscillation files.
- Keep both the outside-cluster cap and visible-cluster witness explicit.

---

### Task 1: Nonvacuous reverse theorem

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualPositiveOutsideClusterCapQuantitativeReverseZeroFree.lean`

**Interfaces:**
- Consumes: stack76 outside-cluster transfer and the coefficient contradiction.
- Produces: `exists_automaticGoodHeight_positiveOutsideRightEdgeCap_eventualUpper_finiteHeightZeroFree`.

- [x] **Step 1: choose the finite right-edge zero finset as exceptional cluster**

- [x] **Step 2: run the outside-cluster actual transfer**

- [x] **Step 3: contradict a nonempty cluster with the `q < 1 / 2` upper bound**

- [x] **Step 4: convert cluster emptiness to finite-height zero freedom**

### Task 2: Contract, audit, and publication

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualPositiveOutsideClusterCapQuantitativeReverseZeroFreeContract.lean`
- Create: `Test/ZeroDensityLayerBudgetActualPositiveOutsideClusterCapQuantitativeReverseZeroFreeAxiomAudit.lean`

- [x] **Step 1: compile implementation and contract directly**

- [x] **Step 2: run the focused axiom audit**

- [x] **Step 3: commit documentation and code separately**

- [x] **Step 4: push and create a draft PR based on stack76**
