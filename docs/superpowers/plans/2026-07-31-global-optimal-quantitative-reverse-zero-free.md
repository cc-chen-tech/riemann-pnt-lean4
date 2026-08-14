# Global Optimal Quantitative Reverse Zero-Free Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Convert an eventual `q < 1 / 2` actual-error bound into finite-height right-edge zero freedom at the globally optimized truncation height.

**Architecture:** Specialize stack60 to the finite right-edge zero cluster and reuse stack51's coefficient-separation contradiction. Preserve the canonical optimizer and exact global exponent in the reverse theorem output.

**Tech Stack:** Lean 4, actual relative Chebyshev error, target-amplitude witnesses, globally optimized two-height transfer.

## Global Constraints

- Modify only `ZeroDensityLayerBudget*.lean` and task design/plan files.
- Do not modify `ZeroForcedOscillationComplementaryBound.lean`.
- Do not modify VK-edge or sharp-oscillation files.
- Keep the visible-cluster witness explicit.

---

### Task 1: Global quantitative reverse transfer

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualGlobalOptimalQuantitativeReverseZeroFree.lean`

**Interfaces:**
- Consumes: stack60 global actual transfer and stack51 coefficient contradiction.
- Produces: `exists_globallyNearOptimalAutomaticGoodHeight_globalRealPartBound_eventualUpper_finiteHeightZeroFree`.

- [ ] **Step 1: specialize the global transfer to the right-edge finset**

- [ ] **Step 2: assume the enlarged cluster is nonempty**

- [ ] **Step 3: obtain the half-amplitude far witness**

- [ ] **Step 4: contradict the eventual `q < 1 / 2` upper bound**

- [ ] **Step 5: convert enlarged-cluster emptiness to finite-height zero freedom**

### Task 2: Contract, audit, and publication

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualGlobalOptimalQuantitativeReverseZeroFreeContract.lean`
- Create: `Test/ZeroDensityLayerBudgetActualGlobalOptimalQuantitativeReverseZeroFreeAxiomAudit.lean`

**Interfaces:**
- Consumes: the global reverse theorem.
- Produces: focused declaration and axiom evidence.

- [ ] **Step 1: compile implementation and contract directly**

- [ ] **Step 2: run the focused axiom audit**

- [ ] **Step 3: commit docs and code separately**

- [ ] **Step 4: push and create a draft PR based on stack60**
