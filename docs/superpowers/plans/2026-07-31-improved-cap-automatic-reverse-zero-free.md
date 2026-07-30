# Improved Cap Automatic Reverse Zero-Free Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Derive finite-height right-edge zero freedom from a `q < 1 / 2` actual-error bound throughout the improved cap range.

**Architecture:** Specialize stack63's automatic actual transfer to the finite right-edge zero cluster and apply the established coefficient-separation contradiction. Preserve all automatically selected optimal-height data in the theorem output.

**Tech Stack:** Lean 4, improved cap threshold, target-amplitude witnesses, quantitative reverse transfer.

## Global Constraints

- Modify only `ZeroDensityLayerBudget*.lean` and task design/plan files.
- Do not modify `ZeroForcedOscillationComplementaryBound.lean`.
- Do not modify VK-edge or sharp-oscillation files.
- Keep the visible-cluster witness explicit.

---

### Task 1: Improved-cap automatic reverse theorem

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualImprovedCapAutomaticReverseZeroFree.lean`

**Interfaces:**
- Consumes: stack63 automatic actual transfer and the coefficient contradiction.
- Produces: `exists_improvedCapAutomaticGoodHeight_globalRealPartBound_eventualUpper_finiteHeightZeroFree`.

- [ ] **Step 1: specialize stack63 to the right-edge finset**

- [ ] **Step 2: derive a half-amplitude far witness from nonemptiness**

- [ ] **Step 3: contradict the eventual `q < 1 / 2` bound**

- [ ] **Step 4: conclude finite-height zero freedom**

### Task 2: Contract, audit, and publication

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualImprovedCapAutomaticReverseZeroFreeContract.lean`
- Create: `Test/ZeroDensityLayerBudgetActualImprovedCapAutomaticReverseZeroFreeAxiomAudit.lean`

**Interfaces:**
- Consumes: the improved-cap reverse theorem.
- Produces: focused declaration and axiom evidence.

- [ ] **Step 1: compile implementation and contract directly**

- [ ] **Step 2: run the focused axiom audit**

- [ ] **Step 3: commit docs and code separately**

- [ ] **Step 4: push and create a draft PR based on stack63**
