# Quantitative Reverse Finite-Height Zero-Free Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Derive finite-height zero freedom from an eventual actual PNT-error coefficient strictly below one half.

**Architecture:** Add a generic real eventual-upper/far-witness incompatibility lemma and compose it with stack48's half-amplitude transfer on the concrete right-edge cluster.

**Tech Stack:** Lean 4, filter eventual bounds, target-amplitude witnesses, actual zeta-zero clusters.

## Global Constraints

- Modify only `ZeroDensityLayerBudget*.lean` and task design/plan files.
- Do not modify `ZeroForcedOscillationComplementaryBound.lean`.
- Do not modify VK-edge or sharp-oscillation files.
- Preserve the exact strict threshold `q < 1 / 2`.

---

### Task 1: Quantitative real witness incompatibility

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualAutomaticQuantitativeReverseFiniteHeightZeroFree.lean`

**Interfaces:**
- Consumes: eventual `q * amplitude` upper bound and eventual amplitude positivity.
- Produces: `not_hasFarTargetAmplitude_mul_of_eventually_abs_le_mul`.

- [ ] **Step 1: Combine the upper bound with amplitude positivity**

- [ ] **Step 2: Evaluate a far witness after the eventual threshold**

- [ ] **Step 3: Use `q < d` to contradict the witness**

### Task 2: Quantitative finite-height zero-free transfer

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualAutomaticQuantitativeReverseFiniteHeightZeroFree.lean`

**Interfaces:**
- Consumes: stack48 and the right-edge cluster semantics.
- Produces: `exists_automaticGoodHeight_globalRealPartBound_eventualUpper_finiteHeightZeroFree`.

- [ ] **Step 1: Select automatic transfer parameters**

- [ ] **Step 2: Transfer a nonempty-cluster witness to coefficient `1 / 2`**

- [ ] **Step 3: Contradict the eventual coefficient `q < 1 / 2`**

- [ ] **Step 4: Convert cluster emptiness to finite-height zero freedom**

### Task 3: Contract, audit, and publication

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualAutomaticQuantitativeReverseFiniteHeightZeroFreeContract.lean`
- Create: `Test/ZeroDensityLayerBudgetActualAutomaticQuantitativeReverseFiniteHeightZeroFreeAxiomAudit.lean`

**Interfaces:**
- Consumes: both new theorems.
- Produces: focused API and axiom evidence.

- [ ] **Step 1: Add contract and axiom audit**

- [ ] **Step 2: Compile directly with minimal `.olean` files**

- [ ] **Step 3: Commit docs and code separately**

- [ ] **Step 4: Open a draft PR based on stack50**

