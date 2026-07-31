# Cubic Cap Deficit Asymptotic Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove the improved cap deficit is asymptotic to `36 * (1 - beta)^3`.

**Architecture:** First derive exact rational normalizations from stack65's explicit threshold. Then transfer elementary continuous rational limits to the original threshold expressions by eventual equality on the left neighborhood of one.

**Tech Stack:** Lean 4, one-sided filters, continuous rational functions, explicit Carlson threshold formulas.

## Global Constraints

- Modify only `ZeroDensityLayerBudget*.lean` and task design/plan files.
- Do not modify `ZeroForcedOscillationComplementaryBound.lean`.
- Do not modify VK-edge or sharp-oscillation files.
- State the asymptotic as internal to the formalized Carlson model.

---

### Task 1: Exact normalized identities

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightCubicCapDeficitAsymptotic.lean`

**Interfaces:**
- Produces: the cubic normalization and old/new deficit-ratio identities.

- [ ] **Step 1: normalize the new deficit by `(1 - beta)^3`**

- [ ] **Step 2: normalize it by the old canonical deficit**

### Task 2: One-sided limits

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightCubicCapDeficitAsymptotic.lean`

**Interfaces:**
- Produces: the cubic limit `36` and relative deficit limit `0`.

- [ ] **Step 1: prove continuity of the rational normal forms at one**

- [ ] **Step 2: restrict the limits to `nhdsWithin 1 (Iio 1)`**

- [ ] **Step 3: use eventual `2 / 3 < beta < 1` to rewrite by exact identities**

### Task 3: Contract, audit, and publication

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightCubicCapDeficitAsymptoticContract.lean`
- Create: `Test/ZeroDensityLayerBudgetJointTwoHeightCubicCapDeficitAsymptoticAxiomAudit.lean`

**Interfaces:**
- Consumes: exact and asymptotic deficit theorems.
- Produces: focused declaration and axiom evidence.

- [ ] **Step 1: compile implementation and contract directly**

- [ ] **Step 2: run the focused axiom audit**

- [ ] **Step 3: commit docs and code separately**

- [ ] **Step 4: push and create a draft PR based on stack65**
