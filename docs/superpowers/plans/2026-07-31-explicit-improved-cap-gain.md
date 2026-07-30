# Explicit Improved Cap Gain Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Derive explicit rational formulas for the improved global cap threshold and its normalized gain.

**Architecture:** Evaluate the Carlson density exponent at the canonical threshold, substitute it into the improved-cap definition, factor the difference, and bound the normalized gain using the already proved strict threshold inequalities.

**Tech Stack:** Lean 4, real rational identities, Carlson density exponent.

## Global Constraints

- Modify only `ZeroDensityLayerBudget*.lean` and task design/plan files.
- Do not modify `ZeroForcedOscillationComplementaryBound.lean`.
- Do not modify VK-edge or sharp-oscillation files.
- Keep claims internal to the formalized Carlson model.

---

### Task 1: Explicit threshold formula

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightExplicitImprovedCapGain.lean`

**Interfaces:**
- Produces: `jointTwoHeightCanonicalDensityExponent`, its canonical evaluation theorem, and `jointTwoHeightImprovedGlobalCapThreshold_explicit`.

- [ ] **Step 1: evaluate the canonical density exponent**

- [ ] **Step 2: substitute it into the global cap threshold**

### Task 2: Gain formulas

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightExplicitImprovedCapGain.lean`

**Interfaces:**
- Produces: the factored gain, normalized gain, and `(0,1)` bound.

- [ ] **Step 1: factor the absolute threshold gain**

- [ ] **Step 2: divide by the canonical-to-beta gap**

- [ ] **Step 3: prove the normalized fraction lies in `(0,1)`**

### Task 3: Contract, audit, and publication

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightExplicitImprovedCapGainContract.lean`
- Create: `Test/ZeroDensityLayerBudgetJointTwoHeightExplicitImprovedCapGainAxiomAudit.lean`

**Interfaces:**
- Consumes: the explicit gain theorem chain.
- Produces: focused declaration and axiom evidence.

- [ ] **Step 1: compile implementation and contract directly**

- [ ] **Step 2: run the focused axiom audit**

- [ ] **Step 3: commit docs and code separately**

- [ ] **Step 4: push and create a draft PR based on stack64**
