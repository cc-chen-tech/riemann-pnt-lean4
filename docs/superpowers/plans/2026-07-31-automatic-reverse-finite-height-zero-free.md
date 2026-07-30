# Automatic Reverse Finite-Height Zero-Free Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Convert automatic reverse cluster exclusion into an actual finite-height zeta zero-free statement.

**Architecture:** Instantiate stack49 with `rightEdgeNontrivialZerosFinset beta H`, project emptiness from its real-ordinate enlargement, and apply the existing emptiness/zero-free equivalence.

**Tech Stack:** Lean 4, finite zeta-zero clusters, automatic Pintz-Carlson explicit-formula reverse transfer.

## Global Constraints

- Modify only `ZeroDensityLayerBudget*.lean` and task design/plan files.
- Do not modify `ZeroForcedOscillationComplementaryBound.lean`.
- Do not modify VK-edge or sharp-oscillation files.
- Keep the cluster witness conditional and explicit.

---

### Task 1: Finite-height specialization

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualAutomaticReverseFiniteHeightZeroFree.lean`

**Interfaces:**
- Consumes: `exists_automaticGoodHeight_globalRealPartBound_reverseClusterExclusion`, `rightEdgeNontrivialZerosFinset_conjugationInvariant`, and `rightEdgeNontrivialZerosFinset_eq_empty_iff_zeroFree`.
- Produces: `exists_automaticGoodHeight_globalRealPartBound_finiteHeightZeroFree`.

- [ ] **Step 1: Instantiate stack49 with the right-edge cluster**

- [ ] **Step 2: Project base-cluster emptiness from enlarged-cluster emptiness**

- [ ] **Step 3: Apply the finite-height zero-free equivalence**

### Task 2: Contract, audit, and publication

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualAutomaticReverseFiniteHeightZeroFreeContract.lean`
- Create: `Test/ZeroDensityLayerBudgetActualAutomaticReverseFiniteHeightZeroFreeAxiomAudit.lean`

**Interfaces:**
- Consumes: the new theorem.
- Produces: focused API and axiom evidence.

- [ ] **Step 1: Add `#check` and `#print axioms`**

- [ ] **Step 2: Compile implementation, contract, and audit directly**

- [ ] **Step 3: Commit docs and code separately**

- [ ] **Step 4: Open a draft PR based on stack49**

