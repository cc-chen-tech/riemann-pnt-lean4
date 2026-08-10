# Actual Target-Amplitude Two-Height Strip Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Transfer the target-amplitude two-height exponents to the actual multiplicity-weighted zeta-zero strip and prove a genuine positive-width strip decay theorem for every `2/3 < beta < 1`.

**Architecture:** Normalize the existing actual low/high budgets by `targetZeroPowerAmplitude`, prove exact endpoint-shift identities, and reuse the audited actual two-height convergence theorems. A final existential theorem perturbs the canonical limiting endpoint to a strict positive-width strip.

**Tech Stack:** Lean 4, Mathlib real powers and filters, existing actual Carlson two-height split, stack 35 target-amplitude exponent arithmetic.

## Global Constraints

- Modify only new `ZeroDensityLayerBudget*` artifacts and this task's documents.
- Do not read, modify, delete, or stage `ZeroForcedOscillationComplementaryBound.lean`.
- Do not modify VK-edge modules.
- Preserve analytic multiplicity and the exact `x ^ (beta - 1)` target scale.
- Do not claim a full complementary-tail estimate, unconditional Omega theorem, or RH.

---

### Task 1: Endpoint-shift identities and normalized budgets

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualTargetAmplitudeTwoHeightStrip.lean`

**Interfaces:**
- Consumes: stack 35 exponent definitions and existing actual two-height budgets.
- Produces: normalized low/high budget definitions and endpoint-shift equalities.

- [ ] **Step 1: Prove the target-power quotient identity**

For `0 < x`, prove:

```text
x^(tau-1) / targetZeroPowerAmplitude(beta,x)
  = x^((tau-beta+1)-1).
```

- [ ] **Step 2: Define target low and high budgets**

Each is the corresponding existing actual budget divided by the target
amplitude.

- [ ] **Step 3: Prove both budgets equal shifted-endpoint budgets**

Use the quotient identity and ring normalization.

### Task 2: Actual normalized strip convergence

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualTargetAmplitudeTwoHeightStrip.lean`

**Interfaces:**
- Consumes: Task 1 shift identities and existing actual budget convergence.
- Produces: low, high, and whole-strip target-normalized convergence.

- [ ] **Step 1: Transfer low/high budget convergence**

Rewrite to endpoint `tau - beta + 1`, then invoke the existing low/high
budget convergence theorems.

- [ ] **Step 2: Define the normalized actual strip mass**

Divide the multiplicity-weighted norm sum over
`actualPositiveCarlsonStrip sigma tau (x^alpha)` by
`targetZeroPowerAmplitude beta x`.

- [ ] **Step 3: Prove the two-height majorization**

For `x >= 1`, divide the existing actual strip bound by the positive target
amplitude and distribute division over the low/high sum.

- [ ] **Step 4: Prove convergence by squeeze**

Use nonnegativity and the sum of the two normalized budget limits.

### Task 3: Balanced and canonical positive-width specializations

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualTargetAmplitudeTwoHeightStrip.lean`

**Interfaces:**
- Consumes: Task 2 convergence and stack 35 strict-margin existence.
- Produces: balanced feasibility transfer and a `beta > 2/3` actual-strip existence theorem.

- [ ] **Step 1: Add balanced feasibility wrapper**

From the stack 35 feasibility inequality, choose `alpha`, `gamma`, and
`epsilon`, then return `alpha > 1-beta` and normalized actual-strip
convergence.

- [ ] **Step 2: Choose a strict endpoint above canonical sigma**

Let the upper feasible endpoint be
`beta - balancedSlope sigma * (1-beta)`. Strict feasibility at `tau=sigma`
proves `sigma < upper`. Choose their midpoint as `tau`.

- [ ] **Step 3: Prove genuine strip existence**

Return `sigma`, `tau`, and `alpha` with:

```text
1/2 < sigma < tau < beta,
1-beta < alpha,
Tendsto normalizedActualStripMass atTop (nhds 0).
```

### Task 4: Contract, audit, and publication

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualTargetAmplitudeTwoHeightStripContract.lean`
- Create: `Test/ZeroDensityLayerBudgetActualTargetAmplitudeTwoHeightStripAxiomAudit.lean`

- [ ] **Step 1: Add contract checks for all public endpoints**

- [ ] **Step 2: Add axiom checks for shift, convergence, balanced, and canonical theorems**

- [ ] **Step 3: Run focused build and audit**

```bash
lake -Kjobs=1 build \
  PrimeNumberTheorem.ZeroDensityLayerBudgetActualTargetAmplitudeTwoHeightStrip \
  PrimeNumberTheorem.ZeroDensityLayerBudgetActualTargetAmplitudeTwoHeightStripContract
lake env lean \
  Test/ZeroDensityLayerBudgetActualTargetAmplitudeTwoHeightStripAxiomAudit.lean
```

- [ ] **Step 4: Commit documents and code separately, then open a draft PR based on stack 35**
