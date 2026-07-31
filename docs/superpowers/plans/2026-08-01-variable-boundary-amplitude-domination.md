# Variable-Boundary Amplitude Domination Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Transfer fixed-exponent natural-point remainder decay to a pointwise larger moving-exponent target amplitude.

**Architecture:** Add one generic monotonicity theorem for normalized natural-point remainders, then specialize it using monotonicity of `Real.rpow` on bases at least one. Keep the public contract and axiom audit isolated from explicit-formula or oscillation assembly.

**Tech Stack:** Lean 4, Mathlib filters and real powers, repository contract and axiom-audit conventions.

## Global Constraints

- Modify only `ZeroDensityLayerBudget*.lean`, matching audits, and this task's documentation.
- Do not modify `ZeroForcedOscillationComplementaryBound.lean` or VK-edge files.
- Do not claim a moving-package witness, unconditional `Omega_+-`, or RH.
- Run at most one Lean process at a time.

---

### Task 1: Generic amplitude domination

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetVariableBoundaryAmplitudeDomination.lean`

**Interfaces:**
- Consumes: `NaturalPointTargetAmplitudeNegligible amplitude remainder`.
- Produces: `NaturalPointTargetAmplitudeNegligible.mono_amplitude`.

- [ ] **Step 1:** State eventual positivity and eventual denominator-order hypotheses.
- [ ] **Step 2:** Bound the larger-denominator normalized remainder between zero and the known normalized remainder.
- [ ] **Step 3:** Apply squeeze convergence at `atTop`.

### Task 2: Fixed-to-moving target powers

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetVariableBoundaryAmplitudeDomination.lean`

**Interfaces:**
- Consumes: eventual `beta0 <= beta m` and fixed-amplitude negligibility.
- Produces: `targetZeroPowerAmplitude_le_variableBoundaryTargetAmplitude` and `naturalPointTargetAmplitudeNegligible_variableBoundary_of_fixed`.

- [ ] **Step 1:** Use `Real.rpow_le_rpow_of_exponent_le` for natural bases at least one.
- [ ] **Step 2:** Establish eventual positivity of both target amplitudes.
- [ ] **Step 3:** Invoke the generic denominator-domination theorem.

### Task 3: Public contract and audit

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetVariableBoundaryAmplitudeDominationContract.lean`
- Create: `Test/ZeroDensityLayerBudgetVariableBoundaryAmplitudeDominationAxiomAudit.lean`

**Interfaces:**
- Consumes: the three stack103 public declarations.
- Produces: compile-time signature checks and printed axiom dependencies.

- [ ] **Step 1:** Add `#check` declarations to the contract.
- [ ] **Step 2:** Add `#print axioms` declarations to the audit.
- [ ] **Step 3:** Compile implementation, contract, and audit sequentially with the overlay.
- [ ] **Step 4:** Commit exact task paths and publish a bounded stacked PR.
