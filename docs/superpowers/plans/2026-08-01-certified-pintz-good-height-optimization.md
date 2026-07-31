# Certified Pintz Good-Height Optimization Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Construct a pointwise finite-grid optimizer whose candidates are actual uniform good heights and whose selected schedule retains the exact truncated explicit-formula certificate.

**Architecture:** A finite family of `UniformNaturalPointGoodHeightSelection` values with one common remainder constant generates an everywhere-positive dynamic grid. The existing `dynamicFiniteGridOptimalHeight` selects the cost minimizer. Membership in the image grid recovers a witnessing selector, which transfers interval, good-height, exact-certificate, and generic pointwise properties to the selected schedule.

**Tech Stack:** Lean 4, Mathlib filters and finite sets, existing `ZeroDensityLayerBudget` optimization and actual good-height modules.

## Global Constraints

- Modify only `ZeroDensityLayerBudget*` modules, matching contract/audit files, and this task's documents.
- Do not touch `ZeroForcedOscillationComplementaryBound.lean`, VK-edge modules, or Sharp oscillation modules.
- Use one low-priority Lean process and direct overlay builds.
- Do not claim unconditional signed Omega or RH.

---

### Task 1: Certified candidate family and dynamic grid

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualPintzCertifiedGoodHeightOptimization.lean`

**Interfaces:**
- Consumes: `UniformNaturalPointGoodHeightSelection`, `selectedUniformGoodHeight`, `DynamicFiniteHeightGrid`, and `dynamicFiniteGridOptimalHeight`.
- Produces: `ActualPintzGoodHeightCandidateFamily`, `actualPintzCandidateHeight`, and `actualPintzCertifiedDynamicGrid`.

- [ ] **Step 1:** Define a finite nonempty selector family with `commonConstant` and `constant_eq`.
- [ ] **Step 2:** Define the regularized candidate height, using the selected good height when `9 <= x ^ alpha` and `8` otherwise.
- [ ] **Step 3:** Build the finite image grid and prove every member is positive.
- [ ] **Step 4:** Use `tendsto_rpow_atTop` to construct a regularized lower envelope tending to infinity and prove it lies below every candidate.

### Task 2: Optimizer inheritance chain

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualPintzCertifiedGoodHeightOptimization.lean`

**Interfaces:**
- Consumes: `actualPintzCertifiedDynamicGrid`.
- Produces: `actualPintzCertifiedOptimalHeight`, exact family cost optimality, optimizer witness recovery, eventual interval and good-height theorems, divergence, exact natural-point certificate recovery, and generic property inheritance.

- [ ] **Step 1:** Define `actualPintzCertifiedOptimalHeight` via `dynamicFiniteGridOptimalHeight`.
- [ ] **Step 2:** Recover an index whose certified candidate equals the selected optimizer and prove exact cost optimality against each family member.
- [ ] **Step 3:** Prove eventual membership in `[x ^ alpha - 1, x ^ alpha]`, eventual analytic good-height status, and convergence to infinity.
- [ ] **Step 4:** For `m >= 3` and admissible polynomial base, recover a `TruncatedPNTErrorCertificate` at exactly the optimized height, rewriting the remainder constant to `commonConstant`.
- [ ] **Step 5:** Prove a generic pointwise-property inheritance theorem for later zero-free-envelope instantiation.

### Task 3: Public contract and axiom audit

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualPintzCertifiedGoodHeightOptimizationContract.lean`
- Create: `Test/ZeroDensityLayerBudgetActualPintzCertifiedGoodHeightOptimizationAxiomAudit.lean`

**Interfaces:**
- Consumes: public Stack119 declarations.
- Produces: compile-time signature checks and axiom reports for the central inheritance theorems.

- [ ] **Step 1:** Add `#check` declarations for the family, grid, optimizer, cost optimality, eventual good-height, divergence, exact certificate, and property inheritance.
- [ ] **Step 2:** Add `#print axioms` for dynamic-grid construction, exact certificate recovery, and generic property inheritance.
- [ ] **Step 3:** Build the implementation, contract, and audit directly through the overlay with `nice -n 10` and `-Kjobs=1`.
- [ ] **Step 4:** Commit only the three Stack119 Lean files and the implementation plan.
