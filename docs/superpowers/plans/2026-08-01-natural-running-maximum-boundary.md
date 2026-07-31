# Natural Running-Maximum Zero Boundary Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Construct a canonical sampled-monotone moving zero boundary and feed it into the canonical-good-height unified upper/signed-Omega theorem.

**Architecture:** A finite pointwise bottleneck bounds current visible zeros. A recursive running maximum adds history and a fixed lower anchor. A floor extension supplies the framework's real-valued exponent while preserving exact natural samples.

**Tech Stack:** Lean 4, Mathlib Finsets and `Nat.floor`, repository zeta-zero Finsets and variable-boundary transfer modules.

## Global Constraints

- Modify only `ZeroDensityLayerBudget*`, matching contract/audit files, and task documents.
- Do not touch `ZeroForcedOscillationComplementaryBound.lean` or Sharp/VK-edge files.
- Preserve `m^(beta(m)-1)` and `x^(beta(x))` exactly.
- Do not hide or claim the signed anti-cancellation witnesses.
- Do not claim unconditional Omega or RH.

---

### Task 1: Pointwise visible-zero bottleneck

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetVariableBoundaryNaturalRunningMaximumUnifiedUpperSignedOmega.lean`

**Interfaces:**
- Consumes: `positiveNontrivialZerosFinset` and `mem_positiveNontrivialZerosFinset`.
- Produces: `visiblePositiveZeroRealPartBottleneck` and `visiblePositiveZero_re_le_bottleneck`.

- [ ] Define the inserted-zero `Finset.max'` bottleneck.
- [ ] Prove every currently visible positive zero lies below it.

### Task 2: Recursive natural running maximum

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetVariableBoundaryNaturalRunningMaximumUnifiedUpperSignedOmega.lean`

**Interfaces:**
- Consumes: Task 1 bottleneck.
- Produces: natural and real running-boundary definitions, global lower anchor, sampled monotonicity, and indexed visible right edge.

- [ ] Define the recursive running maximum from `beta0`.
- [ ] Prove the lower anchor by induction.
- [ ] Prove successor growth and sampled monotonicity.
- [ ] Define the floor extension and prove its natural-cast evaluation.
- [ ] Prove the indexed visible right edge using the current bottleneck.

### Task 3: Unified facade, contract, and audit

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetVariableBoundaryNaturalRunningMaximumUnifiedUpperSignedOmega.lean`
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetVariableBoundaryNaturalRunningMaximumUnifiedUpperSignedOmegaContract.lean`
- Create: `Test/ZeroDensityLayerBudgetVariableBoundaryNaturalRunningMaximumUnifiedUpperSignedOmegaAxiomAudit.lean`

**Interfaces:**
- Consumes: Stack 113 and Tasks 1-2.
- Produces: `actualNaturalRunningMaximumBoundaryCanonicalGoodHeightUnifiedUpperSignedOmega`.

- [ ] State the Stack 113 conclusion with the constructed boundary substituted.
- [ ] Discharge lower-anchor, sampled-monotonicity, and indexed right-edge inputs automatically.
- [ ] Add `#check` contract lines for all public declarations.
- [ ] Add `#print axioms` lines for the core lemmas and final theorem.
- [ ] Compile the three targets sequentially with the overlay.
- [ ] Stage exactly the three Lean files, commit, push, and open a draft PR based on Stack 114.
