# Actual Zero-Package Carlson Unnormalized Sign Alternative Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Convert the actual-package relative PNT sign alternative to the unnormalized centered Chebyshev error at exact `x^beta` scale.

**Architecture:** One facade invokes stack94, eliminates its sign disjunction, and applies the existing natural-to-real and relative-to-unnormalized transfer for the selected side.

**Tech Stack:** Lean 4, Mathlib real powers, existing PNT target-amplitude witness interfaces.

## Global Constraints

- Add only the new `ZeroDensityLayerBudgetActualZeroPackageCarlsonUnnormalizedSignAlternative*` files, matching audit, and docs.
- Preserve stack94 hypotheses and budget outputs exactly.
- Claim only conditional `Omega+ OR Omega-` at `x^beta` scale.

---

### Task 1: Unnormalized facade

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualZeroPackageCarlsonUnnormalizedSignAlternative.lean`

**Interfaces:**
- Consumes: stack94 sign alternative, `HasFarNaturalPointPositiveTargetAmplitudeWitness.toReal`, its negative analogue, and each unnormalized transfer theorem.
- Produces: `exists_actualZeroPackage_actualCarlsonHalfThresholdPNTUnnormalizedSignAlternative`.

- [ ] **Step 1:** invoke stack94 and retain all certificate fields.
- [ ] **Step 2:** eliminate the positive-or-negative natural witness.
- [ ] **Step 3:** convert the selected side to a real witness at `x^beta` scale.
- [ ] **Step 4:** repack the unchanged Carlson and PNT convergence certificate.

### Task 2: Contract and audit

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualZeroPackageCarlsonUnnormalizedSignAlternativeContract.lean`
- Create: `Test/ZeroDensityLayerBudgetActualZeroPackageCarlsonUnnormalizedSignAlternativeAxiomAudit.lean`

**Interfaces:**
- Consumes: the Task 1 theorem.
- Produces: a public type check and axiom report.

- [ ] **Step 1:** compile the main module directly with the local olean overlay.
- [ ] **Step 2:** compile the contract and audit serially.
- [ ] **Step 3:** confirm only repository-standard logical axioms occur.
- [ ] **Step 4:** commit docs and Lean code separately and publish a bounded draft PR based on stack94.
