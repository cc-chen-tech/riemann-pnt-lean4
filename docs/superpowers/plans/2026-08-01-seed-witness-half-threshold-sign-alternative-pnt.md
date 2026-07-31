# Seed-Witness Half-Threshold Sign-Alternative PNT Transfer Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Transfer one persistent finite-seed sign, including the sign obtained from an unsigned witness, to the actual relative PNT error at the canonical half-threshold coefficient.

**Architecture:** Add one density/transfer module above stacks 90-92. It exposes one-sided Carlson-boundary adapters, a shared finite-seed sign-disjunction theorem, and an unsigned-seed corollary.

**Tech Stack:** Lean 4, Mathlib filters, existing Pintz-Carlson explicit-formula interfaces.

## Global Constraints

- Modify only `ZeroDensityLayerBudget*` modules, the matching audit, and task docs.
- Do not modify the protected complementary-bound file, Sharp pi/2 modules, or VK-edge modules.
- State only `Omega+ OR Omega-`; do not claim simultaneous signs or RH.

---

### Task 1: One-sided Carlson-boundary adapters

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualCarlsonSeedWitnessHalfThresholdSignAlternativePNTTransfer.lean`

**Interfaces:**
- Consumes: the automatic Carlson-boundary residual estimate and each one-sided `transfer_eventually_sub_lt` lemma.
- Produces: `selectedUniformGoodHeightActualCarlsonBalancedBoundaryPNTSharpPositiveTransfer_automatic` and its negative analogue.

- [ ] **Step 1:** Define the positive adapter using loss `c - q`.
- [ ] **Step 2:** Define the negative adapter using the identical residual certificate.
- [ ] **Step 3:** Compile the module directly with the local olean overlay.

### Task 2: Seed sign alternative and unsigned corollary

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualCarlsonSeedWitnessHalfThresholdSignAlternativePNTTransferContract.lean`
- Create: `Test/ZeroDensityLayerBudgetActualCarlsonSeedWitnessHalfThresholdSignAlternativePNTTransferAxiomAudit.lean`

**Interfaces:**
- Consumes: stack90 target-line capture budgets, finite seed extension, stack92 `signAlternative`, and Task 1 adapters.
- Produces: `exists_seedWitness_actualCarlsonHalfThresholdSignAlternativePNTTransfer` and `exists_seedWitness_actualCarlsonHalfThresholdUnsignedPNTSignAlternativeTransfer`.

- [ ] **Step 1:** Construct the finite target-line extension before splitting on the sign disjunction.
- [ ] **Step 2:** Transfer the selected sign at coefficient `(c - loss) / 2`.
- [ ] **Step 3:** Derive the unsigned-seed corollary with `hseedUnsigned.signAlternative`.
- [ ] **Step 4:** Compile the contract and axiom audit and inspect the printed dependencies.
- [ ] **Step 5:** Commit the design separately from the Lean implementation and publish a bounded draft PR based on stack92.
