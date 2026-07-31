# Finite-Switching Remainder and Envelope Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove that the Stack119 pointwise optimizer inherits actual natural-point remainder and visible-zero-envelope certificates from its finite certified candidate family.

**Architecture:** First prove a generic finite-switching remainder lemma by squeezing against a finite sum. Then transfer the existing selected-good-height certificate to each regularized candidate by eventual equality. Finally instantiate the switching lemma and the Stack119 generic witness for the optimized schedule.

**Tech Stack:** Lean 4, Mathlib filters and finite sums, Stack119 certified optimizer, actual selected-height remainder bridge, Stack118 zero-free-envelope predicate.

## Global Constraints

- Create only one new `ZeroDensityLayerBudget*` implementation module and matching contract/audit files.
- Do not modify protected complementary-zero, VK-edge, or Sharp oscillation files.
- Use one low-priority overlay build process.
- Keep unconditional Omega and RH outside the claim boundary.

---

### Task 1: Generic finite-switching remainder stability

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualPintzCertifiedGoodHeightRemainderEnvelopeTransfer.lean`

**Interfaces:**
- Consumes: `ActualSelectedHeightNaturalPointRemainderCertificate` and target-amplitude positivity.
- Produces: `actualSelectedHeightNaturalPointRemainderCertificate_of_finite_switching`.

- [ ] Prove convergence of the finite sum of normalized candidate remainders.
- [ ] Recover the active candidate at each natural sample.
- [ ] Squeeze the optimized normalized remainder between zero and the finite sum.

### Task 2: Stack119 optimizer instantiations

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualPintzCertifiedGoodHeightRemainderEnvelopeTransfer.lean`

**Interfaces:**
- Produces: candidate and optimizer actual remainder certificates plus optimized visible-zero-envelope inheritance.

- [ ] Transfer the selected uniform good-height remainder certificate to the regularized candidate by eventual congruence.
- [ ] Apply finite switching using `actualPintzCertifiedOptimalHeight_eq_candidate`.
- [ ] Rewrite positive-zero finset membership through the same optimizer witness to inherit `IsNaturalPositiveZeroFreeEnvelope`.

### Task 3: Contract, audit, and bounded PR

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualPintzCertifiedGoodHeightRemainderEnvelopeTransferContract.lean`
- Create: `Test/ZeroDensityLayerBudgetActualPintzCertifiedGoodHeightRemainderEnvelopeTransferAxiomAudit.lean`

- [ ] Add public `#check` declarations for all three transfer layers.
- [ ] Audit the generic switching theorem and both optimizer certificates.
- [ ] Compile implementation, contract, and audit through the overlay.
- [ ] Commit exact Stack120 files, push, and open a draft PR based on Stack119.
