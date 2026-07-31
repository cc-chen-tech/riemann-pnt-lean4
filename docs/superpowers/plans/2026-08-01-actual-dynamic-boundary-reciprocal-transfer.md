# Actual Dynamic-Boundary Reciprocal Transfer Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Install the reciprocal low-layer margin in the complete actual dynamic-boundary PNT upper and conditional lower transfer.

**Architecture:** A parallel transfer module replaces only the positive-tail input, then reuses exact explicit-formula decomposition, natural-point negligibility addition, package coefficient caps, and witness transfer. Separate contract and axiom-audit modules lock the result.

**Tech Stack:** Lean 4, Stack150 reciprocal low layer, existing dynamic-boundary explicit formula and witness transfer.

## Global Constraints

- Modify only `ZeroDensityLayerBudgetActualDynamicBoundaryReciprocalTransfer*.lean` and this stack's spec/plan files.
- Keep the old unit-slope transfer intact.
- Preserve all selected-height, right-edge, coefficient-cap, and visible-main witness boundaries.
- Do not claim RH or an unconditional Omega theorem.
- Compile serially with `nice -n 10` and the existing overlay.

---

### Task 1: Reassemble the explicit-formula residual

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualDynamicBoundaryReciprocalTransfer.lean`
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualDynamicBoundaryReciprocalTransferContract.lean`

**Interfaces:**
- Consumes: Stack150 positive-tail decay, real-tail decay, exact explicit-formula decomposition, and selected-height remainder certificate.
- Produces: reciprocal versions of signed-complement and explicit-formula residual negligibility.

- [ ] **Step 1: Combine reciprocal positive and existing real normalized tails.**

- [ ] **Step 2: Add closed-axis, contour, and complement negligible terms.**

- [ ] **Step 3: Rewrite the exact explicit formula to obtain residual negligibility.**

### Task 2: Propagate upper and witness transfers

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualDynamicBoundaryReciprocalTransfer.lean`

**Interfaces:**
- Consumes: residual negligibility, package coefficient cap, and main-witness transfer.
- Produces: reciprocal automatic upper, witness, bidirectional, and fully automatic facades.

- [ ] **Step 1: Feed the residual to the generic package-cap upper assembler.**

- [ ] **Step 2: Feed the same residual to the main-witness transfer.**

- [ ] **Step 3: Combine both conclusions and install the Carlson coefficient cap.**

### Task 3: Verify, audit, and publish Stack151

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualDynamicBoundaryReciprocalTransferAxiomAudit.lean`
- Create: `docs/superpowers/specs/2026-08-01-actual-dynamic-boundary-reciprocal-transfer-design.md`
- Create: `docs/superpowers/plans/2026-08-01-actual-dynamic-boundary-reciprocal-transfer.md`

**Interfaces:**
- Consumes: all public Stack151 theorems.
- Produces: an audited stacked draft PR based on Stack150.

- [ ] **Step 1: Compile implementation, contract, and audit serially through the overlay.**

Expected: all commands exit zero without warnings; audited theorems use only `propext`, `Classical.choice`, and `Quot.sound`.

- [ ] **Step 2: Commit docs and Lean files separately, push, and create a draft PR based on Stack150.**
