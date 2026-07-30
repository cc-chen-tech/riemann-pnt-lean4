# Half-Sharp Target-Amplitude Barrier Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove that the attained half-sharp full-PNT majorant is too large,
after fixed-power normalization, to supply the existing reverse-cluster
hypothesis.

**Architecture:** Reduce the normalized half Carlson kernel to the existing
subpolynomial contour barrier, then lift divergence from that kernel summand to
the complete closed-form PNT majorant.

**Tech Stack:** Lean 4, Mathlib filters at infinity, repository Carlson and
target-amplitude transfer modules.

## Global Constraints

- State a majorant limitation, not a lower bound for the actual error.
- Keep `beta < 1` fixed.
- Do not modify complementary-zero, VK-edge, or existing unified-transfer
  files.
- Audit all public divergence and non-eventual-bound endpoints.

---

### Task 1: Normalized half Carlson kernel

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonHalfSharpTargetAmplitudeBarrier.lean`

**Interfaces:**
- Consumes: the half-sharp Carlson majorant and generic target-amplitude
  contour barrier.
- Produces: exact ratio identity and divergence to `atTop`.

- [ ] Define the normalized kernel ratio.
- [ ] Rewrite it as constant times polynomial times the contour ratio.
- [ ] Prove divergence using the polynomial lower bound by one.

### Task 2: Complete majorant barrier

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonHalfSharpTargetAmplitudeBarrier.lean`

**Interfaces:**
- Consumes: nonnegativity of all full-PNT majorant terms.
- Produces: full-majorant ratio divergence and failure of every fixed
  coefficient bound.

- [ ] Prove the Carlson kernel is bounded above by the full majorant.
- [ ] Transfer divergence through positive target-amplitude division.
- [ ] Derive the non-eventual `q * A_beta` theorem.

### Task 3: Contract, audit, and publication

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonHalfSharpTargetAmplitudeBarrierContract.lean`
- Create: `Test/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonHalfSharpTargetAmplitudeBarrierAxiomAudit.lean`
- Create: `docs/superpowers/specs/2026-07-31-half-sharp-target-amplitude-barrier-design.md`
- Create: `docs/superpowers/plans/2026-07-31-half-sharp-target-amplitude-barrier.md`

**Interfaces:**
- Consumes: all stack 34 barrier declarations.
- Produces: focused build, axiom audit, two commits, and a draft stacked PR.

- [ ] Build the main module and contract with `lake -Kjobs=1 build`.
- [ ] Run the dedicated audit with `lake env lean`.
- [ ] Commit docs separately from Lean.
- [ ] Push `research/pintz-carlson-stack-34-half-sharp-target-amplitude-barrier`.
- [ ] Open a draft PR against
  `research/pintz-carlson-stack-33-half-sharp-full-pnt`.
