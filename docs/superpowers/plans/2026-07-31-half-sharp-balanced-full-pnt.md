# Half-Sharp Balanced Full-PNT Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Propagate the attained Carlson half endpoint to an actual
closed-form natural-point PNT error bound.

**Architecture:** Convert the compensated stack 32 coefficient to the stack 31
theta coefficient at `theta = 1 / 2`, then reuse the existing theta tail and
explicit-formula transfer hierarchy.

**Tech Stack:** Lean 4, Mathlib filters, repository dynamic zero-layer and
explicit-formula modules.

## Global Constraints

- Do not modify earlier stack files.
- Do not modify complementary-zero or VK-edge modules.
- Preserve `halfRate = gapRate / 2 = balancedRate / 4`.
- Bound the actual `relativeChebyshevPsi0Error`, not an abstract kernel.

---

### Task 1: Moving-mass bridge

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonHalfSharpFullPNT.lean`

**Interfaces:**
- Consumes: stack 32 compensated fixed-anchor mass.
- Produces:
  `exists_selectedClassicalAdmissibleDyadicCarlsonHalfQuantitativeMassMajorant_of_zeroFree`.

- [ ] Set `D = C * exp(gapRate / 2)`.
- [ ] Convert the half majorant to the theta majorant at `1 / 2`.
- [ ] Lift the fixed-anchor bound to selected moving middle and strip masses.

### Task 2: Complete explicit-formula assembly

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonHalfSharpFullPNT.lean`

**Interfaces:**
- Consumes: stack 31 theta tail and explicit-formula transfer interfaces.
- Produces:
  `exists_selectedBalancedClassicalAdmissibleDyadicCarlsonHalfClosedFormFullPNTErrorMajorant`.

- [ ] Assemble the positive and full zero tails.
- [ ] Apply closed real-axis and contour remainder bounds.
- [ ] Record both exact half-rate identities and strict improvement.

### Task 3: Contract, audit, and publication

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonHalfSharpFullPNTContract.lean`
- Create: `Test/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonHalfSharpFullPNTAxiomAudit.lean`
- Create: `docs/superpowers/specs/2026-07-31-half-sharp-balanced-full-pnt-design.md`
- Create: `docs/superpowers/plans/2026-07-31-half-sharp-balanced-full-pnt.md`

**Interfaces:**
- Consumes: the full stack 33 endpoint.
- Produces: focused verification, two commits, and a draft stacked PR.

- [ ] Run:

```bash
lake -Kjobs=1 build \
  PrimeNumberTheorem.ZeroDensityLayerBudgetActualClassicalDyadicCarlsonHalfSharpFullPNT \
  PrimeNumberTheorem.ZeroDensityLayerBudgetActualClassicalDyadicCarlsonHalfSharpFullPNTContract
```

- [ ] Run:

```bash
lake env lean \
  Test/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonHalfSharpFullPNTAxiomAudit.lean
```

- [ ] Commit docs separately from Lean.
- [ ] Push `research/pintz-carlson-stack-33-half-sharp-full-pnt`.
- [ ] Open a draft PR against
  `research/pintz-carlson-stack-32-half-sharp-carlson-rate`.
