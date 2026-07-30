# Theta-Sharp Balanced Full-PNT Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Carry every fixed Carlson exponent `theta * gapRate`, for
`1 / 4 < theta < 1 / 2`, through the complete natural-point explicit formula.

**Architecture:** Add one parallel Lean module importing the theta-sharp
fixed-anchor result. Reuse all non-Carlson components and define only the four
majorants whose formulas contain the improved Carlson term.

**Tech Stack:** Lean 4, Mathlib filters and limits, repository explicit-formula
and Carlson zero-density modules.

## Global Constraints

- Do not modify `ZeroForcedOscillationComplementaryBound.lean`.
- Do not modify VK-edge modules.
- Preserve the exact exponent `theta * gapRate`.
- Require the strict range `1 / 4 < theta < 1 / 2`.
- Stage only files with the stack 31 theta-sharp full-PNT prefix and its docs.

---

### Task 1: Theta majorant hierarchy

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonThetaSharpFullPNT.lean`

**Interfaces:**
- Consumes: `classicalDyadicCarlsonThetaSqrtLogMajorant` and its convergence.
- Produces: theta middle, positive-tail, full-zero-tail, and closed-form
  full-PNT majorants with convergence lemmas.

- [ ] Define each majorant by replacing every old Carlson square-root-log term
  with `classicalDyadicCarlsonThetaSqrtLogMajorant D rate theta`.
- [ ] Prove convergence by adding the existing component limits.

### Task 2: Explicit-formula transfer

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonThetaSharpFullPNT.lean`

**Interfaces:**
- Consumes: an eventual theta full-zero-tail bound and the two existing
  remainder bounds.
- Produces:
  `eventually_abs_relativeChebyshevPsi0Error_le_thetaClosedFormFullPNTMajorant`.

- [ ] Expand the dynamic explicit formula.
- [ ] Bound the real part of the finite zero sum by its norm.
- [ ] combine the zero, real-axis, and contour bounds into the theta
  closed-form majorant.

### Task 3: Balanced theta endpoint

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonThetaSharpFullPNT.lean`

**Interfaces:**
- Consumes: balanced truncation, theta fixed-anchor mass, moving-layer
  comparison, and explicit-formula transfer.
- Produces:
  `exists_selectedBalancedClassicalAdmissibleDyadicCarlsonThetaClosedFormFullPNTErrorMajorant`.

- [ ] Lift the theta fixed-anchor estimate to moving middle and strip masses.
- [ ] Assemble positive and full zero tails.
- [ ] Apply the explicit-formula transfer.
- [ ] Record `theta * gapRate`, strict improvement over the old rate, and the
  strict upper limit at one quarter of the balanced height rate.

### Task 4: Contract and axiom audit

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonThetaSharpFullPNTContract.lean`
- Create: `Test/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonThetaSharpFullPNTAxiomAudit.lean`

**Interfaces:**
- Consumes: all public stack 31 declarations.
- Produces: compile-time API checks and printed axiom dependencies.

- [ ] Add `#check` entries for all public definitions and theorem endpoints.
- [ ] Add `#print axioms` entries for the transfer and convergence endpoints.

### Task 5: Verification and publication

**Files:**
- Create: `docs/superpowers/specs/2026-07-31-theta-sharp-balanced-full-pnt-design.md`
- Create: `docs/superpowers/plans/2026-07-31-theta-sharp-balanced-full-pnt.md`

**Interfaces:**
- Consumes: the completed Lean implementation.
- Produces: a two-commit stack 31 branch and a draft PR based on stack 30.

- [ ] Run:

```bash
lake -Kjobs=1 build \
  PrimeNumberTheorem.ZeroDensityLayerBudgetActualClassicalDyadicCarlsonThetaSharpFullPNT \
  PrimeNumberTheorem.ZeroDensityLayerBudgetActualClassicalDyadicCarlsonThetaSharpFullPNTContract
```

- [ ] Run:

```bash
lake env lean \
  Test/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonThetaSharpFullPNTAxiomAudit.lean
```

- [ ] Commit docs separately from Lean implementation.
- [ ] Push `research/pintz-carlson-stack-31-theta-sharp-full-pnt`.
- [ ] Open a draft PR against
  `research/pintz-carlson-stack-30-theta-sharp-carlson-rate`.
