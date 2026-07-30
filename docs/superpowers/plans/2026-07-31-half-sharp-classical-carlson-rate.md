# Half-Sharp Classical Carlson Rate Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Attain the Carlson endpoint `theta = 1 / 2` by retaining the exact
constant compensation `exp(rate / 2)`.

**Architecture:** Add one endpoint module on top of stack 30. Reuse the theta
majorant at `theta = 1 / 2` with a compensated coefficient, then transfer the
coarse estimate to the actual fixed-anchor multiplicity mass.

**Tech Stack:** Lean 4, Mathlib real logarithms and filters, repository Carlson
dynamic-layer interfaces.

## Global Constraints

- Do not modify complementary-zero or VK-edge modules.
- Do not change the dyadic layer schedule or zero-density hypothesis.
- Retain the exact compensation `exp(rate / 2)`.
- Keep full-PNT propagation out of this PR.

---

### Task 1: Compensated endpoint inequality

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonHalfSharpRate.lean`

**Interfaces:**
- Consumes: the stack 30 theta majorant and layered coarse Carlson ratio.
- Produces:
  `eventually_carlsonDynamicGapLayeredCoarseLogPowerRatio_le_halfMajorant`.

- [ ] Define the compensated half majorant.
- [ ] Prove the exact rational identity with nonnegative remainder
  `rate / (2 * (1 + s))`.
- [ ] Use it in the logarithmic exponent comparison.

### Task 2: Actual fixed-anchor transfer

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonHalfSharpRate.lean`

**Interfaces:**
- Consumes: actual fixed-anchor mass bounded by the layered coarse ratio.
- Produces:
  `exists_classicalAdmissibleDyadicCarlsonHalfQuantitativeFixedAnchorMajorant`.

- [ ] Chain the existing multiplicity-aware fixed-anchor estimate into the
  compensated majorant.
- [ ] Prove convergence to zero.
- [ ] Record the exact balanced rate and strict improvement over the old rate.

### Task 3: Contract, audit, and publication

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonHalfSharpRateContract.lean`
- Create: `Test/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonHalfSharpRateAxiomAudit.lean`
- Create: `docs/superpowers/specs/2026-07-31-half-sharp-classical-carlson-rate-design.md`
- Create: `docs/superpowers/plans/2026-07-31-half-sharp-classical-carlson-rate.md`

**Interfaces:**
- Consumes: all stack 32 declarations.
- Produces: a focused build, standard axiom audit, two commits, and a draft PR.

- [ ] Run:

```bash
lake -Kjobs=1 build \
  PrimeNumberTheorem.ZeroDensityLayerBudgetActualClassicalDyadicCarlsonHalfSharpRate \
  PrimeNumberTheorem.ZeroDensityLayerBudgetActualClassicalDyadicCarlsonHalfSharpRateContract
```

- [ ] Run:

```bash
lake env lean \
  Test/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonHalfSharpRateAxiomAudit.lean
```

- [ ] Commit docs separately from Lean.
- [ ] Push `research/pintz-carlson-stack-32-half-sharp-carlson-rate`.
- [ ] Open a draft PR against
  `research/pintz-carlson-stack-31-theta-sharp-full-pnt`.
