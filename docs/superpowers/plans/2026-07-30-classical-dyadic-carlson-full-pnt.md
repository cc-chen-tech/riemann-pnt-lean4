# Classical Dyadic Carlson Full-PNT Transfer Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Assemble a complete Carlson/dyadic ordinary relative-PNT transfer at
the classical admissible selected height.

**Architecture:** Prove real-variable subpolynomial height domination and
cofinality, close every component of the finite zero tail, construct the
actual natural-point remainder certificate, and expose one final endpoint
that retains every intermediate certificate.

**Tech Stack:** Lean 4, Mathlib filters and finite sums, repository Carlson
layer budgets and multiplicity-aware explicit formula.

## Global Constraints

- Add only `ZeroDensityLayerBudget*` production/contract/audit files and task documents.
- Do not modify `ZeroForcedOscillationComplementaryBound.lean` or VK-edge files.
- Preserve Carlson/dyadic hypotheses in the final endpoint.
- Do not claim an Omega theorem, optimal PNT error rate, new density theorem, or RH.
- Accept only `propext`, `Classical.choice`, and `Quot.sound`.

---

### Task 1: Real height envelope

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonFullPNTTransfer.lean`

**Interfaces:**
- Produces real height margin, cofinality, and polynomial-ceiling theorems.

- [ ] Prove `pintzCarlsonHeight k x + 1 <= x^alpha` eventually.
- [ ] Prove the classical selected height tends to infinity.
- [ ] Prove it is eventually below every positive polynomial height.

### Task 2: Complete zero-tail decay

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonFullPNTTransfer.lean`

**Interfaces:**
- Consumes the stack-19 middle-mass endpoint and generic critical/real tail machinery.
- Produces critical-half, right-strip, positive-tail, and full-tail limits.

- [ ] Instantiate the generic critical-half estimate.
- [ ] Generalize real-ordinate decay to every cofinal height.
- [ ] Embed the moving right strip into the dyadic fixed-anchor window.
- [ ] Prove the classical width is eventually at most `1/16`.
- [ ] Assemble positive and complete finite zero-tail decay.

### Task 3: Actual remainder certificate and PNT

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonFullPNTTransfer.lean`

**Interfaces:**
- Consumes the classical truncated contour certificate and complete zero-tail limit.
- Produces the actual remainder certificate and final Carlson full-PNT endpoint.

- [ ] Bound the actual relative remainder by contour plus closed-log terms.
- [ ] Prove the displayed upper bound tends to zero.
- [ ] Construct `ActualSelectedHeightNaturalPointRemainderCertificate 1 H`.
- [ ] Apply the generic explicit-formula assembler.

### Task 4: Contract, audit, and publication

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonFullPNTTransferContract.lean`
- Create: `Test/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonFullPNTTransferAxiomAudit.lean`
- Create: `docs/superpowers/specs/2026-07-30-classical-dyadic-carlson-full-pnt-design.md`
- Create: `docs/superpowers/plans/2026-07-30-classical-dyadic-carlson-full-pnt.md`

**Interfaces:**
- Produces exact type evidence, axiom evidence, and a bounded stack-20 PR.

- [ ] Build production and contract together.
- [ ] Run the standalone axiom audit.
- [ ] Commit design and implementation separately with exact staging.
- [ ] Push `research/pintz-carlson-stack-20-classical-full-pnt`.
- [ ] Open a draft PR against `research/pintz-carlson-stack-19-classical-pnt`.
