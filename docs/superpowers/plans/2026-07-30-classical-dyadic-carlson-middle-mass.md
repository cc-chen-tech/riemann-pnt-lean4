# Classical Dyadic Carlson Middle-Mass Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove that the classical admissible selected height has a
Carlson-controlled moving middle-zero mass tending to zero.

**Architecture:** Establish a strict subpolynomial-versus-polynomial height
margin, transfer the fixed low-strip decay by finset inclusion, and cover the
remaining high part with the existing automatic dyadic fixed-anchor mass.
Instantiate the classical moving width only at the final endpoint.

**Tech Stack:** Lean 4, Mathlib filters and real asymptotics, repository
explicit-formula and Carlson layer-budget modules.

## Global Constraints

- Modify only `ZeroDensityLayerBudget*` production files, their contracts,
  audits, and this task's documents.
- Do not modify `ZeroForcedOscillationComplementaryBound.lean`.
- Do not modify VK-edge modules.
- Do not claim complete PNT reassembly or an unconditional Omega theorem.
- Accept only `propext`, `Classical.choice`, and `Quot.sound`.

---

### Task 1: Height domination

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonMiddleMass.lean`

**Interfaces:**
- Consumes: `pintzCarlsonHeight`, the classical and polynomial unit-window
  selector certificates.
- Produces:
  `eventually_pintzCarlsonHeight_add_one_le_nat_rpow` and
  `eventually_selectedClassicalAdmissibleGoodHeight_le_selectedUniformGoodHeight`.

- [ ] Prove `pintzCarlsonHeight k m + 1 <= m^alpha` eventually.
- [ ] Derive eventual ordering of the selected heights without selector
  monotonicity.

### Task 2: Low-strip transfer

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonMiddleMass.lean`

**Interfaces:**
- Consumes: `mem_actualPositiveCarlsonStrip` and polynomial selected-height
  low-strip decay.
- Produces:
  `actualSelectedHeightSevenEighthsLowMass_mono` and
  `tendsto_actualSelectedClassicalAdmissibleSevenEighthsLowMass_zero`.

- [ ] Prove truncation-height monotonicity by finset inclusion.
- [ ] Squeeze the classical low-strip mass by the polynomial low-strip mass.

### Task 3: Dyadic middle-mass transfer

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonMiddleMass.lean`

**Interfaces:**
- Consumes: `mem_actualDyadicCarlsonMinimalFixedAnchorWindow` and
  `exists_constants_tendsto_actualDyadicCarlsonMinimalFixedAnchorMass_zero_automatic`.
- Produces:
  `actualSelectedHeightMovingCarlsonMiddleMass_le_low_add_dyadicFixedAnchor`,
  `tendsto_actualSelectedClassicalAdmissibleMovingMiddleMass_zero_of_dyadic`,
  and `exists_selectedClassicalAdmissibleDyadicCarlsonMiddleMassDecay`.

- [ ] Split the moving middle strip at real part `7/8`.
- [ ] Prove the high substrip is contained in the dyadic fixed-anchor window.
- [ ] Squeeze by the low-strip and fixed-anchor mass limits.
- [ ] Instantiate the canonical classical width and zero-free edge.

### Task 4: Contract and audit

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonMiddleMassContract.lean`
- Create: `Test/ZeroDensityLayerBudgetActualClassicalDyadicCarlsonMiddleMassAxiomAudit.lean`

**Interfaces:**
- Consumes: all public declarations from Tasks 1-3.
- Produces: exact type checks and the standalone axiom report.

- [ ] Build the production module and exact contract together.
- [ ] Run the standalone axiom audit.
- [ ] Confirm each endpoint has exactly the standard three axioms.

### Task 5: Publish the bounded stack node

**Files:**
- Create: `docs/superpowers/specs/2026-07-30-classical-dyadic-carlson-middle-mass-design.md`
- Create: `docs/superpowers/plans/2026-07-30-classical-dyadic-carlson-middle-mass.md`

**Interfaces:**
- Consumes: the verified theorem chain and audit output.
- Produces: a dedicated stack-19 branch and draft pull request.

- [ ] Commit the design certificate separately.
- [ ] Commit the Lean implementation, contract, and audit with exact staging.
- [ ] Push `research/pintz-carlson-stack-19-classical-pnt`.
- [ ] Open a draft PR against `research/pintz-carlson-stack-18-classical-gap`.
