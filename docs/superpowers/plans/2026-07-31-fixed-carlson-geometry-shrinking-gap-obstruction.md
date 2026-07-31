# Fixed Carlson Geometry Shrinking-Gap Obstruction Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove the exact logarithmic threshold for a shrinking-gap power envelope and show that the standard fixed-`sigma`, fixed-positive-`gamma` Carlson low-budget envelope cannot certify a cap converging to `beta`.

**Architecture:** A small arithmetic module defines the envelope, proves a sufficient exponential-margin limit and a non-decay theorem for fixed positive penalty, then specializes the penalty to `carlsonTwoHeightDensityExponent sigma * gamma`. A contract and focused axiom audit keep the claim surface auditable.

**Tech Stack:** Lean 4, Mathlib filters/order topology/real `rpow`, existing Carlson exponent definitions.

## Global Constraints

- Create only the three stack85 Lean files and stack85 documents.
- Do not modify any existing Lean file.
- State non-decay only for the power envelope, never for the actual Carlson mass.
- Keep the frozen complementary-bound file untracked and untouched.
- Use focused direct compilation and axiom audit; do not run a full repository build.

---

### Task 1: Test-first public interface

**Files:**
- Test temporarily: `/tmp/stack85_red.lean`

**Interfaces:**
- Produces a failing import/check before production code exists.

- [ ] **Step 1: Write and run the failing probe**

```lean
import PrimeNumberTheorem.ZeroDensityLayerBudgetShrinkingGapFixedGeometryObstruction
open PrimeNumberTheorem
#check tendsto_shrinkingGapPowerEnvelope_zero_of_logMargin
#check not_tendsto_fixedCarlsonLowPowerEnvelope_zero_of_cap_tendsto_target
```

Expected: failure because the new module `.olean` does not exist.

---

### Task 2: General shrinking-gap envelope arithmetic

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetShrinkingGapFixedGeometryObstruction.lean`

**Interfaces:**
- Consumes: Mathlib `Real.rpow_def_of_pos`, `Real.tendsto_exp_atBot`, filter eventuality, and `tendsto_order`.
- Produces: the general envelope, sufficient-margin theorem, and fixed-positive-penalty obstruction.

- [ ] **Step 1: Define the envelope**

```lean
def shrinkingGapPowerEnvelope
    (p beta : ℝ) (capTau : ℝ → ℝ) (x : ℝ) : ℝ :=
  x ^ (p + capTau x - beta)
```

- [ ] **Step 2: Prove the sufficient logarithmic margin theorem**

```lean
theorem tendsto_shrinkingGapPowerEnvelope_zero_of_logMargin
    {p beta : ℝ} {capTau : ℝ → ℝ}
    (hmargin : Tendsto
      (fun x => ((beta - capTau x) - p) * Real.log x)
      atTop atTop) :
    Tendsto (shrinkingGapPowerEnvelope p beta capTau)
      atTop (nhds 0)
```

Rewrite `rpow` eventually for `x > 0`; its exponential argument is the negative of the supplied margin. Compose negation with `Real.tendsto_exp_atBot`.

- [ ] **Step 3: Prove fixed-positive-penalty non-decay**

```lean
theorem not_tendsto_shrinkingGapPowerEnvelope_zero_of_fixedPositivePenalty
    {p beta : ℝ} {capTau : ℝ → ℝ}
    (hp : 0 < p)
    (hcap : Tendsto capTau atTop (nhds beta)) :
    ¬ Tendsto (shrinkingGapPowerEnvelope p beta capTau)
      atTop (nhds 0)
```

The exponent tends to `p`, hence is eventually nonnegative. For eventual `1 <= x`, apply `Real.one_le_rpow`; this contradicts the eventual strict upper bound `< 1` implied by convergence to zero.

---

### Task 3: Carlson fixed-geometry specialization

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetShrinkingGapFixedGeometryObstruction.lean`

**Interfaces:**
- Consumes: `carlsonTwoHeightDensityExponent sigma = 4 * sigma * (1 - sigma)`.
- Produces: positivity of the low penalty and the final method-obstruction theorem.

- [ ] **Step 1: Prove penalty positivity**

```lean
theorem fixedCarlsonLowPenalty_pos
    {sigma gamma : ℝ}
    (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1)
    (hgamma : 0 < gamma) :
    0 < carlsonTwoHeightDensityExponent sigma * gamma
```

Unfold the density exponent and discharge the strict inequalities with `positivity` or `nlinarith`.

- [ ] **Step 2: Specialize the obstruction**

```lean
theorem not_tendsto_fixedCarlsonLowPowerEnvelope_zero_of_cap_tendsto_target
    {beta sigma gamma : ℝ} {capTau : ℝ → ℝ}
    (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1)
    (hgamma : 0 < gamma)
    (hcap : Tendsto capTau atTop (nhds beta)) :
    ¬ Tendsto
      (shrinkingGapPowerEnvelope
        (carlsonTwoHeightDensityExponent sigma * gamma)
        beta capTau)
      atTop (nhds 0)
```

Apply Task 2 Step 3 with `fixedCarlsonLowPenalty_pos`.

---

### Task 4: Contract, audit, verification, and publication

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetShrinkingGapFixedGeometryObstructionContract.lean`
- Create: `Test/ZeroDensityLayerBudgetShrinkingGapFixedGeometryObstructionAxiomAudit.lean`

**Interfaces:**
- Produces public signature and axiom evidence for all four declarations.

- [ ] **Step 1: Add contract checks and axiom prints**

The contract checks `shrinkingGapPowerEnvelope` and all four theorems. The audit prints axioms for the three theorems.

- [ ] **Step 2: Compile and audit**

Directly compile the main module and contract into `.lake/build/lib/lean`, then run the focused audit. Expected: exit code `0` and only repository-allowlisted axioms.

- [ ] **Step 3: Commit and publish**

Commit the plan separately, then commit the three Lean files. Push `research/pintz-carlson-stack-85-fixed-geometry-shrinking-gap-obstruction` and open a Draft PR based on `research/pintz-carlson-stack-84-moving-extension-shrinking-gap`.
