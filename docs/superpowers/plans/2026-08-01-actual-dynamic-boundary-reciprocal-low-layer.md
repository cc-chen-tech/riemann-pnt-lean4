# Actual Dynamic-Boundary Reciprocal Low-Layer Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the dynamic low layer's `O(H log H)` count loss by the proved `O(log^2 H)` reciprocal-zero mass and remove the full `alpha` power cost.

**Architecture:** A new parallel module first proves a generic reciprocal-mass layer bound, then derives an explicit normalized log-power majorant and its decay, and finally plugs the improved low layer into the existing canonical positive-tail decomposition. Existing transfer modules remain unchanged.

**Tech Stack:** Lean 4, Mathlib finite sums and real asymptotics, global reciprocal-zero multiplicity, existing dynamic-boundary two-strip split.

## Global Constraints

- Modify only `ZeroDensityLayerBudgetActualDynamicBoundaryReciprocalLowLayer*.lean` and this stack's spec/plan files.
- Do not edit the old automatic low-layer theorem or any protected reciprocal-zero file.
- Preserve the existing high Carlson layer and right-edge hypotheses.
- Do not claim visible-main witnesses, RH, or an unconditional Omega theorem.
- Compile serially with `nice -n 10` and the existing overlay.

---

### Task 1: Prove the generic reciprocal layer bound

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualDynamicBoundaryReciprocalLowLayer.lean`
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualDynamicBoundaryReciprocalLowLayerContract.lean`

**Interfaces:**
- Consumes: `norm_pntRelativeZeroContribution_eq_multiplicity_mul_norm`, `norm_pntRelativeSimpleZeroKernel_eq`, and `globalReciprocalZeroMultiplicity`.
- Produces: `PositiveZeroOutsideClusterBucketInput.norm_layer_sum_le_rpow_mul_globalReciprocal`.

- [ ] **Step 1: Prove every outside-cluster layer is a subset of `nontrivialZerosFinset T`.**

- [ ] **Step 2: Bound each multiplicity-weighted kernel while preserving `1 / |rho|`.**

- [ ] **Step 3: Compare the finite reciprocal mass to the global truncation mass.**

### Task 2: Remove the polynomial power cost

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualDynamicBoundaryReciprocalLowLayer.lean`

**Interfaces:**
- Consumes: `exists_globalReciprocalZeroMultiplicity_le_log_sq` and the selected-height polynomial ceiling.
- Produces: `tendsto_actualReciprocalLowNormalizedLogPowerMajorant_zero` and `actualDynamicBoundaryCanonicalLowNormalizedSum_tendsto_zero_reciprocal`.

- [ ] **Step 1: Define the explicit `x^(sigma-beta) log^8 x` majorant.**

- [ ] **Step 2: Prove its decay by squaring the existing `rpow * log^4` decay theorem at half exponent.**

- [ ] **Step 3: Bound `log(H + 6)^2` by the polynomial-height log majorant.**

- [ ] **Step 4: Normalize the pointwise reciprocal bound and prove low-layer convergence under `sigma - beta + epsilon < 0`.**

### Task 3: Reassemble the positive tail and publish Stack150

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualDynamicBoundaryReciprocalLowLayerAxiomAudit.lean`
- Create: `docs/superpowers/specs/2026-08-01-actual-dynamic-boundary-reciprocal-low-layer-design.md`
- Create: `docs/superpowers/plans/2026-08-01-actual-dynamic-boundary-reciprocal-low-layer.md`

**Interfaces:**
- Consumes: `actualDynamicBoundaryPositiveNormalizedSum_tendsto_zero` and the existing high Carlson layer.
- Produces: `actualDynamicBoundaryCanonicalPositiveNormalizedSum_tendsto_zero_reciprocal` and a bounded stacked draft PR based on Stack149.

- [ ] **Step 1: Feed the reciprocal low-layer convergence into the existing positive-tail split.**

- [ ] **Step 2: Compile implementation, contract, and audit serially through the overlay.**

Expected: all commands exit zero without warnings; audited theorems use only `propext`, `Classical.choice`, and `Quot.sound`.

- [ ] **Step 3: Commit docs and Lean files separately, push, and create a draft PR based on Stack149.**
