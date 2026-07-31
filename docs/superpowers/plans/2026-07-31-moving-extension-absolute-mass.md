# Moving Extension Absolute-Mass Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove a cancellation-free Carlson majorant for the moving right-edge extension and use a genuine outside-seed gap to obtain an automatic actual signed PNT witness at coefficient `c / 4`.

**Architecture:** Replace signed outside-tail norms by sums of term norms, prove positive mass decay with the selected two-height Carlson split, restore negative mass by conjugation, handle the finite real slice termwise, and feed the resulting moving-extension negligibility into stack82 with `loss = c / 2`.

**Tech Stack:** Lean 4, multiplicity-aware zeta-zero kernels, finite-set absolute mass, selected uniform good heights, Carlson two-height density bounds, signed natural-point transfer.

## Global Constraints

- Create only `ZeroDensityLayerBudgetActualMovingExtensionAbsoluteMass*.lean`, its focused audit, and this task documentation.
- Do not modify `ZeroForcedOscillationComplementaryBound.lean`.
- Do not modify sharp, localized pi-over-two, VK-edge, or zero-reproduction modules.
- Never compare a sub-sum norm with a complete signed-sum norm.
- Keep the genuine outside-seed gap and signed seed witnesses explicit.
- Preserve the final signed coefficient `c / 4`.
- Do not claim unconditional Omega-plus-minus or RH.

---

### Task 1: Positive outside absolute mass

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingExtensionAbsoluteMass.lean`

**Interfaces:**
- Produces: `dynamicPositiveOutsideClusterPNTAbsoluteMass`, selected low/high absolute-mass bounds, and `selectedPositiveOutsideClusterPNTAbsoluteMass_targetAmplitudeNegligible`.

- [x] **Step 1: define the positive outside absolute mass**

Sum `norm(pntRelativeZeroContribution x rho)` over
`positiveNontrivialZerosOutsideClusterFinset (H x) S`.

- [x] **Step 2: bound the selected low-layer absolute mass**

Use `canonicalSelectedLayer_subset_polynomialLayer` and
`dynamicOutsideClusterLayerMass_eq_low_add_high`.

- [x] **Step 3: bound the selected high-layer absolute mass**

Use `canonicalSelectedHighLayer_subset_polynomialCarlsonStrip` and monotonicity
of a nonnegative finite sum.

- [x] **Step 4: aggregate the two canonical layers**

Apply the bucket certificate `sum_decomposition` to the norm-valued summand
and `Fin.sum_univ_two`.

- [x] **Step 5: prove target-amplitude decay**

Reuse `tendsto_dynamicOutsideClusterTwoHeightMass_div_target` for the low
layer and
`tendsto_actualPositiveCarlsonStripTargetAmplitudeMass_twoHeight` for the high
layer.

### Task 2: Real and full outside absolute mass

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingExtensionAbsoluteMass.lean`

**Interfaces:**
- Produces: real, negative, and full absolute-mass definitions and full target-amplitude decay.

- [x] **Step 1: define real, negative, and full outside absolute masses**

- [x] **Step 2: prove real absolute-mass decay**

Freeze the real set at height zero and sum
`tendsto_norm_pntRelativeZeroContribution_div_targetZeroPowerAmplitude` over
the finite set.

- [x] **Step 3: prove the positive/negative/real mass partition**

Specialize `finiteZeroSumOutsideCluster_eq_positive_add_negative_add_real` to
the complex coercion of each nonnegative term norm and take real parts.

- [x] **Step 4: identify negative and positive masses by conjugation**

Use `sum_negativeOutsideCluster_eq_conj_sum_positiveOutsideCluster`, seed
conjugation invariance, and `pntRelativeZeroContribution_conj`.

- [x] **Step 5: prove full absolute-mass decay**

Rewrite full mass as `positive + positive + real` eventually and combine the
three target-negligibility certificates.

### Task 3: Moving-extension domination

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingExtensionAbsoluteMass.lean`

**Interfaces:**
- Produces: `abs_dynamicVisibleClusterPNTMain_sdiff_le_fullOutsideAbsoluteMass` and `selectedMovingRightEdgeExtension_targetAmplitudeNegligible`.

- [x] **Step 1: prove the pointwise extension bound**

Apply `abs(re z) <= norm z`, `norm_sum_le`, and pointwise indicator domination
to show every `E \\ S0` visible main is bounded by the full outside absolute
mass of `S0`.

- [x] **Step 2: specialize to the moving right-edge cluster**

Use `TargetAmplitudeNegligible.of_eventually_abs_le` with the full mass
certificate.

### Task 4: Genuine-gap signed automatic transfer

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingExtensionAbsoluteMass.lean`

**Interfaces:**
- Produces: `exists_automaticGoodHeight_positiveOutsideClusterGapMovingSeedSignedNaturalTargetTransfer`.

- [x] **Step 1: select all two-height parameters above `theta`**

Call `exists_jointTwoHeightTargetAmplitudeParameters_above_cap`.

- [x] **Step 2: derive the selected positive cap**

Use `PositiveOutsideClusterRealPartCap S0 theta` and `theta < tau`.

- [x] **Step 3: obtain moving-extension negligibility**

Combine Tasks 1-3 at `selectedUniformGoodHeight alpha selection`.

- [x] **Step 4: choose `loss = c / 2`**

Convert negligibility to the eventual strict budget with
`eventually_abs_lt_mul_of_naturalPointTargetAmplitudeNegligible`.

- [x] **Step 5: invoke stack82 and normalize the result**

Return fixed-rate PNT convergence and
`HasFarSignedTargetAmplitudeWitnesses` at
`(c / 4) * targetZeroPowerAmplitude beta`.

### Task 5: Contract, audit, and publication

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingExtensionAbsoluteMassContract.lean`
- Create: `Test/ZeroDensityLayerBudgetActualMovingExtensionAbsoluteMassAxiomAudit.lean`

- [x] **Step 1: compile implementation directly**

```bash
base=.lake/build/lib/lean
lake env lean \
  -o "$base/PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingExtensionAbsoluteMass.olean" \
  -i "$base/PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingExtensionAbsoluteMass.ilean" \
  PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingExtensionAbsoluteMass.lean
```

- [x] **Step 2: compile contract and run focused axiom audit**

Use the analogous dedicated contract outputs, then run the focused audit.

- [ ] **Step 3: commit plan and Lean code separately**

Use explicit paths and preserve the frozen untracked file.

- [ ] **Step 4: publish a stacked draft PR**

Base the PR on
`research/pintz-carlson-stack-82-moving-right-edge-signed-seed-stability`.
