# Carlson Pointwise-Gap Extension Absolute-Mass Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Remove every uniform outside real-part gap from the cancellation-free moving-extension estimate by embedding finite high-strip absolute mass into the summable Carlson outside-cluster kernel tail.

**Architecture:** A new module proves an exact low/high finite absolute-mass split. The canonical low layer uses the existing two-height absolute-mass decay, while the high layer is dominated by the infinite dyadic reciprocal Carlson `tsum`. Conjugation and the real-ordinate estimate give full mass decay, which feeds the existing signed moving-seed transfer.

**Tech Stack:** Lean 4, Mathlib finite sums/tsums/filters, actual Carlson positive-zero indexing, stack83 absolute masses, stack82 signed transfer.

## Global Constraints

- Create only the stack86 main module, contract, audit, and documents.
- Do not modify any existing Lean file.
- Never replace a finite absolute sum by a signed total-sum norm.
- Keep the frozen complementary-bound file untouched and untracked.
- The high hypothesis is pointwise `Re rho < beta`; same-line zeros must be in `S`.
- Run only direct main/contract compilation and the focused axiom audit.

---

### Task 1: Test-first contract probe

**Files:**
- Test temporarily: `/tmp/stack86_red.lean`

- [ ] **Step 1: Check the desired public names before implementation**

```lean
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonPointwiseGapExtensionAbsoluteMass
open PrimeNumberTheorem
#check truncatedPositiveZeroAbsoluteMass_div_target_le_low_add_CarlsonTail
#check exists_automaticGoodHeight_CarlsonPointwiseGapMovingSeedSignedNaturalTargetTransfer
```

Expected: import failure because the new `.olean` does not exist.

---

### Task 2: Finite absolute-mass split

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualCarlsonPointwiseGapExtensionAbsoluteMass.lean`

**Interfaces:**
- Consumes: `actualHighPositiveZerosOutsideClusterFinset`, `lowLayer_eq_filter_re_le`, and `finite_actualHighPositiveZeroKernelSum_le_CarlsonTail`.
- Produces: `truncatedPositiveZeroAbsoluteMass_div_target_le_low_add_CarlsonTail`.

- [ ] **Step 1: Partition the finite positive zero set**

For arbitrary bucket input `input` and low index `i`, use `hreLow` and `hlowCover` to identify the low layer with `Re rho <= sigma`; identify the complement with `actualHighPositiveZerosOutsideClusterFinset sigma T S`.

- [ ] **Step 2: Prove the normalized absolute-mass inequality**

Expose:

```lean
theorem truncatedPositiveZeroAbsoluteMass_div_target_le_low_add_CarlsonTail
    {T sigma beta : ℝ} {S : Finset ℂ} {n : ℕ}
    (input : PositiveZeroOutsideClusterBucketInput T S n) (i : Fin n)
    (hreLow : ∀ rho ∈ input.layer i, rho.re ≤ sigma)
    (hlowCover : ∀ rho ∈ positiveNontrivialZerosOutsideClusterFinset T S,
      rho.re ≤ sigma → input.bucket rho = i)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hreHigh : ∀ index : ActualCarlsonPositiveZeroIndex sigma,
      actualCarlsonPositiveZero index ∉ S →
        actualCarlsonPositiveZeroRealPart index < beta)
    {m : ℕ} (hm : 1 ≤ m) :
    (∑ rho ∈ positiveNontrivialZerosOutsideClusterFinset T S,
        ‖pntRelativeZeroContribution (m : ℝ) rho‖) /
        targetZeroPowerAmplitude beta (m : ℝ) ≤
      (∑ rho ∈ input.layer i,
        ‖pntRelativeZeroContribution (m : ℝ) rho‖) /
          targetZeroPowerAmplitude beta (m : ℝ) +
        actualCarlsonOutsideClusterNormalizedKernelTail
          (sigma := sigma) beta S m
```

Use exact partition of the nonnegative sum, `Finset.sum_div`, and the existing finite-high Carlson-tail theorem.

---

### Task 3: Natural-point positive and full absolute-mass decay

**Files:**
- Modify: the stack86 main module.

**Interfaces:**
- Consumes: Task 2, `canonicalSelectedLowLayerAbsoluteMass_le_polynomialTwoHeightMass`, `tendsto_dynamicOutsideClusterTwoHeightMass_div_target`, and the Carlson tail limit.
- Produces: positive and full natural-point negligibility theorems.

- [ ] **Step 1: Prove selected positive absolute-mass decay**

Expose `selectedPositiveOutsideClusterPNTAbsoluteMass_naturalPointNegligible_of_CarlsonPointwiseGap`. Its assumptions are the stack83 low two-height margins, eventual `H <= x^alpha`, `1/2 < sigma < 1`, and pointwise `hreHigh`. Build the canonical two-strip input; squeeze the normalized selected positive absolute mass by the polynomial low mass plus Carlson `tsum`.

- [ ] **Step 2: Prove full absolute-mass decay**

Expose `selectedFullOutsideClusterPNTAbsoluteMass_naturalPointNegligible_of_CarlsonPointwiseGap`. Add conjugation invariance, eventual `0 <= H`, and strict real-ordinate separation. Reuse `dynamicFullOutsideClusterPNTAbsoluteMass_eq_two_positive_add_real` and the natural-point restriction of the real-ordinate theorem.

---

### Task 4: Moving extension and automatic signed transfer

**Files:**
- Modify: the stack86 main module.

**Interfaces:**
- Consumes: Task 3, `abs_dynamicVisibleClusterPNTMain_sdiff_le_fullOutsideAbsoluteMass`, automatic two-height parameters, and the existing unified signed transfer.
- Produces: moving-extension natural-point decay and an automatic `c / 4` PNT theorem.

- [ ] **Step 1: Prove arbitrary moving-extension decay**

Expose `selectedMovingRightEdgeExtension_naturalPointNegligible_of_CarlsonPointwiseGap`; use `NaturalPointTargetAmplitudeNegligible.of_eventually_abs_le` and the stack83 pointwise absolute-mass domination.

- [ ] **Step 2: Prove the automatic signed theorem**

For `2/3 < beta < 1`, choose parameters with `theta = 1/2`. Return `sigma`, `transferTau`, and `alpha`. For every selected good height, assume only:

```lean
∀ index : ActualCarlsonPositiveZeroIndex sigma,
  actualCarlsonPositiveZero index ∉ S →
    actualCarlsonPositiveZeroRealPart index < beta
```

plus strict real-ordinate separation and positive/negative fixed-seed witnesses. Derive full absolute-mass decay, take loss `c / 2`, and call `unified_automaticGoodHeight_twoHeight_movingRightEdgeSignedSeedNaturalTargetTransfer`. Normalize the final amplitude to `c / 4`.

---

### Task 5: Contract, audit, and stacked PR

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualCarlsonPointwiseGapExtensionAbsoluteMassContract.lean`
- Create: `Test/ZeroDensityLayerBudgetActualCarlsonPointwiseGapExtensionAbsoluteMassAxiomAudit.lean`

- [ ] **Step 1: Add public `#check` and focused `#print axioms` declarations**

Check/audit the finite split, positive/full mass decay, extension decay, and final automatic transfer.

- [ ] **Step 2: Compile and audit**

Compile the main module and contract directly into `.lake/build/lib/lean`, then run the focused audit. Expected: exit code `0` and only repository-allowlisted foundations.

- [ ] **Step 3: Commit and publish**

Commit the plan separately, then the three Lean files. Push `research/pintz-carlson-stack-86-carlson-pointwise-gap-extension-absolute-mass` and open a Draft PR based on `research/pintz-carlson-stack-85-fixed-geometry-shrinking-gap-obstruction`.
