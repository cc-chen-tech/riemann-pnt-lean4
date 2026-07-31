# Moving Right-Edge Seed Stability Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Transfer a fixed finite target-line zeta-zero seed witness through the moving right-edge cluster to an actual coefficient-preserving PNT witness.

**Architecture:** Add generic natural-point moving-family finite-sum stability, prove automatic eventual inclusion of a finite target-line seed in the cofinal moving right-edge cluster, and compose the resulting moving-main witness with stack80's Carlson and explicit-formula residual bounds.

**Tech Stack:** Lean 4, finite zeta-zero clusters, selected uniform good heights, target-amplitude negligibility, Carlson two-height parameter selection.

## Global Constraints

- Create only `ZeroDensityLayerBudgetActualMovingRightEdgeSeedStabilityTransfer*.lean`, its focused audit, and this task documentation.
- Do not modify `ZeroForcedOscillationComplementaryBound.lean`.
- Do not modify VK-edge or sharp/localized oscillation modules.
- Preserve the exact retained coefficient `(c - loss) / 2`.
- Keep the moving-extension budget as an explicit hypothesis.
- Do not claim unconditional Omega, Omega-plus-minus, or RH.

---

### Task 1: Moving finite-seed algebra

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingRightEdgeSeedStabilityTransfer.lean`

**Interfaces:**
- Consumes: `dynamicVisibleClusterPNTMain_eq_seed_add_extension`.
- Produces: `dynamicVisibleClusterPNTMain_eq_seed_add_movingExtension` and `hasFarNaturalPointTargetAmplitudeWitness_movingVisibleCluster_of_seed`.

- [x] **Step 1: define the pointwise moving-extension decomposition**

For `S : N -> Finset C`, specialize the existing fixed-extension equality at
`S m`:

```lean
theorem dynamicVisibleClusterPNTMain_eq_seed_add_movingExtension
    (T : R -> R) {S0 : Finset C} (S : N -> Finset C)
    (hsub : forall m rho, rho in S0 -> rho in S m) (m : N) :
    dynamicVisibleClusterPNTMain T (S m) (m : R) =
      dynamicVisibleClusterPNTMain T S0 (m : R) +
        dynamicVisibleClusterPNTMain T (S m \ S0) (m : R)
```

- [x] **Step 2: prove eventual moving-seed witness stability**

Use `transfer_eventually_sub_lt` with eventual inclusion and the exact
extension budget:

```lean
theorem hasFarNaturalPointTargetAmplitudeWitness_movingVisibleCluster_of_seed
    (T : R -> R) {S0 : Finset C} (S : N -> Finset C)
    (hsub : forall eventually m, S0 subset S m)
    (hseed : HasFarNaturalPointTargetAmplitudeWitness
      (fun m => dynamicVisibleClusterPNTMain T S0 m)
      (fun m => c * amplitude m))
    (hnew : forall eventually m,
      abs (dynamicVisibleClusterPNTMain T (S m \ S0) m) <
        loss * amplitude m) :
    HasFarNaturalPointTargetAmplitudeWitness
      (fun m => dynamicVisibleClusterPNTMain T (S m) m)
      (fun m => (c - loss) * amplitude m)
```

### Task 2: Automatic target-line seed visibility

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingRightEdgeSeedStabilityTransfer.lean`

**Interfaces:**
- Consumes: `selectedUniformGoodHeight_tendsto_atTop`, `mem_rightEdgeNontrivialZerosFinset`.
- Produces: `IsTargetRealPartNontrivialZeroSeed` and `eventually_targetSeed_subset_movingRightEdgeExceptionalCluster`.

- [x] **Step 1: define the actual target-line seed predicate**

```lean
def IsTargetRealPartNontrivialZeroSeed
    (beta : R) (S0 : Finset C) : Prop :=
  forall rho in S0,
    RiemannHypothesis.IsNontrivialZero rho /\ rho.re = beta
```

- [x] **Step 2: prove finite eventual visibility at every cofinal height**

Induct on `S0`. For each inserted zero, pull back
`eventually_ge_atTop abs(rho.im)` through `Tendsto H atTop atTop`, then use
`tau < beta` and the target-line equality to prove right-edge membership.

- [x] **Step 3: specialize to every selected uniform good height**

Apply `selectedUniformGoodHeight_tendsto_atTop halpha selection`.

### Task 3: Coefficient-preserving actual transfer

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingRightEdgeSeedStabilityTransfer.lean`

**Interfaces:**
- Consumes: stack79 moving-complement negligibility, selected contour remainder, natural-point amplitude scaling, and the Task 1-2 witness.
- Produces: `automaticGoodHeight_twoHeight_movingRightEdgeSeedNaturalPointLowerTransfer` and `unified_automaticGoodHeight_twoHeight_movingRightEdgeSeedNaturalTargetTransfer`.

- [x] **Step 1: construct the moving-main witness**

Use the automatic eventual seed inclusion and the explicit moving-extension
budget to obtain amplitude `(c - loss) * targetZeroPowerAmplitude beta`.

- [x] **Step 2: rescale all three residual certificates**

From `0 < c - loss`, use
`NaturalPointTargetAmplitudeNegligible.const_mul_amplitude` for the closed
axis, selected contour remainder, and moving Carlson complement.

- [x] **Step 3: apply the exact moving explicit formula**

Invoke `hasFarNaturalPointTargetAmplitudeWitness_of_three_remainders` and
`relativeChebyshevPsi0Error_eq_movingRightEdgeCluster_add_actualResiduals`.
Return:

```text
HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
  (fun x => ((c - loss) * targetZeroPowerAmplitude beta x) / 2)
```

- [x] **Step 4: pair the lower witness with fixed-rate PNT convergence**

Return the existing `exists_fixedRate_relativeChebyshevPsi0Error_tendsto`
together with the coefficient-preserving lower result.

### Task 4: Automatic two-height parameters

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingRightEdgeSeedStabilityTransfer.lean`

**Interfaces:**
- Consumes: `exists_jointTwoHeightTargetAmplitudeParameters_above_cap`.
- Produces: `exists_automaticGoodHeight_movingRightEdgeSeedNaturalTargetTransfer`.

- [x] **Step 1: prove anchor feasibility from `2 / 3 < beta`**

Establish:

```lean
(1 / 2 : R) < (3 * beta - 1) / 2
```

- [x] **Step 2: select `sigma`, `tau`, `alpha`, and both height splits**

Reuse the same selector and destructuring as stack80.

- [x] **Step 3: discharge target-line seed visibility automatically**

Use `tau < beta`, the seed predicate, and selected-height cofinality.

- [x] **Step 4: return the unified implication for every selection**

The only lower inputs must be the fixed seed witness and moving-extension
budget.

### Task 5: Contract, audit, and publication

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingRightEdgeSeedStabilityTransferContract.lean`
- Create: `Test/ZeroDensityLayerBudgetActualMovingRightEdgeSeedStabilityTransferAxiomAudit.lean`

**Interfaces:**
- Contract checks every public definition and theorem.
- Audit prints axioms for the fixed-parameter, unified, and automatic transfer theorems.

- [x] **Step 1: compile the implementation directly**

```bash
base=.lake/build/lib/lean
lake env lean \
  -o "$base/PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingRightEdgeSeedStabilityTransfer.olean" \
  -i "$base/PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingRightEdgeSeedStabilityTransfer.ilean" \
  PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingRightEdgeSeedStabilityTransfer.lean
```

- [x] **Step 2: compile the contract and run the focused audit**

```bash
base=.lake/build/lib/lean
lake env lean \
  -o "$base/PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingRightEdgeSeedStabilityTransferContract.olean" \
  -i "$base/PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingRightEdgeSeedStabilityTransferContract.ilean" \
  PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingRightEdgeSeedStabilityTransferContract.lean
lake env lean \
  Test/ZeroDensityLayerBudgetActualMovingRightEdgeSeedStabilityTransferAxiomAudit.lean
```

- [ ] **Step 3: commit documentation and Lean code separately**

Stage only the task documentation and
`ZeroDensityLayerBudgetActualMovingRightEdgeSeedStabilityTransfer*` paths.

- [ ] **Step 4: publish a stacked draft PR**

Push `research/pintz-carlson-stack-81-moving-right-edge-seed-stability` and
open a draft PR based on
`research/pintz-carlson-stack-80-moving-right-edge-unified-transfer`.
