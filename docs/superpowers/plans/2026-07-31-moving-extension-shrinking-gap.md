# Moving Extension Shrinking-Gap Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the fixed outside-zero real-part gap in the cancellation-free moving-extension transfer by an auditable scale-dependent Carlson rate, while preserving the actual signed PNT witness coefficient `c / 4`.

**Architecture:** A new standalone Lean module first records a generic shrinking-gap mass rate and an exponential-margin constructor. It then defines the exact dynamic two-height Carlson budget, proves actual positive/full outside absolute-mass decay, transfers that decay to the moving extension, and composes with the existing signed PNT transfer. Existing stack82/83 modules are imported but not modified.

**Tech Stack:** Lean 4, Mathlib filters and real powers, the existing Pintz/Carlson layer budgets, stack82 signed transfer, stack83 cancellation-free absolute masses.

## Global Constraints

- Work only on branch `research/pintz-carlson-stack-84-moving-extension-shrinking-gap` in `.worktrees/explicit-formula-unified-next`.
- Create only `ZeroDensityLayerBudget*ShrinkingGap*`, its contract/audit, and this stack's documents.
- Never edit, stage, delete, or overwrite `PrimeNumberTheorem/ZeroForcedOscillationComplementaryBound.lean`.
- Do not edit Sharp, localized pi/2, VK-edge, or zero-reproduction modules.
- Never control a signed sub-sum by a signed full sum; use stack83's termwise absolute mass.
- Keep `transferTau : ℝ` distinct from the moving cap `capTau : ℝ → ℝ`.
- Do not claim an unconditional zeta gap, signed seed witness, `Omega_+-`, or RH theorem.
- Compile only the new main module and contract, then run only the focused axiom audit.
- Stage every commit with exact paths; never use `git add -A`.

---

### Task 1: Generic shrinking-gap and actual Carlson-rate interfaces

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingExtensionShrinkingGap.lean`

**Interfaces:**
- Consumes: `targetZeroPowerAmplitude`, `actualCarlsonTargetTwoHeightLowBudget`, `actualCarlsonTargetTwoHeightHighBudget`, and stack83 absolute-mass declarations.
- Produces: `HasShrinkingGapMassRate`, `HasShrinkingGapCarlsonTwoHeightRate`, `shrinkingGapMassRate_of_exponentialMargin`, and `shrinkingGapCarlsonTwoHeightRate_of_budget_majorants`.

- [ ] **Step 1: Create the module and imports**

```lean
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualMovingExtensionAbsoluteMass

namespace PrimeNumberTheorem

open Filter Real
open scoped Topology
```

- [ ] **Step 2: Define the generic multiplicative rate**

```lean
def HasShrinkingGapMassRate
    (beta : ℝ) (scale capTau massCoefficient : ℝ → ℝ) : Prop :=
  Tendsto
    (fun x => massCoefficient x * (scale x) ^ (capTau x - beta))
    atTop (nhds 0)
```

The definition uses real `rpow`, matching `targetZeroPowerAmplitude`.

- [ ] **Step 3: Prove the exponential-margin constructor**

```lean
theorem shrinkingGapMassRate_of_exponentialMargin
    {beta : ℝ} {scale capTau massCoefficient margin : ℝ → ℝ}
    (hnonneg : ∀ᶠ x in atTop,
      0 ≤ massCoefficient x * (scale x) ^ (capTau x - beta))
    (hle : ∀ᶠ x in atTop,
      massCoefficient x * (scale x) ^ (capTau x - beta) ≤
        Real.exp (-margin x))
    (hmargin : Tendsto margin atTop atTop) :
    HasShrinkingGapMassRate beta scale capTau massCoefficient := by
  -- Squeeze the nonnegative rate by exp (-margin x), whose limit is zero.
```

Use `Real.tendsto_exp_atBot` after composing `hmargin` with negation, then `squeeze_zero'`. Do not take `Real.log (massCoefficient x)`; this keeps zero coefficients legal.

- [ ] **Step 4: Define the exact dynamic Carlson rate**

```lean
def HasShrinkingGapCarlsonTwoHeightRate
    (beta sigma alpha gamma : ℝ) (capTau : ℝ → ℝ) : Prop :=
  Tendsto
    (fun x =>
      actualCarlsonTargetTwoHeightLowBudget
          beta sigma (capTau x) gamma x +
        actualCarlsonTargetTwoHeightHighBudget
          beta sigma (capTau x) alpha gamma x)
    atTop (nhds 0)
```

Both terms contain `ZeroDensity.zeroDensityCount`; this is an actual zeta/Carlson interface rather than an abstract kernel.

- [ ] **Step 5: Connect generic majorants to the exact Carlson rate**

```lean
theorem shrinkingGapCarlsonTwoHeightRate_of_budget_majorants
    {beta sigma alpha gamma : ℝ}
    {capTau lowCoefficient highCoefficient : ℝ → ℝ}
    (hlowRate : HasShrinkingGapMassRate beta id capTau lowCoefficient)
    (hhighRate : HasShrinkingGapMassRate beta id capTau highCoefficient)
    (hlowNonneg : ∀ᶠ x in atTop,
      0 ≤ actualCarlsonTargetTwoHeightLowBudget
        beta sigma (capTau x) gamma x)
    (hhighNonneg : ∀ᶠ x in atTop,
      0 ≤ actualCarlsonTargetTwoHeightHighBudget
        beta sigma (capTau x) alpha gamma x)
    (hlow : ∀ᶠ x in atTop,
      actualCarlsonTargetTwoHeightLowBudget
          beta sigma (capTau x) gamma x ≤
        lowCoefficient x * x ^ (capTau x - beta))
    (hhigh : ∀ᶠ x in atTop,
      actualCarlsonTargetTwoHeightHighBudget
          beta sigma (capTau x) alpha gamma x ≤
        highCoefficient x * x ^ (capTau x - beta)) :
    HasShrinkingGapCarlsonTwoHeightRate beta sigma alpha gamma capTau := by
  -- Squeeze each budget by its zero majorant and add the limits.
```

- [ ] **Step 6: Compile the interface checkpoint**

```bash
base=.lake/build/lib/lean
lake env lean \
  -o "$base/PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingExtensionShrinkingGap.olean" \
  -i "$base/PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingExtensionShrinkingGap.ilean" \
  PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingExtensionShrinkingGap.lean
```

Expected: exit code `0`. Fix only compiler-reported errors in the new module.

---

### Task 2: Actual positive and full absolute-mass decay

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingExtensionShrinkingGap.lean`

**Interfaces:**
- Consumes: Task 1's exact Carlson rate, stack83's `dynamicSelectedPositiveOutsideClusterPNTAbsoluteMass_le`, and the existing fixed-`sigma` low-layer two-height decay.
- Produces: `selectedPositiveOutsideClusterPNTAbsoluteMass_targetAmplitudeNegligible_of_shrinkingGap` and `selectedFullOutsideClusterPNTAbsoluteMass_targetAmplitudeNegligible_of_shrinkingGap`.

- [ ] **Step 1: Prove dynamic-strip normalized decay**

Prove that the following function tends to zero from `HasShrinkingGapCarlsonTwoHeightRate`:

```lean
fun x =>
  (∑ rho ∈ actualPositiveCarlsonStrip sigma (capTau x)
      (carlsonPolynomialHeight alpha x),
      ‖pntRelativeZeroContribution x rho‖) /
    targetZeroPowerAmplitude beta x
```

Use `actualPositiveCarlsonStripTargetAmplitudeMass_le_twoHeightBudget` eventually at `1 ≤ x`. Establish nonnegativity from the finite sum and eventual positivity of `targetZeroPowerAmplitude beta x`.

- [ ] **Step 2: Prove positive outside-mass decay**

Expose a theorem with these hypotheses:

```lean
hsigma : 1 / 2 < sigma
hsigmaOne : sigma < 1
halpha : 0 < alpha
hgammaLow : 0 < gammaLow
hepsilonLow : 0 < epsilonLow
hlowLow : gammaLow + sigma - beta + epsilonLow < 0
hlowHigh : alpha + sigma - beta - gammaLow + epsilonLow < 0
hHle : ∀ᶠ x in atTop, H x ≤ carlsonPolynomialHeight alpha x
hcap : ∀ x rho ∈ positiveNontrivialZerosOutsideClusterFinset (H x) S,
  sigma < rho.re → rho.re ≤ capTau x
hstripRate : HasShrinkingGapCarlsonTwoHeightRate
  beta sigma alpha gammaHigh capTau
```

The conclusion is:

```lean
TargetAmplitudeNegligible
  (targetZeroPowerAmplitude beta)
  (dynamicPositiveOutsideClusterPNTAbsoluteMass H S)
```

Use `exists_canonicalTwoStripOutsideCluster_uniform_norm_lower_bound` and `tendsto_dynamicOutsideClusterTwoHeightMass_div_target` for the low canonical layer. Use Task 2 Step 1 for the moving high strip. Apply `dynamicSelectedPositiveOutsideClusterPNTAbsoluteMass_le` pointwise and squeeze the normalized positive mass by the sum of the two limits.

- [ ] **Step 3: Recover full absolute-mass decay**

Expose `selectedFullOutsideClusterPNTAbsoluteMass_targetAmplitudeNegligible_of_shrinkingGap` with the positive hypotheses plus:

```lean
hS : IsConjugationInvariantCluster S
hHnonneg : ∀ᶠ x in atTop, 0 ≤ H x
hreal : ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
  rho.re < beta
```

Use `dynamicRealOrdinateOutsideClusterPNTAbsoluteMass_targetAmplitudeNegligible` and `dynamicFullOutsideClusterPNTAbsoluteMass_eq_two_positive_add_real`. Conclude by adding the three normalized zero limits.

- [ ] **Step 4: Compile the actual-mass checkpoint**

Run the direct main-module command from Task 1 Step 6. Expected: exit code `0`.

---

### Task 3: Moving extension and signed PNT composition

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingExtensionShrinkingGap.lean`

**Interfaces:**
- Consumes: Task 2 full-mass decay, stack83 extension domination, and stack82 `exists_automaticGoodHeight_movingRightEdgeSignedSeedNaturalTargetTransfer`.
- Produces: `selectedMovingRightEdgeExtension_targetAmplitudeNegligible_of_shrinkingGap` and `exists_shrinkingGap_positiveOutsideClusterMovingSeedSignedNaturalTargetTransfer`.

- [ ] **Step 1: Transfer full-mass decay to any fixed exceptional threshold**

```lean
theorem selectedMovingRightEdgeExtension_targetAmplitudeNegligible_of_shrinkingGap
    {H : ℝ → ℝ} {S : Finset ℂ} {beta transferTau : ℝ}
    (hfull : TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (dynamicFullOutsideClusterPNTAbsoluteMass H S)) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (fun x => dynamicVisibleClusterPNTMain H
        (movingRightEdgeExceptionalCluster H transferTau x \ S) x) :=
  selectedMovingRightEdgeExtension_targetAmplitudeNegligible hfull
```

The fixed `transferTau` is intentionally independent of `capTau x`.

- [ ] **Step 2: State the automatic signed composition**

Expose an existential theorem for `2 / 3 < beta < 1`, `0 < c`, a target seed, and a conjugation-invariant cluster. It returns fixed `sigma`, `transferTau`, and `alpha` satisfying stack82's automatic parameter conditions. For every good-height selection it accepts `capTau : ℝ → ℝ`, `gammaLow`, `gammaHigh`, and `epsilonLow`, together with the Task 2 low-layer margins, the selected-height moving cap, the exact shrinking Carlson rate, the real-ordinate gap, and positive/negative fixed-seed witnesses of coefficient `c`.

The conclusion is exactly:

```lean
(∃ rate, 0 < rate ∧ rate ≤ 1 ∧
  Tendsto (fun m => relativeChebyshevPsi0Error (m : ℝ)) atTop (nhds 0)) ∧
HasFarSignedTargetAmplitudeWitnesses
  relativeChebyshevPsi0Error
  (fun x => (c / 4) * targetZeroPowerAmplitude beta x)
```

- [ ] **Step 3: Assemble the final theorem**

Use `loss = c / 2`. Prove `0 < c - c / 2` by linear arithmetic. Obtain the automatic fixed transfer parameters from `exists_automaticGoodHeight_movingRightEdgeSignedSeedNaturalTargetTransfer`. For each selection:

1. instantiate Task 2 full-mass decay with `H = selectedUniformGoodHeight alpha selection`;
2. obtain moving-extension `TargetAmplitudeNegligible` from Task 3 Step 1;
3. specialize the real-variable eventual bound to natural points;
4. use `eventually_abs_lt_mul_of_targetAmplitudeNegligible` with `c / 2`;
5. feed that bound and both seed witnesses to stack82;
6. normalize `(c - c / 2) / 2` to `c / 4` by `ring`.

- [ ] **Step 4: Compile the completed main module**

Run the direct main-module command. Expected: exit code `0`; tactic-style linter warnings are permitted but theorem or declaration warnings are not.

---

### Task 4: Contract and axiom audit

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingExtensionShrinkingGapContract.lean`
- Create: `Test/ZeroDensityLayerBudgetActualMovingExtensionShrinkingGapAxiomAudit.lean`

**Interfaces:**
- Consumes: all public declarations from Tasks 1-3.
- Produces: compile-time signature checks and printed axiom dependencies.

- [ ] **Step 1: Write the contract**

```lean
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualMovingExtensionShrinkingGap
open PrimeNumberTheorem

#check HasShrinkingGapMassRate
#check shrinkingGapMassRate_of_exponentialMargin
#check HasShrinkingGapCarlsonTwoHeightRate
#check shrinkingGapCarlsonTwoHeightRate_of_budget_majorants
#check selectedPositiveOutsideClusterPNTAbsoluteMass_targetAmplitudeNegligible_of_shrinkingGap
#check selectedFullOutsideClusterPNTAbsoluteMass_targetAmplitudeNegligible_of_shrinkingGap
#check selectedMovingRightEdgeExtension_targetAmplitudeNegligible_of_shrinkingGap
#check exists_shrinkingGap_positiveOutsideClusterMovingSeedSignedNaturalTargetTransfer
```

- [ ] **Step 2: Write the focused audit**

```lean
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualMovingExtensionShrinkingGapContract
open PrimeNumberTheorem

#print axioms shrinkingGapMassRate_of_exponentialMargin
#print axioms shrinkingGapCarlsonTwoHeightRate_of_budget_majorants
#print axioms selectedFullOutsideClusterPNTAbsoluteMass_targetAmplitudeNegligible_of_shrinkingGap
#print axioms selectedMovingRightEdgeExtension_targetAmplitudeNegligible_of_shrinkingGap
#print axioms exists_shrinkingGap_positiveOutsideClusterMovingSeedSignedNaturalTargetTransfer
```

- [ ] **Step 3: Compile contract and run audit**

```bash
base=.lake/build/lib/lean
lake env lean \
  -o "$base/PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingExtensionShrinkingGapContract.olean" \
  -i "$base/PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingExtensionShrinkingGapContract.ilean" \
  PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingExtensionShrinkingGapContract.lean &&
lake env lean Test/ZeroDensityLayerBudgetActualMovingExtensionShrinkingGapAxiomAudit.lean
```

Expected: both commands exit `0`; every audited theorem reports only repository allowlisted foundations such as `propext`, `Classical.choice`, and `Quot.sound`.

---

### Task 5: Commit and publish the stacked Draft PR

**Files:**
- Stage only the stack84 design, plan, main module, contract, and audit.

**Interfaces:**
- Consumes: successful Task 4 evidence.
- Produces: an auditable commit series and Draft PR stacked on PR #137.

- [ ] **Step 1: Commit the implementation plan**

```bash
git add -- docs/superpowers/plans/2026-07-31-moving-extension-shrinking-gap.md
git commit -m "docs: plan shrinking-gap moving extension transfer"
```

- [ ] **Step 2: Commit implementation and audit**

```bash
git add -- \
  PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingExtensionShrinkingGap.lean \
  PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingExtensionShrinkingGapContract.lean \
  Test/ZeroDensityLayerBudgetActualMovingExtensionShrinkingGapAxiomAudit.lean
git commit -m "feat: transfer shrinking Carlson gaps to signed PNT"
```

- [ ] **Step 3: Confirm the frozen file remains untracked**

Run `git status -sb --untracked-files=all`. The only unrelated path may be `PrimeNumberTheorem/ZeroForcedOscillationComplementaryBound.lean`, and it must remain untracked.

- [ ] **Step 4: Push and open a Draft PR**

Push `research/pintz-carlson-stack-84-moving-extension-shrinking-gap` and create a Draft PR with base `research/pintz-carlson-stack-83-moving-extension-absolute-mass`.

The PR body must state that the theorem accepts a shrinking Carlson rate and fixed-seed signed witnesses; it does not prove those hypotheses for zeta and does not imply unconditional `Omega_+-` or RH.
