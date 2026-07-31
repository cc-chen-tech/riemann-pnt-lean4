# Moving Right-Edge Signed Seed Stability Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Transfer positive and negative fixed target-line seed witnesses through the moving right-edge cluster to one actual signed PNT certificate with exact coefficient `(c - loss) / 2`.

**Architecture:** Reuse stack81 eventual seed visibility and moving finite-sum decomposition, add positive and negative moving-family stability lemmas, then transfer both signs through one shared natural-point three-remainder estimate and the exact moving explicit formula.

**Tech Stack:** Lean 4, signed natural-point witnesses, moving zeta-zero clusters, selected uniform good heights, Carlson two-height transfer.

## Global Constraints

- Create only `ZeroDensityLayerBudgetActualMovingRightEdgeSignedSeedStabilityTransfer*.lean`, its focused audit, and this task documentation.
- Do not modify `ZeroForcedOscillationComplementaryBound.lean`.
- Do not modify VK-edge, sharp, or localized pi-over-two modules.
- Preserve the exact common signed amplitude `(c - loss) / 2`.
- Keep signed seed witnesses and the moving-extension budget explicit.
- Do not claim unconditional Omega-plus-minus or RH.

---

### Task 1: Signed moving-family seed stability

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingRightEdgeSignedSeedStabilityTransfer.lean`

**Interfaces:**
- Consumes: stack81 moving finite-sum decomposition and signed `transfer_eventually_sub_lt`.
- Produces: positive and negative moving visible-cluster seed stability theorems.

- [x] **Step 1: prove positive moving-seed stability**

For eventual `S0 subset S(m)`, transfer a positive seed witness at `c * A`
through the shared extension budget to `(c - loss) * A`.

- [x] **Step 2: prove negative moving-seed stability**

Repeat the exact coefficient argument for the negative witness predicate.

### Task 2: Shared signed actual residual transfer

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingRightEdgeSignedSeedStabilityTransfer.lean`

**Interfaces:**
- Consumes: stack81 seed visibility, stack79 moving complement, selected contour remainder, and the exact moving formula.
- Produces: `automaticGoodHeight_twoHeight_movingRightEdgeSignedSeedNaturalPointLowerTransfer`.

- [x] **Step 1: stabilize both seed signs to the moving cluster**

Use one eventual inclusion proof and one shared extension budget.

- [x] **Step 2: rescale all residual certificates by `c - loss`**

Require `0 < c - loss` and establish eventual positivity of the scaled target.

- [x] **Step 3: derive the actual-error minus moving-main bound**

Apply `eventually_abs_naturalPoint_three_remainders_lt_half`, rewrite the exact
moving formula, and simplify the difference.

- [x] **Step 4: transfer both signs and embed into the real interface**

Apply positive and negative `transfer_eventually_sub_lt`, normalize each
resulting target by ring arithmetic, and call
`hasFarSignedTargetAmplitudeWitnesses_of_naturalPoint`.

### Task 3: Unified and automatic parameters

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingRightEdgeSignedSeedStabilityTransfer.lean`

**Interfaces:**
- Produces: `unified_automaticGoodHeight_twoHeight_movingRightEdgeSignedSeedNaturalTargetTransfer` and `exists_automaticGoodHeight_movingRightEdgeSignedSeedNaturalTargetTransfer`.

- [x] **Step 1: pair signed lower transfer with fixed-rate PNT convergence**

- [x] **Step 2: select all two-height parameters from `2 / 3 < beta < 1`**

- [x] **Step 3: return the signed implication for every good-height selection**

The only lower inputs are the two seed signs and shared moving-extension
budget.

### Task 4: Contract, audit, and publication

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingRightEdgeSignedSeedStabilityTransferContract.lean`
- Create: `Test/ZeroDensityLayerBudgetActualMovingRightEdgeSignedSeedStabilityTransferAxiomAudit.lean`

- [x] **Step 1: compile implementation directly**

```bash
base=.lake/build/lib/lean
lake env lean \
  -o "$base/PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingRightEdgeSignedSeedStabilityTransfer.olean" \
  -i "$base/PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingRightEdgeSignedSeedStabilityTransfer.ilean" \
  PrimeNumberTheorem/ZeroDensityLayerBudgetActualMovingRightEdgeSignedSeedStabilityTransfer.lean
```

- [x] **Step 2: compile contract and run focused axiom audit**

Use the analogous dedicated output paths, then run:

```bash
lake env lean \
  Test/ZeroDensityLayerBudgetActualMovingRightEdgeSignedSeedStabilityTransferAxiomAudit.lean
```

- [ ] **Step 3: commit plan and code separately**

Use explicit paths and leave every frozen untracked file untouched.

- [ ] **Step 4: publish a stacked draft PR**

Base the PR on
`research/pintz-carlson-stack-81-moving-right-edge-seed-stability`.
