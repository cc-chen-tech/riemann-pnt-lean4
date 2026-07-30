# Target-Amplitude Two-Height Exponent Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalize the denominator-saving two-height Carlson exponent after normalization by a target zero amplitude and prove the canonical `beta > 2/3` feasibility threshold.

**Architecture:** A standalone arithmetic module reuses the existing Carlson density exponent and balanced cut. It defines target-normalized low, high, and balanced exponents, proves their exact identities and feasibility criterion, and packages a canonical parameter existence theorem. A contract and axiom audit expose and verify the public chain.

**Tech Stack:** Lean 4, Mathlib real arithmetic, existing Pintz-Carlson layer-budget modules.

## Global Constraints

- Modify only `ZeroDensityLayerBudget*` files and this task's design/plan documents.
- Do not read, modify, delete, or stage `ZeroForcedOscillationComplementaryBound.lean`.
- Do not modify VK-edge modules.
- Do not claim an actual annulus estimate, unconditional Omega theorem, or RH.
- Keep target normalization at the exact `x ^ (beta - 1)` scale.

---

### Task 1: Target-normalized two-height exponent arithmetic

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetTargetAmplitudeTwoHeightExponent.lean`

**Interfaces:**
- Consumes: `carlsonTwoHeightDensityExponent`, `carlsonTwoHeightBalancedCut`, and their positivity/cut bounds.
- Produces: target-normalized low, high, balanced, and balanced-slope definitions and identities.

- [ ] **Step 1: Define the four arithmetic quantities**

```lean
def targetAmplitudeCarlsonTwoHeightLowExponent
    (beta sigma tau gamma : R) : R :=
  carlsonTwoHeightDensityExponent sigma * gamma + tau - beta

def targetAmplitudeCarlsonTwoHeightHighExponent
    (beta sigma tau alpha gamma : R) : R :=
  carlsonTwoHeightDensityExponent sigma * alpha + tau - beta - gamma

noncomputable def targetAmplitudeCarlsonTwoHeightBalancedSlope
    (sigma : R) : R :=
  carlsonTwoHeightDensityExponent sigma ^ 2 /
    (carlsonTwoHeightDensityExponent sigma + 1)

noncomputable def targetAmplitudeCarlsonTwoHeightBalancedExponent
    (beta sigma tau alpha : R) : R :=
  tau - beta +
    targetAmplitudeCarlsonTwoHeightBalancedSlope sigma * alpha
```

- [ ] **Step 2: Prove balanced low/high identities**

Use `field_simp` and `ring` under
`carlsonTwoHeightDensityExponent sigma + 1 != 0`.

- [ ] **Step 3: Prove strict improvement over one height**

Show:

```lean
targetAmplitudeCarlsonTwoHeightBalancedExponent beta sigma tau alpha <
  carlsonTwoHeightDensityExponent sigma * alpha + tau - beta
```

for `1/2 < sigma < 1` and `0 < alpha`.

### Task 2: Exact feasibility and strict-margin package

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetTargetAmplitudeTwoHeightExponent.lean`

**Interfaces:**
- Consumes: Task 1 balanced-slope positivity and exponent identity.
- Produces: an iff criterion and simultaneous low/high strict margins.

- [ ] **Step 1: Prove balanced-slope positivity**

Derive it from `carlsonTwoHeightDensityExponent_pos`.

- [ ] **Step 2: Prove the feasibility iff**

```lean
(exists alpha,
    1 - beta < alpha and
    targetAmplitudeCarlsonTwoHeightBalancedExponent
      beta sigma tau alpha < 0) <->
  targetAmplitudeCarlsonTwoHeightBalancedSlope sigma *
      (1 - beta) + tau - beta < 0
```

For the reverse direction, choose the midpoint between `1 - beta` and the
zero of the affine balanced exponent.

- [ ] **Step 3: Add a positive epsilon**

Given a negative balanced exponent, choose
`epsilon = -balancedExponent / 2` and prove both balanced low and high
exponents plus epsilon are negative.

### Task 3: Canonical `beta > 2/3` parameters

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetTargetAmplitudeTwoHeightExponent.lean`

**Interfaces:**
- Consumes: Task 2 feasibility package.
- Produces: the explicit canonical threshold and a complete parameter witness.

- [ ] **Step 1: Define the canonical strip threshold**

```lean
def targetAmplitudeCarlsonTwoHeightCanonicalThreshold (beta : R) : R :=
  (3 * beta - 1) / 2
```

- [ ] **Step 2: Prove density and slope bounds**

For the canonical threshold under `2/3 < beta < 1`, prove:

```text
1/2 < sigma
sigma < beta
sigma < 1
0 < q(sigma) < 1
0 < r(sigma) < 1/2
```

- [ ] **Step 3: Prove canonical feasibility**

Instantiate the feasibility iff with `tau = sigma`, then obtain
`alpha`, balanced `gamma`, and `epsilon` satisfying both strict exponent
margins.

### Task 4: Contract and axiom audit

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetTargetAmplitudeTwoHeightExponentContract.lean`
- Create: `Test/ZeroDensityLayerBudgetTargetAmplitudeTwoHeightExponentAxiomAudit.lean`

**Interfaces:**
- Consumes: all public declarations from Tasks 1-3.
- Produces: compile-time signature checks and axiom reports.

- [ ] **Step 1: Add contract checks**

Check the definitions, balanced identities, improvement theorem, feasibility
iff, and canonical parameter theorem.

- [ ] **Step 2: Add axiom audit**

Print axioms for the balanced identities, feasibility iff, improvement
theorem, and canonical parameter theorem.

- [ ] **Step 3: Run focused verification**

```bash
lake -Kjobs=1 build \
  PrimeNumberTheorem.ZeroDensityLayerBudgetTargetAmplitudeTwoHeightExponent \
  PrimeNumberTheorem.ZeroDensityLayerBudgetTargetAmplitudeTwoHeightExponentContract
lake env lean \
  Test/ZeroDensityLayerBudgetTargetAmplitudeTwoHeightExponentAxiomAudit.lean
```

Expected: focused build succeeds and audited endpoints use only the standard
Mathlib axioms already allowed by the project.

### Task 5: Publish the coherent stack

**Files:**
- Stage only the two task documents and three Task 1-4 Lean files.

- [ ] **Step 1: Commit documents separately**

```bash
git add -- \
  docs/superpowers/specs/2026-07-31-target-amplitude-two-height-exponent-design.md \
  docs/superpowers/plans/2026-07-31-target-amplitude-two-height-exponent.md
git commit -m "docs: design target-amplitude two-height exponents"
```

- [ ] **Step 2: Commit verified Lean artifacts**

```bash
git add -- \
  PrimeNumberTheorem/ZeroDensityLayerBudgetTargetAmplitudeTwoHeightExponent.lean \
  PrimeNumberTheorem/ZeroDensityLayerBudgetTargetAmplitudeTwoHeightExponentContract.lean \
  Test/ZeroDensityLayerBudgetTargetAmplitudeTwoHeightExponentAxiomAudit.lean
git commit -m "feat: optimize target-amplitude two-height exponents"
```

- [ ] **Step 3: Push and open a draft stacked PR**

Use stack 34 as the PR base and state explicitly that the actual annulus
kernel transfer remains the next bridge.
