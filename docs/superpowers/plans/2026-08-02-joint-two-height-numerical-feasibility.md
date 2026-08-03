# Joint Two-Height Numerical Feasibility Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove, as an independent main-based slice, the pure real-arithmetic seven-parameter feasibility theorem for every `2 / 3 < beta < 1`, with four explicit strictly negative exponent margins.

**Architecture:** A dependency-free numerical core owns the Carlson density exponent, balanced cut, target-normalized low/high exponents, and only the algebraic lemmas needed downstream. A second module constructs the seven witnesses. Exact-type contracts are written and observed failing before production declarations, and separate axiom audits lock the proof boundary.

**Tech Stack:** Lean 4, Mathlib real arithmetic (`linarith`, `nlinarith`, `field_simp`, `ring`), Lake, Git worktrees, GitHub Draft PRs.

## Global Constraints

- Rebase the unpublished branch onto the current `origin/main` immediately before final verification and publication.
- Keep only pure real arithmetic. Do not import actual zero-set, zero-count, explicit-formula tail, contour, smoothing, Sharp, or Witness modules.
- Preserve exactly seven witnesses: `sigma tau alpha gammaLow gammaHigh epsilonLow epsilonHigh`.
- Preserve exactly the four strict negative-margin conditions in the approved theorem type.
- Do not claim an actual tail estimate, E2-to-two-height transfer, zero exclusion, or a result at `beta = 2 / 3`.
- Keep the ignored local `vendor -> ../../vendor` symlink and `.lake` out of commits.
- Run at most one Lean/Lake command at a time, with `LEAN_NUM_THREADS=1 lake -Kjobs=1`.
- Accepted axiom output is limited to `propext`, `Classical.choice`, and `Quot.sound`.

---

## File map

- Create `PrimeNumberTheorem/ZeroDensityLayerBudgetTwoHeightNumericalCore.lean`: exact formulas and reusable real-algebra lemmas.
- Create `Test/ZeroDensityLayerBudgetTwoHeightNumericalCoreContract.lean`: definitional equalities and exact public lemma types.
- Create `Test/ZeroDensityLayerBudgetTwoHeightNumericalCoreAxiomAudit.lean`: `#print axioms` for the numerical lemmas.
- Create `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightParameterFeasibility.lean`: the seven-witness construction.
- Create `Test/ZeroDensityLayerBudgetJointTwoHeightParameterFeasibilityContract.lean`: exact theorem-type lock.
- Create `Test/ZeroDensityLayerBudgetJointTwoHeightParameterFeasibilityAxiomAudit.lean`: theorem axiom audit.
- Modify `lakefile.lean`: register both implementation roots and all four test roots.

---

### Task 1: Numerical core with exact-formula contract

**Files:**
- Create: `Test/ZeroDensityLayerBudgetTwoHeightNumericalCoreContract.lean`
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetTwoHeightNumericalCore.lean`
- Create: `Test/ZeroDensityLayerBudgetTwoHeightNumericalCoreAxiomAudit.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes: Mathlib real arithmetic only.
- Produces:
  - `carlsonTwoHeightDensityExponent : ℝ → ℝ`
  - `carlsonTwoHeightBalancedCut : ℝ → ℝ → ℝ`
  - `targetAmplitudeCarlsonTwoHeightLowExponent : ℝ → ℝ → ℝ → ℝ → ℝ`
  - `targetAmplitudeCarlsonTwoHeightHighExponent : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ`
  - `targetAmplitudeCarlsonTwoHeightBalancedSlope : ℝ → ℝ`
  - `targetAmplitudeCarlsonTwoHeightBalancedExponent : ℝ → ℝ → ℝ → ℝ → ℝ`
  - positivity, cut-bound, balanced-identity, and slope-bound lemmas named in the approved spec.

- [ ] **Step 1: Prepare only the ignored local dependency link**

Run:

```bash
test -e vendor || ln -s ../../vendor vendor
git status --short --ignored | sed -n '1,40p'
```

Expected: `vendor` is ignored and no tracked source file changes.

- [ ] **Step 2: Write the failing exact-formula contract**

Create `Test/ZeroDensityLayerBudgetTwoHeightNumericalCoreContract.lean`:

```lean
import PrimeNumberTheorem.ZeroDensityLayerBudgetTwoHeightNumericalCore

namespace PrimeNumberTheorem

example (sigma : ℝ) :
    carlsonTwoHeightDensityExponent sigma =
      4 * sigma * (1 - sigma) := rfl

example (sigma alpha : ℝ) :
    carlsonTwoHeightBalancedCut sigma alpha =
      carlsonTwoHeightDensityExponent sigma * alpha /
        (carlsonTwoHeightDensityExponent sigma + 1) := rfl

example (beta sigma tau gamma : ℝ) :
    targetAmplitudeCarlsonTwoHeightLowExponent beta sigma tau gamma =
      carlsonTwoHeightDensityExponent sigma * gamma + tau - beta := rfl

example (beta sigma tau alpha gamma : ℝ) :
    targetAmplitudeCarlsonTwoHeightHighExponent
        beta sigma tau alpha gamma =
      carlsonTwoHeightDensityExponent sigma * alpha + tau - beta - gamma := rfl

example (sigma : ℝ) :
    targetAmplitudeCarlsonTwoHeightBalancedSlope sigma =
      carlsonTwoHeightDensityExponent sigma ^ 2 /
        (carlsonTwoHeightDensityExponent sigma + 1) := rfl

example (beta sigma tau alpha : ℝ) :
    targetAmplitudeCarlsonTwoHeightBalancedExponent beta sigma tau alpha =
      tau - beta +
        targetAmplitudeCarlsonTwoHeightBalancedSlope sigma * alpha := rfl

#check carlsonTwoHeightDensityExponent_pos
#check carlsonTwoHeightDensityExponent_lt_one
#check carlsonTwoHeightBalancedCut_pos
#check carlsonTwoHeightBalancedCut_lt_alpha
#check targetAmplitudeCarlsonTwoHeightLowExponent_balanced
#check targetAmplitudeCarlsonTwoHeightHighExponent_balanced
#check targetAmplitudeCarlsonTwoHeightBalancedSlope_pos
#check targetAmplitudeCarlsonTwoHeightBalancedSlope_lt_half

end PrimeNumberTheorem
```

- [ ] **Step 3: Run the contract and verify RED**

Run:

```bash
LEAN_NUM_THREADS=1 lake -Kjobs=1 env lean \
  Test/ZeroDensityLayerBudgetTwoHeightNumericalCoreContract.lean
```

Expected: failure because
`PrimeNumberTheorem.ZeroDensityLayerBudgetTwoHeightNumericalCore` does not
exist.  Do not accept a syntax, path, or dependency failure as the RED result.

- [ ] **Step 4: Implement the minimal numerical core**

Create `PrimeNumberTheorem/ZeroDensityLayerBudgetTwoHeightNumericalCore.lean`
with `import Mathlib`, namespace `PrimeNumberTheorem`, the six exact
definitions from the contract, and exactly these theorem signatures:

```lean
theorem carlsonTwoHeightDensityExponent_pos
    {sigma : ℝ} (hhalf : 1 / 2 < sigma) (hone : sigma < 1) :
    0 < carlsonTwoHeightDensityExponent sigma

theorem carlsonTwoHeightDensityExponent_lt_one
    {sigma : ℝ} (hhalf : 1 / 2 < sigma) :
    carlsonTwoHeightDensityExponent sigma < 1

theorem carlsonTwoHeightBalancedCut_pos
    {sigma alpha : ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (halpha : 0 < alpha) :
    0 < carlsonTwoHeightBalancedCut sigma alpha

theorem carlsonTwoHeightBalancedCut_lt_alpha
    {sigma alpha : ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (halpha : 0 < alpha) :
    carlsonTwoHeightBalancedCut sigma alpha < alpha

theorem targetAmplitudeCarlsonTwoHeightBalancedSlope_pos
    {sigma : ℝ} (hhalf : 1 / 2 < sigma) (hone : sigma < 1) :
    0 < targetAmplitudeCarlsonTwoHeightBalancedSlope sigma

theorem targetAmplitudeCarlsonTwoHeightLowExponent_balanced
    {beta sigma tau alpha : ℝ}
    (hden : carlsonTwoHeightDensityExponent sigma + 1 ≠ 0) :
    targetAmplitudeCarlsonTwoHeightLowExponent beta sigma tau
        (carlsonTwoHeightBalancedCut sigma alpha) =
      targetAmplitudeCarlsonTwoHeightBalancedExponent beta sigma tau alpha

theorem targetAmplitudeCarlsonTwoHeightHighExponent_balanced
    {beta sigma tau alpha : ℝ}
    (hden : carlsonTwoHeightDensityExponent sigma + 1 ≠ 0) :
    targetAmplitudeCarlsonTwoHeightHighExponent beta sigma tau alpha
        (carlsonTwoHeightBalancedCut sigma alpha) =
      targetAmplitudeCarlsonTwoHeightBalancedExponent beta sigma tau alpha

theorem targetAmplitudeCarlsonTwoHeightBalancedSlope_lt_half
    {sigma : ℝ} (hhalf : 1 / 2 < sigma) (hone : sigma < 1) :
    targetAmplitudeCarlsonTwoHeightBalancedSlope sigma < 1 / 2
```

Use only the audited algebraic proof bodies from these immutable sources:

```bash
git show 28105ae9^:PrimeNumberTheorem/ZeroDensityLayerBudgetCarlsonTwoHeightSplit.lean
git show 28105ae9^:PrimeNumberTheorem/ZeroDensityLayerBudgetTargetAmplitudeTwoHeightExponent.lean
```

Port only the six definitions and eight listed lemmas.  In particular, do
not port rectangle transfers, logarithmic majorants, asymptotic decay
theorems, canonical-threshold helpers, or strict-margin existence helpers.

- [ ] **Step 5: Register the implementation and contract roots**

Add to the existing `lean_lib PrimeNumberTheorem` roots in `lakefile.lean`:

```lean
    `PrimeNumberTheorem.ZeroDensityLayerBudgetTwoHeightNumericalCore,
```

Add to the existing test roots:

```lean
    `Test.ZeroDensityLayerBudgetTwoHeightNumericalCoreContract,
```

- [ ] **Step 6: Run GREEN checks serially**

Run, one command at a time:

```bash
LEAN_NUM_THREADS=1 lake -Kjobs=1 env lean \
  PrimeNumberTheorem/ZeroDensityLayerBudgetTwoHeightNumericalCore.lean
LEAN_NUM_THREADS=1 lake -Kjobs=1 env lean \
  Test/ZeroDensityLayerBudgetTwoHeightNumericalCoreContract.lean
```

Expected: both exit 0.

- [ ] **Step 7: Add and run the numerical-core axiom audit**

Create `Test/ZeroDensityLayerBudgetTwoHeightNumericalCoreAxiomAudit.lean`:

```lean
import PrimeNumberTheorem.ZeroDensityLayerBudgetTwoHeightNumericalCore

open PrimeNumberTheorem

#print axioms carlsonTwoHeightDensityExponent_pos
#print axioms carlsonTwoHeightDensityExponent_lt_one
#print axioms carlsonTwoHeightBalancedCut_pos
#print axioms carlsonTwoHeightBalancedCut_lt_alpha
#print axioms targetAmplitudeCarlsonTwoHeightLowExponent_balanced
#print axioms targetAmplitudeCarlsonTwoHeightHighExponent_balanced
#print axioms targetAmplitudeCarlsonTwoHeightBalancedSlope_pos
#print axioms targetAmplitudeCarlsonTwoHeightBalancedSlope_lt_half
```

Register `Test.ZeroDensityLayerBudgetTwoHeightNumericalCoreAxiomAudit` in
`lakefile.lean`, then run:

```bash
LEAN_NUM_THREADS=1 lake -Kjobs=1 env lean \
  Test/ZeroDensityLayerBudgetTwoHeightNumericalCoreAxiomAudit.lean
```

Expected: exit 0; every printed axiom is in the allowed trio.

- [ ] **Step 8: Commit the independently testable core**

Run:

```bash
git add lakefile.lean \
  PrimeNumberTheorem/ZeroDensityLayerBudgetTwoHeightNumericalCore.lean \
  Test/ZeroDensityLayerBudgetTwoHeightNumericalCoreContract.lean \
  Test/ZeroDensityLayerBudgetTwoHeightNumericalCoreAxiomAudit.lean
git diff --cached --check
git commit -m "feat: extract two-height numerical core"
```

---

### Task 2: Seven-parameter joint feasibility theorem

**Files:**
- Create: `Test/ZeroDensityLayerBudgetJointTwoHeightParameterFeasibilityContract.lean`
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightParameterFeasibility.lean`
- Create: `Test/ZeroDensityLayerBudgetJointTwoHeightParameterFeasibilityAxiomAudit.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes: all six definitions and eight lemmas from
  `ZeroDensityLayerBudgetTwoHeightNumericalCore`.
- Produces: `exists_jointTwoHeightTargetAmplitudeParameters` with the exact
  seven witnesses and conjunction type below.

- [ ] **Step 1: Write the failing exact theorem contract**

Create
`Test/ZeroDensityLayerBudgetJointTwoHeightParameterFeasibilityContract.lean`:

```lean
import PrimeNumberTheorem.ZeroDensityLayerBudgetJointTwoHeightParameterFeasibility

namespace PrimeNumberTheorem

#check
  (exists_jointTwoHeightTargetAmplitudeParameters :
    ∀ {beta : ℝ}, 2 / 3 < beta → beta < 1 →
      ∃ sigma tau alpha gammaLow gammaHigh epsilonLow epsilonHigh : ℝ,
        1 / 2 < sigma ∧
        sigma < tau ∧
        tau < beta ∧
        sigma < 1 ∧
        1 - beta < alpha ∧
        0 < alpha ∧
        alpha ≤ 1 ∧
        gammaLow = alpha / 2 ∧
        0 < gammaLow ∧
        gammaLow ≤ alpha ∧
        gammaHigh = carlsonTwoHeightBalancedCut sigma alpha ∧
        0 < gammaHigh ∧
        gammaHigh < alpha ∧
        0 < epsilonLow ∧
        0 < epsilonHigh ∧
        gammaLow + sigma - beta + epsilonLow < 0 ∧
        alpha + sigma - beta - gammaLow + epsilonLow < 0 ∧
        targetAmplitudeCarlsonTwoHeightLowExponent
            beta sigma tau gammaHigh + epsilonHigh < 0 ∧
        targetAmplitudeCarlsonTwoHeightHighExponent
            beta sigma tau alpha gammaHigh + epsilonHigh < 0)

end PrimeNumberTheorem
```

- [ ] **Step 2: Run the theorem contract and verify RED**

Run:

```bash
LEAN_NUM_THREADS=1 lake -Kjobs=1 env lean \
  Test/ZeroDensityLayerBudgetJointTwoHeightParameterFeasibilityContract.lean
```

Expected: failure because the imported joint-feasibility module does not
exist.  The core module must still compile independently.

- [ ] **Step 3: Implement the theorem without old analytic imports**

Read the complete, immutable theorem source with:

```bash
git show 71fe009e:PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightParameterFeasibility.lean
```

Use `apply_patch` to create
`PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightParameterFeasibility.lean`
from that exact source.  Preserve the module documentation, theorem statement,
and complete proof body byte-for-byte except for replacing its two old
analytic imports

```lean
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualTargetAmplitudeLowLayerTwoHeight
import PrimeNumberTheorem.ZeroDensityLayerBudgetTargetAmplitudeTwoHeightExponent
```

with the single pure import

```lean
import PrimeNumberTheorem.ZeroDensityLayerBudgetTwoHeightNumericalCore
```

The exact theorem type is already locked by the RED contract in Step 1.  The
preserved proof constructs:

```text
threshold = (3 * beta - 1) / 2
sigma = (1 / 2 + threshold) / 2
tauUpper = beta - slope * (1 - beta)
tau = (sigma + tauUpper) / 2
lowUpper = 2 * (beta - sigma)
highUpper = (beta - tau) / slope
cap = min 1 (min lowUpper highUpper)
alpha = ((1 - beta) + cap) / 2
gammaLow = alpha / 2
gammaHigh = carlsonTwoHeightBalancedCut sigma alpha
epsilonLow = -(gammaLow + sigma - beta) / 2
epsilonHigh =
  -targetAmplitudeCarlsonTwoHeightBalancedExponent beta sigma tau alpha / 2
```

Do not port any other declaration from the research branch.

- [ ] **Step 4: Register the implementation and contract roots**

Add to `lakefile.lean`:

```lean
    `PrimeNumberTheorem.ZeroDensityLayerBudgetJointTwoHeightParameterFeasibility,
    `Test.ZeroDensityLayerBudgetJointTwoHeightParameterFeasibilityContract,
```

- [ ] **Step 5: Run GREEN checks serially**

Run:

```bash
LEAN_NUM_THREADS=1 lake -Kjobs=1 env lean \
  PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightParameterFeasibility.lean
LEAN_NUM_THREADS=1 lake -Kjobs=1 env lean \
  Test/ZeroDensityLayerBudgetJointTwoHeightParameterFeasibilityContract.lean
```

Expected: both exit 0 with the theorem type unchanged from the RED contract.

- [ ] **Step 6: Add and run the joint theorem axiom audit**

Create
`Test/ZeroDensityLayerBudgetJointTwoHeightParameterFeasibilityAxiomAudit.lean`:

```lean
import PrimeNumberTheorem.ZeroDensityLayerBudgetJointTwoHeightParameterFeasibility

open PrimeNumberTheorem

#print axioms exists_jointTwoHeightTargetAmplitudeParameters
```

Register
`Test.ZeroDensityLayerBudgetJointTwoHeightParameterFeasibilityAxiomAudit` in
`lakefile.lean`, then run:

```bash
LEAN_NUM_THREADS=1 lake -Kjobs=1 env lean \
  Test/ZeroDensityLayerBudgetJointTwoHeightParameterFeasibilityAxiomAudit.lean
```

Expected: exit 0 and only the allowed axiom trio.

- [ ] **Step 7: Commit the joint theorem**

Run:

```bash
git add lakefile.lean \
  PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightParameterFeasibility.lean \
  Test/ZeroDensityLayerBudgetJointTwoHeightParameterFeasibilityContract.lean \
  Test/ZeroDensityLayerBudgetJointTwoHeightParameterFeasibilityAxiomAudit.lean
git diff --cached --check
git commit -m "feat: prove joint two-height parameter feasibility"
```

---

### Task 3: Scope, import, and final branch audit

**Files:**
- Verify: all six new Lean files
- Verify: `lakefile.lean`
- Verify: `docs/superpowers/specs/2026-08-02-joint-two-height-numerical-feasibility-design.md`
- Verify: `docs/superpowers/plans/2026-08-02-joint-two-height-numerical-feasibility.md`

**Interfaces:**
- Consumes: Tasks 1 and 2.
- Produces: fresh evidence that the Draft PR contains only numerical
  feasibility and is safe to publish directly against `main`.

- [ ] **Step 1: Verify the import boundary**

Run:

```bash
sed -n '1,8p' \
  PrimeNumberTheorem/ZeroDensityLayerBudgetTwoHeightNumericalCore.lean \
  PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightParameterFeasibility.lean
```

Expected: the core imports only Mathlib; the joint theorem imports only the
core.  No analytic project module appears.

- [ ] **Step 2: Run all six Lean targets serially and capture fresh output**

Run each separately:

```bash
LEAN_NUM_THREADS=1 lake -Kjobs=1 env lean PrimeNumberTheorem/ZeroDensityLayerBudgetTwoHeightNumericalCore.lean
LEAN_NUM_THREADS=1 lake -Kjobs=1 env lean Test/ZeroDensityLayerBudgetTwoHeightNumericalCoreContract.lean
LEAN_NUM_THREADS=1 lake -Kjobs=1 env lean Test/ZeroDensityLayerBudgetTwoHeightNumericalCoreAxiomAudit.lean
LEAN_NUM_THREADS=1 lake -Kjobs=1 env lean PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightParameterFeasibility.lean
LEAN_NUM_THREADS=1 lake -Kjobs=1 env lean Test/ZeroDensityLayerBudgetJointTwoHeightParameterFeasibilityContract.lean
LEAN_NUM_THREADS=1 lake -Kjobs=1 env lean Test/ZeroDensityLayerBudgetJointTwoHeightParameterFeasibilityAxiomAudit.lean
```

Expected: six exit codes 0; audit output contains no axiom outside the allowed
trio.

- [ ] **Step 3: Run forbidden declaration and incomplete-proof scans**

Run:

```bash
rg -n '\b(sorry|admit)\b|^\s*axiom\b' \
  PrimeNumberTheorem/ZeroDensityLayerBudgetTwoHeightNumericalCore.lean \
  PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightParameterFeasibility.lean \
  Test/ZeroDensityLayerBudgetTwoHeightNumericalCoreContract.lean \
  Test/ZeroDensityLayerBudgetTwoHeightNumericalCoreAxiomAudit.lean \
  Test/ZeroDensityLayerBudgetJointTwoHeightParameterFeasibilityContract.lean \
  Test/ZeroDensityLayerBudgetJointTwoHeightParameterFeasibilityAxiomAudit.lean

rg -n '^\s*(def|theorem|lemma|axiom)\s+.*(Zero|zero|Tail|tail|Smooth|smooth|Witness|witness)' \
  PrimeNumberTheorem/ZeroDensityLayerBudgetTwoHeightNumericalCore.lean \
  PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightParameterFeasibility.lean
```

Expected: both commands return no matches.  File names may contain
`ZeroDensityLayerBudget`; the declaration-name scan, not a raw word scan,
enforces the analytic boundary.

- [ ] **Step 4: Check stack diff, ignored artifacts, and claim wording**

Run:

```bash
git diff --check origin/main...HEAD
git diff --stat origin/main...HEAD
git status --short --ignored | sed -n '1,80p'
rg -n 'exclude.*zero|zero-free|actual.*tail.*(decay|small|zero)' \
  docs/superpowers/specs/2026-08-02-joint-two-height-numerical-feasibility-design.md \
  PrimeNumberTheorem/ZeroDensityLayerBudgetTwoHeightNumericalCore.lean \
  PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightParameterFeasibility.lean || true
```

Expected: only the design, plan, two implementation modules, four test files,
and `lakefile.lean` differ from `origin/main`; `.lake` and `vendor` are ignored; any
claim-wording matches occur only in explicit non-claim boundaries.

- [ ] **Step 5: Commit the implementation plan if still uncommitted**

Run:

```bash
git add docs/superpowers/plans/2026-08-02-joint-two-height-numerical-feasibility.md
git diff --cached --check
git commit -m "docs: plan joint two-height numerical feasibility"
```

If the plan was committed before execution, skip this step without creating
an empty commit.

- [ ] **Step 6: Publish only after verification**

After re-reading the approved spec line by line, use the GitHub publication
workflow to push `codex/joint-two-height-numerical-feasibility` and open a
Draft PR with base `main`.

The PR title must state numerical feasibility, not tail decay or zero
exclusion.  The body must include:

```text
Conclusion: for each fixed 2/3 < beta < 1, seven real parameters exist and
the four stated numerical exponents have explicit positive strict margins.

Not proved: an actual-zeta tail bound, smoothing/two-height transfer,
Sharp/Witness lower bound, Carlson contradiction, or zero-free half-plane.
```

Keep the PR Draft and do not merge it.
