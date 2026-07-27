# VK-edge Target-Pair Annihilator Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalize a symmetric finite-difference detector that annihilates one selected zeta zero pair, expose its exact action on the true PNT error, and isolate the arithmetic lower bound needed to force positive residual energy.

**Architecture:** Put the real-frequency algebra, zeta specialization, and local `L2` transfer in one focused module, `PrimeNumberTheorem/VKEdgeTargetPairAnnihilator.lean`. Fix public signatures in a contract module, audit their axioms separately, and record both the usable conditional bridge and the pure-pair/frequency-collision no-go results.

**Tech Stack:** Lean 4, Mathlib real trigonometry and interval integration, the existing `VKEdgeResidualAmplification` normalized error/residual API, Lake contract targets, repository verification scripts.

## Global Constraints

- Work only in `/Users/luicy/AI/Riemann/riemann-pnt-lean4/.worktrees/vk-edge-target-annihilator` on `research/vk-edge-target-annihilator`.
- Keep PR #25 and its worktree unchanged; this branch is stacked on commit `ce69836`.
- Do not duplicate or modify the zero-density iteration, half-isolated dichotomy, or Carlson shared cores.
- Do not add `sorry`, `admit`, project `axiom`, or theorem-shaped `def ... : Prop`.
- Do not claim positive residual energy, an additional zero, a Carlson contradiction, or RH without a proved true-prime lower bound after target annihilation.
- Add failing contract checks before each implementation step.

---

### Task 1: Symmetric Frequency Annihilator

**Files:**
- Create: `PrimeNumberTheorem/VKEdgeTargetPairAnnihilator.lean`
- Create: `Test/VKEdgeTargetPairAnnihilatorContract.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes: `PrimeNumberTheorem.VKEdgePiOverTwo.cosineZeroPair`.
- Produces:

```lean
def symmetricFrequencyAnnihilator
    (h gamma : ℝ) (f : ℝ → ℝ) (y : ℝ) : ℝ

theorem symmetricFrequencyAnnihilator_cosineZeroPair
    (h gamma m lambda phase y : ℝ) :
    symmetricFrequencyAnnihilator h gamma
        (cosineZeroPair m lambda phase) y =
      2 * (Real.cos (lambda * h) - Real.cos (gamma * h)) *
        cosineZeroPair m lambda phase y

theorem symmetricFrequencyAnnihilator_targetPair_eq_zero
    (h gamma m phase y : ℝ) :
    symmetricFrequencyAnnihilator h gamma
        (cosineZeroPair m gamma phase) y = 0
```

- [x] **Step 1: Add the failing contract and Lake target**

Create `Test/VKEdgeTargetPairAnnihilatorContract.lean`:

```lean
import PrimeNumberTheorem.VKEdgeTargetPairAnnihilator

open PrimeNumberTheorem.VKEdgePiOverTwo

#check symmetricFrequencyAnnihilator
#check symmetricFrequencyAnnihilator_cosineZeroPair
#check symmetricFrequencyAnnihilator_targetPair_eq_zero
```

Add `Test.VKEdgeTargetPairAnnihilatorContract` as a `lean_lib` root in
`lakefile.lean`.

- [x] **Step 2: Run the contract and confirm the expected failure**

Run:

```bash
lake build Test.VKEdgeTargetPairAnnihilatorContract
```

Expected: failure because the source module and declarations do not exist.

- [x] **Step 3: Implement the detector and multiplier identity**

Define:

```lean
def symmetricFrequencyAnnihilator
    (h gamma : ℝ) (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  f (y + h) - 2 * Real.cos (gamma * h) * f y + f (y - h)
```

Prove the multiplier identity by expanding `cosineZeroPair`,
`Real.cos_add`, and `Real.cos_sub`, then close the polynomial identity with
`ring`.  Derive target annihilation by setting `lambda = gamma`.

- [x] **Step 4: Verify and commit**

Run:

```bash
lake build Test.VKEdgeTargetPairAnnihilatorContract
git diff --check
```

Commit:

```bash
git add PrimeNumberTheorem/VKEdgeTargetPairAnnihilator.lean Test/VKEdgeTargetPairAnnihilatorContract.lean lakefile.lean
git commit -m "feat: add target-pair frequency annihilator"
```

### Task 2: Zeta Residual Identity and Three-Scale Prime Formula

**Files:**
- Modify: `PrimeNumberTheorem/VKEdgeTargetPairAnnihilator.lean`
- Modify: `Test/VKEdgeTargetPairAnnihilatorContract.lean`

**Interfaces:**
- Consumes:
  - `normalizedPsiError`
  - `normalizedTargetZeroPair`
  - `normalizedPsiResidual`
- Produces:

```lean
def annihilatedNormalizedPsiError
    (rho : ℂ) (h y : ℝ) : ℝ

theorem annihilatedNormalizedPsiError_eq_residual
    (rho : ℂ) (h y : ℝ) :
    annihilatedNormalizedPsiError rho h y =
      symmetricFrequencyAnnihilator h rho.im
        (normalizedPsiResidual rho) y

theorem annihilatedNormalizedPsiError_eq_threeScale
    (rho : ℂ) (h y : ℝ) :
    annihilatedNormalizedPsiError rho h y =
      ‖rho‖ * Real.exp (-rho.re * y) *
        (Real.exp (-rho.re * h) *
            (chebyshevPsi (Real.exp (y + h)) - Real.exp (y + h)) -
          2 * Real.cos (rho.im * h) *
            (chebyshevPsi (Real.exp y) - Real.exp y) +
          Real.exp (rho.re * h) *
            (chebyshevPsi (Real.exp (y - h)) - Real.exp (y - h)))
```

- [x] **Step 1: Extend the contract and confirm failure**

Add `#check` lines for all three declarations above, then run:

```bash
lake build Test.VKEdgeTargetPairAnnihilatorContract
```

Expected: failure at the first missing declaration.

- [x] **Step 2: Implement the zeta detector and residual identity**

Define:

```lean
def annihilatedNormalizedPsiError
    (rho : ℂ) (h y : ℝ) : ℝ :=
  symmetricFrequencyAnnihilator h rho.im (normalizedPsiError rho) y
```

Unfold `normalizedPsiResidual`, use linearity of
`symmetricFrequencyAnnihilator`, and rewrite the target-pair term with
`symmetricFrequencyAnnihilator_targetPair_eq_zero`.

- [x] **Step 3: Prove the exact three-scale formula**

Unfold `annihilatedNormalizedPsiError`, `symmetricFrequencyAnnihilator`,
and `normalizedPsiError`.  Rewrite:

```lean
Real.exp (-rho.re * (y + h))
  = Real.exp (-rho.re * y) * Real.exp (-rho.re * h)

Real.exp (-rho.re * (y - h))
  = Real.exp (-rho.re * y) * Real.exp (rho.re * h)
```

using `Real.exp_add` and ring normalization.  Finish by `ring`.

- [x] **Step 4: Verify and commit**

Run:

```bash
lake build Test.VKEdgeTargetPairAnnihilatorContract
git diff --check
```

Commit:

```bash
git add PrimeNumberTheorem/VKEdgeTargetPairAnnihilator.lean Test/VKEdgeTargetPairAnnihilatorContract.lean
git commit -m "feat: expose annihilated three-scale PNT error"
```

### Task 3: Explicit Local `L2` Transfer

**Files:**
- Modify: `PrimeNumberTheorem/VKEdgeTargetPairAnnihilator.lean`
- Modify: `Test/VKEdgeTargetPairAnnihilatorContract.lean`

**Interfaces:**
- Produces:

```lean
theorem sq_symmetricFrequencyAnnihilator_le
    (f : ℝ → ℝ) (h gamma y : ℝ) :
    symmetricFrequencyAnnihilator h gamma f y ^ 2 ≤
      12 * (f (y + h) ^ 2 + f y ^ 2 + f (y - h) ^ 2)

theorem integral_sq_symmetricFrequencyAnnihilator_le_of_shifted
    {f : ℝ → ℝ} {s : Set ℝ} {h gamma E : ℝ}
    (hplus : ∫ y in s, f (y + h) ^ 2 ≤ E)
    (hzero : ∫ y in s, f y ^ 2 ≤ E)
    (hminus : ∫ y in s, f (y - h) ^ 2 ≤ E)
    (hdet :
      IntegrableOn
        (fun y => symmetricFrequencyAnnihilator h gamma f y ^ 2) s) :
    ∫ y in s, symmetricFrequencyAnnihilator h gamma f y ^ 2 ≤
      36 * E
```

The final theorem may require explicit integrability hypotheses for the three
shifted squares if Mathlib's integral monotonicity cannot infer them from
`hdet`; the contract must record the final honest signature.

- [x] **Step 1: Add failing contract checks**

Add `#check` lines for the pointwise and integrated inequalities.  Run the
contract and confirm failure.

- [x] **Step 2: Prove the pointwise constant `12`**

Use:

```text
(a + b + c)^2 <= 3 * (a^2 + b^2 + c^2)
abs (cos t) <= 1
```

with `b = -2 * cos(gamma*h) * f y`.  Close the real algebra with `nlinarith`
after supplying `sq_nonneg` and `Real.neg_one_le_cos` /
`Real.cos_le_one`.

- [x] **Step 3: Integrate the pointwise inequality**

Apply `MeasureTheory.integral_mono_ae_restrict` on `s`, distribute the finite
sum with `integral_add`, and substitute `hplus`, `hzero`, and `hminus`.
Keep every integrability premise explicit.

- [x] **Step 4: Derive the zeta residual gate**

Add:

```lean
theorem integral_annihilatedNormalizedPsiError_sq_le_of_residual_shifts
    {rho : ℂ} {s : Set ℝ} {h E : ℝ}
    (hplus : ∫ y in s, normalizedPsiResidual rho (y + h) ^ 2 ≤ E)
    (hzero : ∫ y in s, normalizedPsiResidual rho y ^ 2 ≤ E)
    (hminus : ∫ y in s, normalizedPsiResidual rho (y - h) ^ 2 ≤ E)
    (hdet :
      IntegrableOn
        (fun y => annihilatedNormalizedPsiError rho h y ^ 2) s) :
    ∫ y in s, annihilatedNormalizedPsiError rho h y ^ 2 ≤ 36 * E
```

Prove it by rewriting with `annihilatedNormalizedPsiError_eq_residual` and
applying the generic theorem.

- [x] **Step 5: Verify and commit**

Run:

```bash
lake build Test.VKEdgeTargetPairAnnihilatorContract
git diff --check
```

Commit:

```bash
git add PrimeNumberTheorem/VKEdgeTargetPairAnnihilator.lean Test/VKEdgeTargetPairAnnihilatorContract.lean
git commit -m "theorem: transfer annihilator energy to zeta residual"
```

### Task 4: Collision and Pure-Pair No-go Audit

**Files:**
- Modify: `PrimeNumberTheorem/VKEdgeTargetPairAnnihilator.lean`
- Modify: `Test/VKEdgeTargetPairAnnihilatorContract.lean`
- Create: `docs/research/vk-edge-target-pair-annihilator-audit.md`

**Interfaces:**
- Produces:

```lean
theorem no_positive_lower_bound_on_pure_target_pair
    {h gamma m phase C a b : ℝ}
    (hC : 0 < C) (hab : a < b) :
    ¬ C * (b - a) ≤
      ∫ y in Set.Icc a b,
        symmetricFrequencyAnnihilator h gamma
          (cosineZeroPair m gamma phase) y ^ 2

theorem symmetricFrequencyAnnihilator_cosineZeroPair_eq_zero_iff
    {h gamma m lambda phase y : ℝ}
    (hm : m ≠ 0)
    (hy : Real.cos (lambda * y - phase) ≠ 0) :
    symmetricFrequencyAnnihilator h gamma
        (cosineZeroPair m lambda phase) y = 0 ↔
      Real.cos (lambda * h) = Real.cos (gamma * h)
```

- [ ] **Step 1: Add failing contract checks**

Extend the contract with the two no-go declarations and confirm the expected
failure.

- [ ] **Step 2: Prove the pure-pair impossibility**

Rewrite the integrand pointwise with
`symmetricFrequencyAnnihilator_targetPair_eq_zero`, simplify the integral to
zero, and use `hC` plus `hab` to prove `0 < C * (b-a)`.

- [ ] **Step 3: Prove the frequency-collision characterization**

Rewrite with the exact multiplier theorem.  The hypotheses `hm` and `hy`
make the cosine package value nonzero, so the product vanishes exactly when
the multiplier vanishes.

- [ ] **Step 4: Write the mathematical audit**

Record:

- exact selected-pair annihilation;
- exact other-frequency multiplier;
- the three-scale classical-prime correlation;
- the explicit residual `L2` transfer constant;
- why the selected zero alone gives no positive detector lower bound;
- why a fixed `h` can miss another frequency;
- the missing theorem: a uniform true-prime lower bound, possibly after
  choosing or averaging `h`;
- no additional zero, Carlson contradiction, or RH claim.

- [ ] **Step 5: Verify and commit**

Run:

```bash
lake build Test.VKEdgeTargetPairAnnihilatorContract
git diff --check
```

Commit:

```bash
git add PrimeNumberTheorem/VKEdgeTargetPairAnnihilator.lean Test/VKEdgeTargetPairAnnihilatorContract.lean docs/research/vk-edge-target-pair-annihilator-audit.md
git commit -m "audit: isolate target-annihilator arithmetic gate"
```

### Task 5: Axiom Audit and Full Verification

**Files:**
- Create: `Test/VKEdgeTargetPairAnnihilatorAxiomAudit.lean`
- Modify: `lakefile.lean`
- Modify: `docs/superpowers/plans/2026-07-27-vk-edge-target-annihilator.md`

**Interfaces:**
- Audits every public theorem introduced in Tasks 1-4.

- [ ] **Step 1: Add the axiom audit**

Create:

```lean
import PrimeNumberTheorem.VKEdgeTargetPairAnnihilator

#print axioms PrimeNumberTheorem.VKEdgePiOverTwo.symmetricFrequencyAnnihilator_cosineZeroPair
#print axioms PrimeNumberTheorem.VKEdgePiOverTwo.symmetricFrequencyAnnihilator_targetPair_eq_zero
#print axioms PrimeNumberTheorem.VKEdgePiOverTwo.annihilatedNormalizedPsiError_eq_residual
#print axioms PrimeNumberTheorem.VKEdgePiOverTwo.annihilatedNormalizedPsiError_eq_threeScale
#print axioms PrimeNumberTheorem.VKEdgePiOverTwo.integral_annihilatedNormalizedPsiError_sq_le_of_residual_shifts
#print axioms PrimeNumberTheorem.VKEdgePiOverTwo.no_positive_lower_bound_on_pure_target_pair
```

Add `Test.VKEdgeTargetPairAnnihilatorAxiomAudit` to `lakefile.lean`.

- [ ] **Step 2: Run focused verification**

Run:

```bash
lake build Test.VKEdgeTargetPairAnnihilatorContract
lake build Test.VKEdgeTargetPairAnnihilatorAxiomAudit
rg -n "sorry|admit|^[[:space:]]*axiom " PrimeNumberTheorem/VKEdgeTargetPairAnnihilator.lean Test/VKEdgeTargetPairAnnihilatorContract.lean Test/VKEdgeTargetPairAnnihilatorAxiomAudit.lean
git diff --check
```

Accept only `propext`, `Classical.choice`, and `Quot.sound`.

- [ ] **Step 3: Run repository verification**

Run:

```bash
./scripts/verify-baseline.sh
lake -Kjobs=1 build
```

- [ ] **Step 4: Confirm branch scope**

Run:

```bash
git status --short
git diff --stat ce69836..HEAD
git diff --name-only ce69836..HEAD
```

The diff must contain only this plan/spec, the new source, contract, audit,
research record, and `lakefile.lean`.

- [ ] **Step 5: Commit final audit state**

```bash
git add Test/VKEdgeTargetPairAnnihilatorAxiomAudit.lean lakefile.lean docs/superpowers/plans/2026-07-27-vk-edge-target-annihilator.md
git commit -m "test: audit target-pair annihilator gate"
```

- [ ] **Step 6: Push only after every verification succeeds**

```bash
git push -u origin research/vk-edge-target-annihilator
```

Create a Draft PR stacked on `research/vk-edge-residual-amplification` only
if the source theorem, contract, and audit bundle are complete.
