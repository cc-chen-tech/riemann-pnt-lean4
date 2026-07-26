# Swept Gaussian Local L2 Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Upgrade the conditional ordinary local PNT-error second-moment lower bound from explicit `sqrt (log Y)` order to explicit `log Y` order by sweeping the Gaussian scale across one epsilon window.

**Architecture:** A new focused module first proves a jointly measurable fixed-scale Gaussian majorant whose integral over the sweep parameter is uniformly bounded. A finite-rectangle Fubini theorem then integrates the existing weighted contour lower bound over a continuum of Gaussian centers. The final specialization uses the existing epsilon-window geometry at `ε / 2` and Carlson missing-harmonic selection.

**Tech Stack:** Lean 4, Mathlib measure theory and Gaussian integrals, existing `VKEdgePiOverTwoOrdinaryL2`, `CenteredLocalizedContourData`, and Carlson APIs.

## Global Constraints

- Work only in branch `research/vk-edge-swept-l2`.
- Base the implementation on commit `debc6bb`.
- Public constants must be explicit definitions and must not use `Classical.choose`.
- The final theorem remains conditional on a hypothetical zero with `1 / 2 < rho.re < 1`.
- Do not claim RH, a fixed-proportion large-value theorem, or a fourth-moment estimate.
- New source must contain no `sorry`, `admit`, or project `axiom`.

---

### Task 1: Contract-first public endpoint

**Files:**
- Create: `Test/VKEdgePiOverTwoSweptL2Contract.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes: `normalizedPsiError`, `missingHarmonicContourCenter`, and `analyticOrderNatAt`.
- Produces: the required public names for all later tasks.

- [ ] **Step 1: Write the failing contract**

```lean
import PrimeNumberTheorem.VKEdgePiOverTwoSweptL2

open Complex Filter MeasureTheory Set
open PrimeNumberTheorem
open PrimeNumberTheorem.VKEdgePiOverTwo

#check sweptGaussianEnvelope
#check exp_scaled_abs_mul_normalizedGaussian_le_sweptEnvelope
#check integral_sweptGaussianEnvelope_le
#check ordinarySecondMoment_linear_lower_of_sweptWeightedLower
#check epsilonSweepRatio
#check centeredSharpenedSweptOrdinaryL2Constant
#check exists_eventually_ordinarySecondMoment_in_epsilonLogWindow_gt_linear
```

- [ ] **Step 2: Register the contract root**

Add `Test.VKEdgePiOverTwoSweptL2Contract` to `lean_lib Contracts` in
`lakefile.lean`.

- [ ] **Step 3: Verify RED**

Run:

```bash
lake build Test.VKEdgePiOverTwoSweptL2Contract
```

Expected: failure because
`PrimeNumberTheorem.VKEdgePiOverTwoSweptL2` does not exist.

- [ ] **Step 4: Commit the red contract**

```bash
git add Test/VKEdgePiOverTwoSweptL2Contract.lean lakefile.lean
git commit -m "test: specify swept Gaussian local L2 endpoint"
```

### Task 2: Fixed-scale Gaussian sweep envelope

**Files:**
- Create: `PrimeNumberTheorem/VKEdgePiOverTwoSweptL2.lean`
- Test: `Test/VKEdgePiOverTwoSweptL2Contract.lean`

**Interfaces:**
- Consumes:
  `centeredSharpenedProjectedPsiKernel_abs_le_inv_sqrt`,
  `projectedPsiKernelAtCenter_abs_le_scaled_exp_abs_mul`, and
  `integral_gaussian`.
- Produces:

```lean
def sweptGaussianEnvelope
    (q M R m y : ℝ) : ℝ

theorem exp_scaled_abs_mul_normalizedGaussian_le_sweptEnvelope
    {q M R m y : ℝ}
    (hM : 1 ≤ M) (hR : 1 ≤ R)
    (hmLower : M ≤ m) (hmUpper : m ≤ R * M) :
    Real.exp |(Real.sqrt m)⁻¹ * (q * m - y)| *
        normalizedGaussian m (q * m - y) ≤
      sweptGaussianEnvelope q M R m y

theorem integral_sweptGaussianEnvelope_le
    {q M R y : ℝ}
    (hq : 0 < q) (hM : 0 < M) (hR : 0 < R) :
    (∫ m in Set.Icc M (R * M),
        sweptGaussianEnvelope q M R m y) ≤
      Real.exp 2 * Real.sqrt (2 * R) / q
```

- [ ] **Step 1: Define the envelope**

Use

```lean
def sweptGaussianEnvelope (q M R m y : ℝ) : ℝ :=
  Real.exp 2 / (2 * Real.sqrt (Real.pi * M)) *
    Real.exp (-(q * m - y) ^ 2 / (8 * R * M))
```

- [ ] **Step 2: Prove completion of the square**

Reduce to

```lean
|t| / Real.sqrt m - t ^ 2 / (4 * m)
  ≤ 2 - t ^ 2 / (8 * m)
```

using `sq_nonneg (|t| / Real.sqrt m - 4)`.

- [ ] **Step 3: Compare variable and fixed scales**

Use `M ≤ m ≤ R * M` to replace the Gaussian denominator by
`sqrt (pi * M)` and the exponent denominator by `8 * R * M`.

- [ ] **Step 4: Integrate the affine Gaussian**

Majorize the `Icc` integral by the full real integral, apply the affine
change `u = q * m - y`, and use `integral_gaussian`.

- [ ] **Step 5: Run the focused build**

```bash
lake build PrimeNumberTheorem.VKEdgePiOverTwoSweptL2 \
  Test.VKEdgePiOverTwoSweptL2Contract
```

Expected: the three envelope declarations compile; later contract names
remain absent until subsequent tasks.

- [ ] **Step 6: Commit**

```bash
git add PrimeNumberTheorem/VKEdgePiOverTwoSweptL2.lean
git commit -m "feat: bound swept Gaussian kernel mass"
```

### Task 3: Finite-rectangle Fubini transfer

**Files:**
- Modify: `PrimeNumberTheorem/VKEdgePiOverTwoSweptL2.lean`
- Test: `Test/VKEdgePiOverTwoSweptL2Contract.lean`

**Interfaces:**
- Consumes: the sweep envelope mass bound from Task 2.
- Produces:

```lean
theorem ordinarySecondMoment_linear_lower_of_sweptWeightedLower
    {q d M R a b C2 K : ℝ} {rho : ℂ} {k : ℕ}
    (hM : 1 ≤ M) (hq : 0 < q) (hR : 1 < R)
    (hwindow :
      ∀ m ∈ Set.Icc M (R * M),
        localizedGaussianLogWindow q d m ⊆ Set.Icc a b)
    (hweighted :
      ∀ m ∈ Set.Icc M (R * M),
        C2 <
          centeredNormalizedWindowSecondMoment q d rho
            (centeredSharpenedProjectedPsiKernel q rho k) m)
    ... :
    C2 * (R - 1) * M ≤
      K * (Real.exp 2 * Real.sqrt (2 * R) / q) *
        ∫ y in Set.Icc a b, normalizedPsiError rho y ^ 2
```

- [ ] **Step 1: Prove joint measurability of the explicit envelope**

On `M > 0` and `R > 0`, prove measurability of

```lean
fun p : ℝ × ℝ =>
  normalizedPsiError rho p.2 ^ 2 *
    sweptGaussianEnvelope q M R p.1 p.2
```

by combining the existing measurability of `normalizedPsiError` with
continuity of the explicit envelope.

- [ ] **Step 2: Prove compact-rectangle integrability**

Use `ContinuousOn.integrableOn_compact` for the envelope factor and the
explicit compact bound for `normalizedPsiError rho` already established in
`VKEdgePiOverTwoOrdinaryL2`.

- [ ] **Step 3: Majorize each true weighted moment**

For every `m` in the sweep interval:

1. use the true-kernel pointwise envelope;
2. use `hwindow` to enlarge the local y-window to `[a,b]`;
3. obtain

```lean
C2 ≤ ∫ y in Set.Icc a b,
  normalizedPsiError rho y ^ 2 *
    K * sweptGaussianEnvelope q M R m y
```

- [ ] **Step 4: Integrate in `m` and swap**

Integrate the preceding inequality over `Icc M (R * M)`, use the exact
interval measure `(R - 1) * M`, apply `integral_integral_swap`, and then
use `integral_sweptGaussianEnvelope_le`.

- [ ] **Step 5: Run focused build and commit**

```bash
lake build PrimeNumberTheorem.VKEdgePiOverTwoSweptL2 \
  Test.VKEdgePiOverTwoSweptL2Contract
git add PrimeNumberTheorem/VKEdgePiOverTwoSweptL2.lean
git commit -m "feat: transfer swept Gaussian energy to ordinary L2"
```

### Task 4: Epsilon sweep geometry

**Files:**
- Modify: `PrimeNumberTheorem/VKEdgePiOverTwoSweptL2.lean`
- Test: `Test/VKEdgePiOverTwoSweptL2Contract.lean`

**Interfaces:**
- Consumes: `epsilonCenterCoefficient`,
  `epsilonRadiusCoefficient`, and
  `localizedGaussianLogWindow_epsilonGaussianScale`.
- Produces:

```lean
def epsilonSweepRatio (ε : ℝ) : ℝ :=
  (1 + ε) / (1 + ε / 2)

theorem one_lt_epsilonSweepRatio {ε : ℝ} (hε : 0 < ε) :
  1 < epsilonSweepRatio ε

theorem localizedGaussianLogWindow_subset_epsilonWindow_of_mem_sweep
    {ε Y m : ℝ} (hε : 0 < ε) (hY : 1 < Y)
    (hm : m ∈ Set.Icc
      (epsilonGaussianScale (ε / 2) Y)
      (epsilonSweepRatio ε *
        epsilonGaussianScale (ε / 2) Y)) :
    localizedGaussianLogWindow
        (epsilonCenterCoefficient (ε / 2))
        (epsilonRadiusCoefficient (ε / 2)) m ⊆
      Set.Icc (Real.log Y) ((1 + ε) * Real.log Y)
```

- [ ] **Step 1: Prove ratio positivity and strictness**

Use `hε`, positivity of `1 + ε / 2`, and field simplification.

- [ ] **Step 2: Prove lower endpoint containment**

From `m ≥ epsilonGaussianScale (ε/2) Y`, multiply by
`q - d > 0`.

- [ ] **Step 3: Prove upper endpoint containment**

Use

```lean
(q + d) / (q - d) = 1 + ε / 2
```

and the definition of `epsilonSweepRatio` to obtain the exact upper
endpoint `(1 + ε) * log Y`.

- [ ] **Step 4: Build and commit**

```bash
lake build PrimeNumberTheorem.VKEdgePiOverTwoSweptL2 \
  Test.VKEdgePiOverTwoSweptL2Contract
git add PrimeNumberTheorem/VKEdgePiOverTwoSweptL2.lean
git commit -m "feat: fit a Gaussian sweep inside epsilon windows"
```

### Task 5: Zeta specialization and explicit linear constant

**Files:**
- Modify: `PrimeNumberTheorem/VKEdgePiOverTwoSweptL2.lean`
- Test: `Test/VKEdgePiOverTwoSweptL2Contract.lean`

**Interfaces:**
- Consumes: Carlson missing-harmonic selection, the eventual weighted
  second-moment theorem, Tasks 2--4.
- Produces:

```lean
def centeredSharpenedSweptOrdinaryL2Constant
    (ε : ℝ) (rho : ℂ) (k : ℕ) : ℝ

theorem exists_eventually_ordinarySecondMoment_in_epsilonLogWindow_gt_linear
    {ε : ℝ} {rho : ℂ} {sigma : ℝ}
    (hε : 0 < ε)
    (hgamma : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (hσ : 1 / 2 < sigma)
    (hσrho : sigma < rho.re)
    (hrhoRe1 : rho.re < 1) :
    ∃ k : ℕ,
      riemannZeta (missingHarmonicContourCenter rho k) ≠ 0 ∧
      0 < centeredSharpenedSweptOrdinaryL2Constant ε rho k ∧
      ∀ᶠ Y : ℝ in Filter.atTop,
        centeredSharpenedSweptOrdinaryL2Constant ε rho k *
            Real.log Y <
          ∫ y in Set.Icc (Real.log Y) ((1 + ε) * Real.log Y),
            normalizedPsiError rho y ^ 2
```

- [ ] **Step 1: Define all named constants**

Use `ε / 2`, `epsilonSweepRatio ε`,
`centeredSharpenedProjectedPsiKernelEnvelopeConstant`, analytic
multiplicity, and `sharpenedMissingHarmonicDenominator`.

- [ ] **Step 2: Select the missing harmonic**

Call `exists_missing_oddHarmonic_with_strict_gap_of_carlson` exactly as in
the PR #22 endpoint.

- [ ] **Step 3: Obtain a uniform weighted lower bound over the sweep**

Specialize
`eventually_centeredSharpenedNormalizedPsiError_secondMoment_gt` with

```lean
C2 =
  (analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 /
    sharpenedMissingHarmonicDenominator k
```

and convert eventual-atTop membership into a bound for every
`m ∈ Icc M (R * M)` once `M` is sufficiently large.

- [ ] **Step 4: Apply the sweep transfer**

Use Task 4 for window containment and Task 3 for the linear ordinary
second-moment lower bound. The public constant is one half of the raw
ratio, yielding a strict inequality.

- [ ] **Step 5: Prove explicit constant positivity**

Use positivity of multiplicity, the missing-harmonic denominator, kernel
envelope constant, `q`, `q-d`, and `R-1`.

- [ ] **Step 6: Build and commit**

```bash
lake build PrimeNumberTheorem.VKEdgePiOverTwoSweptL2 \
  Test.VKEdgePiOverTwoSweptL2Contract
git add PrimeNumberTheorem/VKEdgePiOverTwoSweptL2.lean \
  Test/VKEdgePiOverTwoSweptL2Contract.lean
git commit -m "feat: prove linear local PNT error L2 lower bound"
```

### Task 6: Axiom audit, contradiction boundary, and full verification

**Files:**
- Create: `Test/VKEdgePiOverTwoSweptL2AxiomAudit.lean`
- Create: `docs/research/vk-edge-swept-l2-contradiction-audit.md`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes: final public declarations.
- Produces: verification evidence and the next exact RH-route blocker.

- [ ] **Step 1: Add the axiom audit**

```lean
import PrimeNumberTheorem.VKEdgePiOverTwoSweptL2

open PrimeNumberTheorem.VKEdgePiOverTwo

#print axioms exp_scaled_abs_mul_normalizedGaussian_le_sweptEnvelope
#print axioms integral_sweptGaussianEnvelope_le
#print axioms ordinarySecondMoment_linear_lower_of_sweptWeightedLower
#print axioms exists_eventually_ordinarySecondMoment_in_epsilonLogWindow_gt_linear
```

- [ ] **Step 2: Register the source, contract, and audit roots**

Add:

```lean
PrimeNumberTheorem.VKEdgePiOverTwoSweptL2
Test.VKEdgePiOverTwoSweptL2Contract
Test.VKEdgePiOverTwoSweptL2AxiomAudit
```

to the corresponding `lakefile.lean` libraries.

- [ ] **Step 3: Document the new comparison**

Record that:

1. the new second moment is linear in window length;
2. a fourth moment `O(log Y)` would now yield fixed-proportion measure;
3. existing unconditional pointwise PNT bounds give exponentially larger
   fourth moments after normalization and do not yield a contradiction;
4. an independent upper bound contradicting the linear lower bound for
   every `beta > 1/2` would imply RH by functional-equation symmetry.

- [ ] **Step 4: Run focused verification**

```bash
lake build PrimeNumberTheorem.VKEdgePiOverTwoSweptL2 \
  Test.VKEdgePiOverTwoSweptL2Contract \
  Test.VKEdgePiOverTwoSweptL2AxiomAudit
```

- [ ] **Step 5: Run repository verification**

```bash
./scripts/verify-baseline.sh
git diff --check
rg -n '\b(sorry|admit|axiom)\b' \
  PrimeNumberTheorem/VKEdgePiOverTwoSweptL2.lean \
  Test/VKEdgePiOverTwoSweptL2Contract.lean \
  Test/VKEdgePiOverTwoSweptL2AxiomAudit.lean
```

- [ ] **Step 6: Commit**

```bash
git add Test/VKEdgePiOverTwoSweptL2AxiomAudit.lean \
  docs/research/vk-edge-swept-l2-contradiction-audit.md lakefile.lean
git commit -m "test: audit swept Gaussian local L2 theorem"
```

- [ ] **Step 7: Publish a dependent Draft PR**

Push `research/vk-edge-swept-l2`. If PR #22 is still unmerged, target the
Draft PR at `research/vk-edge-ordinary-l2`; otherwise rebase on current
`main` and target `main`.
