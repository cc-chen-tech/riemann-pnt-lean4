# VK-edge Gaussian L2 and Positive Measure Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove a Gaussian-kernel weighted `L2` lower bound and positive logarithmic measure of strict `pi / 2` PNT-error oscillations in every sufficiently late epsilon power window.

**Architecture:** Strengthen the existing centered contour data before its supremum step, retain the exact projected Gaussian kernel as a weight, and apply a reusable weighted Cauchy-Schwarz inequality. Convert the resulting second-moment lower bound to positive measure by contradiction with an almost-everywhere threshold bound, then specialize Carlson's missing harmonic and the epsilon-window scaling.

**Tech Stack:** Lean 4, Mathlib Bochner integration and measure theory, existing VK-edge Gaussian/Mellin/contour modules.

## Global Constraints

- Work only in `.worktrees/vk-edge-pi-over-two-localized` on `research/vk-edge-pi-over-two-localized`.
- Preserve the strict coefficient greater than `Real.pi / 2`, analytic multiplicity, and the `1 / ‖rho‖` normalization encoded by `normalizedPsiError`.
- "Positive measure" means positive Lebesgue measure in the logarithmic variable.
- Do not claim a uniform positive proportion, separate signs, RH, or an unconditional square-root error bound.
- Use contracts first and verify that each contract fails because its new declaration is absent.
- No `sorry`, `admit`, or project `axiom`.

---

### Task 1: Weighted set-integral Cauchy-Schwarz

**Files:**
- Create: `MathlibAux/WeightedCauchySchwarz.lean`
- Create: `Test/WeightedCauchySchwarzContract.lean`
- Create: `Test/WeightedCauchySchwarzAxiomAudit.lean`

**Interfaces:**
- Consumes: measurable real functions, a measurable set, and integrability of `f^2 * w` and `w`.
- Produces:

```lean
sq_setIntegral_abs_mul_weight_le
```

with conclusion

```lean
(integral over s of |f| * w)^2
  <= (integral over s of f^2 * w) * (integral over s of w).
```

- [ ] **Step 1: Add the failing contract**

Pin the theorem with nonnegative measurable weight and both integrability
hypotheses.

- [ ] **Step 2: Verify the contract fails**

Run:

```bash
lake env lean Test/WeightedCauchySchwarzContract.lean
```

Expected: unknown import or unknown declaration.

- [ ] **Step 3: Implement through the `L2` Cauchy-Schwarz inequality**

Use `|f| * sqrt w` and `sqrt w`; reduce their squared norms using
`Real.sq_sqrt`.

- [ ] **Step 4: Build and audit**

```bash
lake env lean Test/WeightedCauchySchwarzContract.lean
lake env lean Test/WeightedCauchySchwarzAxiomAudit.lean
```

- [ ] **Step 5: Commit**

```bash
git commit -m "feat: add weighted integral Cauchy-Schwarz"
```

### Task 2: Preserve first and second moments in centered contour data

**Files:**
- Modify: `PrimeNumberTheorem/VKEdgePiOverTwoCenteredMissingHarmonicContour.lean`
- Modify: `Test/VKEdgePiOverTwoCenteredMissingHarmonicContourContract.lean`
- Modify: `Test/VKEdgePiOverTwoCenteredMissingHarmonicContourAxiomAudit.lean`

**Interfaces:**
- Consumes: the exact paired contour identity and projected Gaussian kernel.
- Produces fields and definitions for:

```lean
centeredNormalizedWindowFirstMoment
centeredNormalizedWindowSecondMoment
CenteredLocalizedContourData.kernel
CenteredLocalizedContourData.coefficient_eq_kernel_mass
CenteredLocalizedContourData.eventually_first_moment_bound
CenteredLocalizedContourData.eventually_second_moment_integrable
```

- [ ] **Step 1: Extend the contract first**

Pin the moment definitions and new structure projections.

- [ ] **Step 2: Verify failure**

Run the centered contour contract and confirm the new projections are absent.

- [ ] **Step 3: Refactor the existing inside-window proof**

Before applying the window supremum, retain

```lean
signal m <= centeredNormalizedWindowFirstMoment ... m + remainder m.
```

Derive the old supremum inequality from this new field so existing callers
remain unchanged.

- [ ] **Step 4: Prove integrability**

Use measurability of `normalizedPsiError`, integrability of the projected
kernel, and the already available boundedness of normalized error on the
compact window.

- [ ] **Step 5: Build, audit, and commit**

```bash
lake env lean Test/VKEdgePiOverTwoCenteredMissingHarmonicContourContract.lean
lake env lean Test/VKEdgePiOverTwoCenteredMissingHarmonicContourAxiomAudit.lean
git commit -m "feat: retain centered contour moments"
```

### Task 3: Gaussian weighted L2 extraction

**Files:**
- Create: `PrimeNumberTheorem/VKEdgePiOverTwoGaussianL2.lean`
- Create: `Test/VKEdgePiOverTwoGaussianL2Contract.lean`
- Create: `Test/VKEdgePiOverTwoGaussianL2AxiomAudit.lean`

**Interfaces:**
- Consumes: Task 1 weighted Cauchy-Schwarz and Task 2 contour moment fields.
- Produces:

```lean
CenteredLocalizedContourData.eventually_secondMoment_gt
eventually_centeredSharpenedNormalizedPsiError_secondMoment_gt
```

- [ ] **Step 1: Add a failing contract**

Pin the general threshold

```lean
C2 < 2 * multiplicity ^ 2 / mean.
```

- [ ] **Step 2: Verify failure**

Run the new contract and confirm the declaration is missing.

- [ ] **Step 3: Prove the ratio limit**

Show

```text
(signal - remainder)^2 / coefficient
  -> 2 * multiplicity^2 / mean.
```

- [ ] **Step 4: Apply weighted Cauchy-Schwarz**

Combine the eventual first-moment lower bound with positivity of
`signal - remainder` and `coefficient`.

- [ ] **Step 5: Specialize to the true zeta contour**

Expose the exact multiplicity and missing-harmonic denominator.

- [ ] **Step 6: Build, audit, and commit**

```bash
lake env lean Test/VKEdgePiOverTwoGaussianL2Contract.lean
lake env lean Test/VKEdgePiOverTwoGaussianL2AxiomAudit.lean
git commit -m "feat: prove Gaussian weighted PNT error L2 lower bound"
```

### Task 4: Positive logarithmic measure

**Files:**
- Create: `PrimeNumberTheorem/VKEdgePiOverTwoPositiveMeasure.lean`
- Create: `Test/VKEdgePiOverTwoPositiveMeasureContract.lean`
- Create: `Test/VKEdgePiOverTwoPositiveMeasureAxiomAudit.lean`

**Interfaces:**
- Consumes: Task 3 second-moment comparison.
- Produces:

```lean
CenteredLocalizedContourData.eventually_positive_measure_error_gt
eventually_positive_measure_normalizedPsiError_gt_strictPiOverTwo
exists_eventually_positive_measure_in_epsilonLogWindow_gt_strictPiOverTwo
```

- [ ] **Step 1: Add a failing contract**

Pin positive volume of

```lean
{y in localizedGaussianLogWindow q d m |
  C < |normalizedPsiError rho y|}.
```

- [ ] **Step 2: Verify failure**

Run the contract and confirm the positive-measure theorem is absent.

- [ ] **Step 3: Prove the null-set contradiction**

Assume the good set has zero measure. Replace the integrand almost everywhere
by its bad-set bound `C^2 * |kernel|`, contradicting

```text
secondMoment > C^2 * coefficient.
```

- [ ] **Step 4: Insert the strict harmonic constant**

Use

```lean
strictPiOverTwoOscillationConstant_lt_lowerBound
```

and Carlson's selected missing harmonic.

- [ ] **Step 5: Substitute epsilon scaling**

Rewrite the centered window as

```lean
Set.Icc (Real.log Y) ((1 + epsilon) * Real.log Y)
```

using `localizedGaussianLogWindow_epsilonGaussianScale`.

- [ ] **Step 6: Build, audit, and commit**

```bash
lake env lean Test/VKEdgePiOverTwoPositiveMeasureContract.lean
lake env lean Test/VKEdgePiOverTwoPositiveMeasureAxiomAudit.lean
git commit -m "feat: prove positive-measure epsilon-window oscillation"
```

### Task 5: Full verification

**Files:**
- Modify only inventory scripts if a new reusable `Prop` predicate requires classification.

- [ ] **Step 1: Run focused source scans**

```bash
rg -n '\b(sorry|admit)\b|^\s*axiom\b' \
  MathlibAux/WeightedCauchySchwarz.lean \
  PrimeNumberTheorem/VKEdgePiOverTwoGaussianL2.lean \
  PrimeNumberTheorem/VKEdgePiOverTwoPositiveMeasure.lean
```

- [ ] **Step 2: Run repository verification**

```bash
./scripts/verify-baseline.sh
lake build
git diff --check
```

- [ ] **Step 3: Record exact theorem boundary**

Document that the endpoint is conditional and gives positive logarithmic
measure, not a uniform density or sign-separated oscillation.
