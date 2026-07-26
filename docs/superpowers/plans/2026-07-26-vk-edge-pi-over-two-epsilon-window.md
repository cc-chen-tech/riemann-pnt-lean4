# VK-edge Pi-over-two Epsilon-window Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task. Steps use
> checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove that every fixed off-critical-line zeta zero forces a
strictly greater than `pi / 2`, multiplicity-sensitive Chebyshev-error
oscillation in every sufficiently late interval `[Y, Y^(1+ε)]`, for every
fixed `ε > 0`.

**Architecture:** Keep the existing center-16, power-seven theorem unchanged.
Build parallel center-parametric Gaussian, Mellin, contour, tail, and
localized-data layers. Specialize them using explicit
`qε ≍ ε⁻²` and `dε ≍ ε⁻¹` constants only in the final transfer module.

**Tech Stack:** Lean 4.29.1, Mathlib, the verified
`VKEdgePiOverTwo*` contour stack, contract files, `#print axioms`, and the
repository baseline verifier.

## Global Constraints

- Work only on `research/vk-edge-pi-over-two-localized`.
- Preserve all existing `[Y,Y^7]` public APIs and theorem statements.
- Do not introduce `sorry`, `admit`, or a project-defined `axiom`.
- Do not encode Schlage-Puchta, Bellotti, or any other external theorem as an
  unproved Lean assumption.
- The final coefficient must remain
  `strictPiOverTwoOscillationConstant k`; no weakening to `pi / 2 - ε`.
- The final scale must remain
  `(analyticOrderNatAt riemannZeta rho : ℝ) *
   (x ^ rho.re / ‖rho‖)`.
- Constants and the eventual threshold may depend on the fixed `ε`, zero,
  filter, and harmonic.
- A bare Gaussian-tail estimate is insufficient: the true
  `normalizedPsiError * projected kernel` tail must tend to zero.
- Do not claim RH, an unconditional square-root bound, or historical novelty.

---

### Task 1: Parametric Window Arithmetic and Psi Transfer

**Files:**
- Create: `PrimeNumberTheorem/VKEdgePiOverTwoEpsilonWindow.lean`
- Create: `Test/VKEdgePiOverTwoEpsilonWindowContract.lean`
- Create: `Test/VKEdgePiOverTwoEpsilonWindowAxiomAudit.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes:
  `PrimeNumberTheorem.VKEdgePiOverTwo.normalizedPsiError`.
- Produces:
  `localizedGaussianLogWindow`,
  `powerOnePlusEpsilonWindow`,
  `epsilonCenterCoefficient`,
  `epsilonRadiusCoefficient`,
  `epsilonGaussianScale`,
  `localizedGaussianLogWindow_epsilonGaussianScale`,
  `exists_psiError_in_powerOnePlusEpsilonWindow_of_normalizedPsiError`.

- [ ] **Step 1: Write the failing contract**

The contract checks:

```lean
#check localizedGaussianLogWindow
#check powerOnePlusEpsilonWindow
#check epsilonCenterCoefficient
#check epsilonRadiusCoefficient
#check epsilonGaussianScale
#check epsilonRadiusCoefficient_pos
#check epsilonRadiusCoefficient_lt_center
#check epsilonRadius_sq_ge_thirtyTwo_mul
#check localizedGaussianLogWindow_epsilonGaussianScale
#check exists_psiError_in_powerOnePlusEpsilonWindow_of_normalizedPsiError
```

Run:

```bash
lake env lean Test/VKEdgePiOverTwoEpsilonWindowContract.lean
```

Expected: failure because the imported production module does not exist.

- [ ] **Step 2: Implement the explicit parameters**

Use exactly:

```lean
def localizedGaussianLogWindow (q d m : ℝ) : Set ℝ :=
  Set.Icc ((q - d) * m) ((q + d) * m)

def powerOnePlusEpsilonWindow (ε Y : ℝ) : Set ℝ :=
  Set.Icc Y (Y ^ (1 + ε))

def epsilonCenterCoefficient (ε : ℝ) : ℝ :=
  64 * (2 + ε) ^ 2 / ε ^ 2

def epsilonRadiusCoefficient (ε : ℝ) : ℝ :=
  64 * (2 + ε) / ε

def epsilonGaussianScale (ε Y : ℝ) : ℝ :=
  Real.log Y /
    (epsilonCenterCoefficient ε - epsilonRadiusCoefficient ε)
```

For `0 < ε`, prove positivity, `dε < qε`,

```lean
32 * (qε + dε) ≤ dε ^ 2
```

and

```lean
(qε + dε) / (qε - dε) = 1 + ε.
```

- [ ] **Step 3: Prove exact window identification**

Define the logarithmic target interval as
`Set.Icc (Real.log Y) ((1 + ε) * Real.log Y)` and prove:

```lean
theorem localizedGaussianLogWindow_epsilonGaussianScale
    {ε : ℝ} (hε : 0 < ε) (Y : ℝ) :
    localizedGaussianLogWindow
        (epsilonCenterCoefficient ε)
        (epsilonRadiusCoefficient ε)
        (epsilonGaussianScale ε Y) =
      Set.Icc (Real.log Y) ((1 + ε) * Real.log Y)
```

- [ ] **Step 4: Prove the standard-psi transfer**

For `rho ≠ 0`, `ε > 0`, and `Y ≥ 1`, turn a normalized-error witness in the
logarithmic interval into:

```lean
∃ x ∈ powerOnePlusEpsilonWindow ε Y,
  C * (x ^ rho.re / ‖rho‖) < |chebyshevPsi x - x|
```

Use `Real.rpow_def_of_pos` for the upper endpoint; do not assume continuity
of `chebyshevPsi`.

- [ ] **Step 5: Verify and commit**

Run the contract and axiom audit, scan the new source for forbidden
placeholders, and commit:

```bash
git commit -m "feat: parameterize epsilon power windows"
```

### Task 2: Center-parametric Gaussian-Mellin Transform

**Files:**
- Create: `PrimeNumberTheorem/VKEdgePiOverTwoCenteredMellin.lean`
- Create: `Test/VKEdgePiOverTwoCenteredMellinContract.lean`
- Create: `Test/VKEdgePiOverTwoCenteredMellinAxiomAudit.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes:
  `integral_verticalPolynomialGaussian_add_mul_eq`,
  `polynomialGaussianKernel`,
  `polynomialGaussianKernelDeriv`.
- Produces:
  `localizedGaussianWeightAtCenter`,
  `localizedPsiGaussianAverageAtCenter`,
  `integral_rightEdgePolynomialGaussian_cpow_atCenter_eq`,
  `integral_localizedGaussianWeightAtCenter_mul_regularizedLogDeriv_rightEdge_eq`.

- [ ] **Step 1: Write a failing contract**

Pin the centered weight:

```lean
def localizedGaussianWeightAtCenter
    (q : ℝ) (A : ℂ[X]) (w : ℂ) (m : ℝ) (z : ℂ) : ℂ :=
  A.eval (z - w) *
    Complex.exp
      ((m : ℂ) * (z - w) ^ 2 +
        ((q * m : ℝ) : ℂ) * (z - w))
```

and a centered Chebyshev average whose inverse kernel is evaluated at
`q * m - Real.log x`.

- [ ] **Step 2: Prove the centered right-edge Gaussian identity**

Repeat the existing right-edge calculation with
`r = q * m - Real.log x`. The vertical Gaussian theorem already accepts an
arbitrary `r`; do not duplicate its Fourier proof.

- [ ] **Step 3: Prove integrability and Mellin interchange**

Generalize the existing right-edge integrability proof. Constants may depend
on fixed `q`; the theorem needs only `0 < m`, `0 < w.re`.

- [ ] **Step 4: Add compatibility lemmas**

Prove that specializing `q = 16` recovers the existing weight and average:

```lean
localizedGaussianWeightAtCenter 16 A w m =
  localizedGaussianWeight A w m

localizedPsiGaussianAverageAtCenter 16 A w m =
  localizedPsiGaussianAverage A w m
```

- [ ] **Step 5: Verify and commit**

Run focused contract/audit and commit:

```bash
git commit -m "feat: parameterize localized Gaussian center"
```

### Task 3: Center-parametric Exact Zeta Contour

**Files:**
- Create: `PrimeNumberTheorem/VKEdgePiOverTwoCenteredContour.lean`
- Create: `Test/VKEdgePiOverTwoCenteredContourContract.lean`
- Create: `Test/VKEdgePiOverTwoCenteredContourAxiomAudit.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes:
  `exists_weightedExplicitFormula_boundaryRectIntegral_eq_residue_sum`,
  Task 2 centered weight and right-edge Mellin identity.
- Produces:
  `localizedRegularizedLogDerivIntegrandAtCenter`,
  `localizedZeroResidueSumAtCenter`,
  `localizedContourRemainderAtCenter`,
  and an exact finite-height contour identity.

- [ ] **Step 1: Write the failing contract**

Require the exact identity:

```lean
localizedPsiGaussianAverageAtCenter q A w m =
  -(2 * Real.pi : ℂ) *
      localizedZeroResidueSumAtCenter q A w m zeros +
    localizedContourRemainderAtCenter q A w m u T
```

under the same boundary-zero hypotheses as the existing center-16 theorem.

- [ ] **Step 2: Define centered residue and edge terms**

Replace only `localizedGaussianWeight` by
`localizedGaussianWeightAtCenter q`. Keep residues equal to negative analytic
multiplicity and retain exact cancellation at `s = 0` and `s = 1`.

- [ ] **Step 3: Assemble the rectangle**

Reuse the general analytic-weight residue theorem and Task 2 right-edge
identity. Do not reprove the argument principle.

- [ ] **Step 4: Prove center-16 compatibility**

Show each centered object at `q = 16` equals its existing counterpart.

- [ ] **Step 5: Verify and commit**

Run focused checks and commit:

```bash
git commit -m "feat: parameterize localized zeta contour"
```

### Task 4: Uniform Edge Decay for a Fixed Center Coefficient

**Files:**
- Create: `PrimeNumberTheorem/VKEdgePiOverTwoCenteredContourDecay.lean`
- Create: `Test/VKEdgePiOverTwoCenteredContourDecayContract.lean`
- Create: `Test/VKEdgePiOverTwoCenteredContourDecayAxiomAudit.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes:
  Task 3 exact contour and the existing `goodHeight` construction.
- Produces:
  `centeredPoleRadius`,
  `CenteredConcreteLocalizedContourSlice`,
  `selectedLocalizedZeroResidueSumAtCenter`,
  `selectedLocalizedContourRemainderAtCenter`,
  and their limit/decay theorems for every fixed `q > 0`.

- [ ] **Step 1: Write the failing limit contract**

Require a selected exact identity and:

```lean
Tendsto
  (selectedLocalizedContourRemainderAtCenter q A u v)
  atTop (𝓝 0)
```

under `0 < q`, `0 < u`, `u < 1`.

- [ ] **Step 2: Prove the enlarged far-zero radius margin**

Define:

```lean
def centeredPoleRadius (q : ℝ) : ℝ := q + 5
```

For `0 < q` and every real-part displacement `a` with `|a| ≤ 1`, prove:

```lean
a ^ 2 + q * a - centeredPoleRadius q ^ 2 ≤ -8
```

Use `centeredPoleRadius q` in the near-zero filter and far-zero split. The
filter degree may depend on fixed `q`.

- [ ] **Step 3: Generalize edge envelopes**

Carry `q` through the right, left, top, and bottom edge bounds. Allow envelope
constants to depend on fixed `q`.

- [ ] **Step 4: Keep the good-height scale**

Use
`T ∈ Set.Icc (12 * m + |v|) (12 * m + |v| + 1)`.
Prove that the negative `-m*T^2` term dominates the fixed-`q` linear
contribution on horizontal edges. Also prove that this height eventually
exceeds the fixed `centeredPoleRadius q`.

- [ ] **Step 5: Select concrete slices and prove decay**

Mirror the existing `ConcreteLocalizedContourSlice` construction with `q`
added as a parameter. The selected definitions extend invalid small scales
by zero exactly as before.

- [ ] **Step 6: Verify and commit**

Run focused checks and commit:

```bash
git commit -m "feat: control centered localized contour edges"
```

### Task 5: Radius-parametric True Psi Tail

**Files:**
- Create: `PrimeNumberTheorem/VKEdgePiOverTwoCenteredPsiWindow.lean`
- Create: `Test/VKEdgePiOverTwoCenteredPsiWindowContract.lean`
- Create: `Test/VKEdgePiOverTwoCenteredPsiWindowAxiomAudit.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes:
  Task 1 window, Task 2 centered average, and polynomial-Gaussian envelope
  bounds.
- Produces:
  `projectedPsiKernelAtCenter`,
  `relativeProjectedPsiKernelAtCenter`,
  `projectedPsiTailRemainderAtCenter`,
  `relativeProjectedPsiTailRemainderAtCenter`,
  and their zero limits.

- [ ] **Step 1: Write the failing tail contract**

The final public theorem must have explicit hypotheses:

```lean
(hq : 0 < q) (hd : 0 < d) (hdq : d < q)
(hmargin : 16 * (q + d) ≤ d ^ 2)
```

and conclude:

```lean
Tendsto
  (projectedPsiTailRemainderAtCenter q d A
    ((u : ℂ) + I * v))
  atTop (𝓝 0)
```

- [ ] **Step 2: Prove centered logarithmic-coordinate identity**

Generalize the exact change of variables from `x` to `y`, with kernel
argument `q * m - y`.

- [ ] **Step 3: Prove the pointwise true-tail envelope**

For `t = q*m-y` and
`y ∉ localizedGaussianLogWindow q d m`, combine:

```text
|normalizedPsiError| ≤ N * exp ((1-u)*y)
|projected kernel| ≤
  C * exp (|t|/sqrt m) * normalizedGaussian m t
```

with `hmargin`. Derive an exponentially decaying integrable Gaussian
majorant for all sufficiently large `m`.

- [ ] **Step 4: Integrate and prove both tail limits**

Prove the direct and relative tail remainders tend to zero. The relative
version must preserve target normalization and may not silently replace
`target` by `center`.

- [ ] **Step 5: Verify and commit**

Run focused checks and commit:

```bash
git commit -m "feat: control epsilon-window psi tails"
```

### Task 6: Centered Missing-harmonic Contour Data

**Files:**
- Create: `PrimeNumberTheorem/VKEdgePiOverTwoCenteredMissingHarmonicContour.lean`
- Create: `Test/VKEdgePiOverTwoCenteredMissingHarmonicContourContract.lean`
- Create: `Test/VKEdgePiOverTwoCenteredMissingHarmonicContourAxiomAudit.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes:
  Tasks 2--5 and the existing missing-harmonic filters.
- Produces:
  `CenteredLocalizedContourData`,
  `sharpenedCenteredLocalizedContourData`,
  and a normalized-error witness in every late
  `localizedGaussianLogWindow q d m`.

- [ ] **Step 1: Write the failing data contract**

Define a structure whose `eventually_window_bddAbove` and
`eventually_upper_bound` fields use
`localizedGaussianLogWindow q d m`, not the old center-16 window.

- [ ] **Step 2: Generalize the paired coefficient**

Replace every shift `16*m-y` by `q*m-y`. Use uniform-in-center periodic
Gaussian convergence to prove the coefficient still tends to
`2 * sharpenedMissingHarmonicDenominator k`.

- [ ] **Step 3: Install target and missing-harmonic contours**

Pair the two selected true-zeta contour identities before taking absolute
values. Preserve analytic multiplicity, use
`localizedNearZeroFilter center (centeredPoleRadius q)` for both centers,
and use Task 5 for both true-psi tails.

- [ ] **Step 4: Prove the abstract window witness**

Prove:

```lean
∀ᶠ m : ℝ in atTop,
  ∃ y ∈ localizedGaussianLogWindow q d m,
    C < |normalizedPsiError rho y|
```

whenever
`C < multiplicity / sharpenedMissingHarmonicDenominator k`.

- [ ] **Step 5: Verify and commit**

Run focused checks and commit:

```bash
git commit -m "feat: assemble centered missing-harmonic contour"
```

### Task 7: Epsilon-window Main Theorems and Carlson Selection

**Files:**
- Create: `PrimeNumberTheorem/VKEdgePiOverTwoEpsilonOscillation.lean`
- Create: `Test/VKEdgePiOverTwoEpsilonOscillationContract.lean`
- Create: `Test/VKEdgePiOverTwoEpsilonOscillationAxiomAudit.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes:
  Task 1 epsilon specialization, Task 6 centered contour data, and
  `exists_missing_oddHarmonic_with_strict_gap_of_carlson`.
- Produces:
  `eventually_exists_psiError_in_powerOnePlusEpsilonWindow_gt_strictPiOverTwo`
  and
  `exists_eventually_psiError_in_powerOnePlusEpsilonWindow_gt_strictPiOverTwo`.

- [ ] **Step 1: Write the failing final contract**

Pin the fixed-missing-harmonic theorem exactly as specified in the design.
Pin the Carlson-selected theorem with assumptions:

```lean
hε : 0 < ε
hgamma : 0 < rho.im
hzero : riemannZeta rho = 0
hσ : 1 / 2 < σ
hσrho : σ < rho.re
hrhoRe1 : rho.re < 1
```

- [ ] **Step 2: Verify epsilon parameters satisfy analytic hypotheses**

Prove `qε > 0`, `dε > 0`, `dε < qε`, and
`16*(qε+dε) ≤ dε^2`. Show
`epsilonGaussianScale ε Y → ∞`.

- [ ] **Step 3: Compose the fixed-harmonic theorem**

Apply Task 6 at `(qε,dε)`, pull the eventual statement back along
`epsilonGaussianScale ε`, use Task 1's exact window identity, and transfer
to standard `chebyshevPsi`.

- [ ] **Step 4: Compose Carlson selection**

Use the existing Carlson theorem to choose `k` and the missing odd-harmonic
center. Do not alter the strict constant or multiplicity factor.

- [ ] **Step 5: Run focused verification**

Run:

```bash
lake build PrimeNumberTheorem.VKEdgePiOverTwoEpsilonOscillation
lake env lean Test/VKEdgePiOverTwoEpsilonOscillationContract.lean
lake env lean Test/VKEdgePiOverTwoEpsilonOscillationAxiomAudit.lean
```

Scan all seven new source modules for forbidden placeholders.

- [ ] **Step 6: Run full branch verification and commit**

Run:

```bash
./scripts/verify-baseline.sh
lake build
```

Commit:

```bash
git commit -m "feat: localize strict pi-over-two oscillation to epsilon windows"
```
