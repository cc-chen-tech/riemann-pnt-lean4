# VK-edge Pi-over-two Localization Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalize the power-interval localization argument behind the candidate theorem that every sufficiently late `[Y, Y^7]` contains a PNT-error oscillation strictly larger than `pi / 2`.

**Architecture:** Keep the existing global Abel theorem and draft PR unchanged. Build a stacked localization branch with four independent layers: the final logarithmic change of variables, Gaussian averaging, finite-pole annihilation, and a conditional contour assembly. Bellotti enters only through a final bounded-count specialization; no external theorem is introduced as a project axiom.

**Tech Stack:** Lean 4.29.1, Mathlib, the existing `VKEdgePiOverTwoAbel*` modules, focused contract files, and `#print axioms` audits.

## Global Constraints

- Work only on `research/vk-edge-pi-over-two-localized`.
- Do not modify PR #15 or `research/vk-edge-pi-over-two`.
- Do not introduce `sorry`, `admit`, or project-defined `axiom`.
- Do not encode Bellotti or Revesz as an unproved theorem.
- Keep the unconditional Carlson missing-harmonic theorem separate from the Bellotti-uniform specialization.
- Do not claim historical novelty or a completed localized zeta theorem before the analytic transfer and prior-art gates close.

---

### Task 1: Logarithmic Window and Psi Transfer

**Files:**
- Create: `PrimeNumberTheorem/VKEdgePiOverTwoLocalized.lean`
- Create: `Test/VKEdgePiOverTwoLocalizedContract.lean`
- Create: `Test/VKEdgePiOverTwoLocalizedAxiomAudit.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes: `normalizedPsiError` from `PrimeNumberTheorem.VKEdgePiOverTwoAbelPhase`.
- Produces: `gaussianLogWindow_log_div_four` and `exists_psiError_in_powerSevenWindow_of_normalizedPsiError`.

- [x] **Step 1: Add a failing contract for the logarithmic and power windows**

Run:

```bash
lake env lean Test/VKEdgePiOverTwoLocalizedContract.lean
```

Expected before implementation: failure because `PrimeNumberTheorem.VKEdgePiOverTwoLocalized` does not exist.

- [x] **Step 2: Implement the window definitions and exact endpoint identity**

Define:

```lean
def gaussianLogWindow (m : ℝ) : Set ℝ := Set.Icc (4 * m) (28 * m)
def logarithmicPowerSevenWindow (Y : ℝ) : Set ℝ :=
  Set.Icc (Real.log Y) (7 * Real.log Y)
def powerSevenWindow (Y : ℝ) : Set ℝ := Set.Icc Y (Y ^ (7 : ℕ))
```

Prove:

```lean
theorem gaussianLogWindow_log_div_four (Y : ℝ) :
    gaussianLogWindow (Real.log Y / 4) =
      logarithmicPowerSevenWindow Y
```

- [x] **Step 3: Implement the normalized-error transfer**

For `rho != 0` and `Y >= 1`, map a witness in the logarithmic window through `x = exp y`. Prove both interval endpoints and cancel `exp (-rho.re * y)` without assuming continuity of `chebyshevPsi`.

- [x] **Step 4: Run the focused contract and axiom audit**

Run:

```bash
lake env lean Test/VKEdgePiOverTwoLocalizedContract.lean
lake env lean Test/VKEdgePiOverTwoLocalizedAxiomAudit.lean
```

Expected: both commands exit `0`; the audit lists only standard Lean/Mathlib logical axioms.

- [x] **Step 5: Commit the independently reviewable transfer layer**

```bash
git add PrimeNumberTheorem/VKEdgePiOverTwoLocalized.lean \
  Test/VKEdgePiOverTwoLocalizedContract.lean \
  Test/VKEdgePiOverTwoLocalizedAxiomAudit.lean \
  docs/superpowers/plans/2026-07-25-vk-edge-pi-over-two-localized.md
git commit -m "feat: localize VK-edge oscillation window"
```

### Task 2: Gaussian Periodic Averaging

**Files:**
- Create: `PrimeNumberTheorem/VKEdgePiOverTwoGaussianMean.lean`
- Create: `Test/VKEdgePiOverTwoGaussianMeanContract.lean`
- Create: `Test/VKEdgePiOverTwoGaussianMeanAxiomAudit.lean`

**Interfaces:**
- Consumes: Mathlib's Gaussian integral and whole-line integration-by-parts API.
- Produces: a normalized Gaussian of mass one, an `L1` derivative bound tending to zero, and uniform convergence of Gaussian averages of continuous periodic functions to their period mean.

- [x] **Step 1: Pin the normalized Gaussian API in a failing contract**

The contract must check positivity, mass one, the derivative formula, and the periodic-mean limit.

- [x] **Step 2: Prove normalization and differentiability**

Use `Real.integral_gaussian`, `integrable_exp_neg_mul_sq`, and direct differentiation. Keep all statements under `0 < m`.

- [x] **Step 3: Bound the derivative in `L1`**

Use `Real.integrable_mul_exp_neg_mul_sq` and the half-line primitive identity to prove an explicit bound of order `m^(-1/2)`.

- [x] **Step 4: Prove periodic mean convergence**

Subtract the period mean, construct the bounded periodic primitive, and integrate by parts against the Gaussian. The final bound must be uniform in the Gaussian center.

- [x] **Step 5: Run focused verification and commit**

Run both focused files with `lake env lean`, scan the module for forbidden placeholders, and commit the layer independently.

### Task 2a: Exponential Gaussian Tail

**Files:**
- Create: `PrimeNumberTheorem/VKEdgePiOverTwoGaussianTail.lean`
- Create: `Test/VKEdgePiOverTwoGaussianTailContract.lean`
- Create: `Test/VKEdgePiOverTwoGaussianTailAxiomAudit.lean`

- [x] Define the complement of the distance-`12m` Gaussian window.
- [x] Prove the pointwise comparison with the variance-`2m` Gaussian.
- [x] Prove
  `integral (gaussianTail m) (normalizedGaussian m) <= 2 * exp (-18*m)`.
- [x] Run the focused contract, axiom audit, and placeholder scan.

### Task 2b: Gaussian Missing-Harmonic Denominator

**Files:**
- Create: `PrimeNumberTheorem/VKEdgePiOverTwoGaussianDual.lean`
- Create: `Test/VKEdgePiOverTwoGaussianDualContract.lean`
- Create: `Test/VKEdgePiOverTwoGaussianDualAxiomAudit.lean`

- [x] Identify the exact periodic mean with
  `sharpenedMissingHarmonicDenominator`.
- [x] Prove uniform-in-center Gaussian convergence with
  `O(m^(-1/2))` error.
- [x] Run the focused contract, axiom audit, and placeholder scan.

### Task 2c: Polynomial-Weighted Gaussian Stability

**Files:**
- Create: `PrimeNumberTheorem/VKEdgePiOverTwoPolynomialGaussian.lean`
- Create: `Test/VKEdgePiOverTwoPolynomialGaussianContract.lean`
- Create: `Test/VKEdgePiOverTwoPolynomialGaussianAxiomAudit.lean`

- [x] Express every derivative of the standard Gaussian as a Hermite-type
  polynomial times the Gaussian and prove its `L1` integrability.
- [x] Prove the exact scaling law
  `integral |G_m^(k)| = m^(-k/2) * integral |G_1^(k)|`.
- [x] For every fixed complex polynomial `A` with `A(0)=1`, prove
  `||G_(A,m)-G_m||_1 = O_A(m^(-1/2))`.
- [x] For every fixed complex polynomial `A`, prove
  `||G_(A,m)'||_1 = O_A(m^(-1/2))`.
- [x] Run the focused contract, axiom audit, placeholder scan, and branch
  verification.

### Task 3: Finite-Pole Annihilator

**Files:**
- Create: `PrimeNumberTheorem/VKEdgePiOverTwoFinitePoleFilter.lean`
- Create: `Test/VKEdgePiOverTwoFinitePoleFilterContract.lean`
- Create: `Test/VKEdgePiOverTwoFinitePoleFilterAxiomAudit.lean`

**Interfaces:**
- Consumes: finite zero sets, analytic multiplicity, and polynomial evaluation.
- Produces: target-preserving and empty-center polynomials that vanish at every unwanted local pole.

- [x] **Step 1: Define the finite product filters**

Use a `Finset complex` of distinct pole offsets and exclude zero only for the target-preserving filter.

- [x] **Step 2: Prove normalization and vanishing**

Prove `A(0)=1`, target retention, and vanishing at every other listed offset. State explicitly that logarithmic-derivative poles are simple while residues carry analytic multiplicity.

- [x] **Step 3: Prove conjugation compatibility**

Show the conjugated filter is obtained by conjugating both coefficients and arguments.

- [x] **Step 4: Verify and commit**

Run the contract and axiom audit, then commit without adding any contour assumption.

### Task 4: Conditional Localized Analytic Assembly

**Files:**
- Create: `PrimeNumberTheorem/VKEdgePiOverTwoLocalizedAssembly.lean`
- Create: `Test/VKEdgePiOverTwoLocalizedAssemblyContract.lean`
- Create: `Test/VKEdgePiOverTwoLocalizedAssemblyAxiomAudit.lean`

**Interfaces:**
- Consumes: the Gaussian mean layer, finite-pole filter, missing-harmonic certificate, and explicit hypotheses expressing the simultaneous zero-avoiding contour estimates.
- Produces: a conditional theorem locating a strict `> pi / 2` normalized oscillation in every late logarithmic window.

- [x] **Step 1: Define the smallest honest contour-data structure**

Every field must be a quantitative estimate used in equations (15)--(32) of `docs/research/vk-edge-pi-over-two-localized-transfer.md`. Do not include the desired conclusion as a field.

- [x] **Step 2: Prove the residue-to-window lower bound**

Combine target residues, annihilated local poles, exponentially decaying far poles, contour decay, Gaussian averaging, and the strict missing-harmonic denominator.

- [x] **Step 3: Compose with Task 1**

Derive the standard `chebyshevPsi` witness in `[Y,Y^7]`. The starting threshold may depend on the fixed zero and filter data.

- [x] **Step 4: Audit the interface**

Confirm that the theorem is mathematically conditional and that no field merely restates the output. Run focused contracts and `#print axioms`.

### Task 5: Carlson and Bellotti Specializations

**Files:**
- Create: `PrimeNumberTheorem/VKEdgePiOverTwoLocalizedCarlson.lean`
- Create: `Test/VKEdgePiOverTwoLocalizedCarlsonContract.lean`
- Update: `docs/research/vk-edge-pi-over-two-localized-transfer.md`

**Interfaces:**
- Consumes: `exists_missing_oddHarmonic_with_strict_gap_of_carlson` and the conditional localized assembly.
- Produces: an unconditional fixed-zero theorem once the Revesz contour estimates are proved internally; separately, a bounded-count theorem parameterized by `M_A`.

- [ ] **Step 1: Connect Carlson to the localized assembly**

Keep the strict gap zero-dependent and preserve the fixed interval exponent `7`.

- [ ] **Step 2: State the bounded-count specialization without importing Bellotti as an axiom**

Assume the exact multiplicity-counted inequality needed to force one of the first `M_A+1` odd harmonics to be absent. Derive the explicit constant `finiteOddHarmonicLowerBound M_A`.

- [ ] **Step 3: Record the remaining external instantiation**

Document the precise translation still needed from Bellotti's zero-count convention to the Lean multiplicity-counted predicate.

- [ ] **Step 4: Run branch verification**

Run all focused contracts and audits, `./scripts/verify-baseline.sh`, and `lake build` only after all new modules are registered as build roots.
