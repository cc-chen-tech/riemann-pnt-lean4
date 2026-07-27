# VK-edge Annihilator Step-Average Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove that averaging the target-pair annihilator over its step separates every fixed non-target frequency, lift this to finite collected frequency packages, and record the exact zeta-facing dichotomy without claiming that one off-line zero forces a companion zero.

**Architecture:** A new module extends the parent three-point annihilator with a scalar frequency multiplier and exact interval integral. The existing finite exponential-polynomial diagonal/off-diagonal theorem supplies the long-window energy estimate, while the new step average removes fixed-step collisions. Zeta-facing endpoints remain conditional on an explicit same-edge finite package or a real-part-gap remainder bound.

**Tech Stack:** Lean 4, Mathlib interval integrals and filters, `PrimeNumberTheorem.ZeroForcedOscillation`, the parent `VKEdgeTargetPairAnnihilator` API, focused contract modules, and `#print axioms` audits.

## Global Constraints

- Work only in `/Users/luicy/AI/Riemann/riemann-pnt-lean4/.worktrees/vk-edge-annihilator-h-average` on `research/vk-edge-annihilator-h-average`.
- Do not modify `PrimeNumberTheorem/VKEdgeTargetPairAnnihilator.lean`, `PrimeNumberTheorem/VKEdgeResidualAmplification.lean`, Carlson density iteration, zero-layer deduplication, or Vinogradov--Korobov public cores.
- Add no `sorry`, `admit`, project `axiom`, or theorem-shaped `Prop` placeholder.
- Repeated frequencies must be collected before applying finite-package endpoints.
- The public conclusion is a same-edge/near-edge dichotomy, not “one off-line zero forces another equally far-right zero”.
- Only `propext`, `Classical.choice`, and `Quot.sound` may occur in public axiom audits.

---

## File Map

- Create `PrimeNumberTheorem/VKEdgeTargetPairAnnihilatorAverage.lean`: multiplier calculus, finite-frequency simultaneous separation, finite-package energy, and conditional zeta endpoints.
- Create `Test/VKEdgeTargetPairAnnihilatorAverageContract.lean`: compile-time public API contract.
- Create `Test/VKEdgeTargetPairAnnihilatorAverageAxiomAudit.lean`: public `#print axioms` audit.
- Create `docs/research/vk-edge-target-pair-annihilator-average-audit.md`: theorem inventory, hypotheses, and no-go boundary.
- Modify `lakefile.lean`: register the focused contract and audit executables.

### Task 1: Exact Step-Multiplier Calculus

**Files:**
- Create: `PrimeNumberTheorem/VKEdgeTargetPairAnnihilatorAverage.lean`
- Create: `Test/VKEdgeTargetPairAnnihilatorAverageContract.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes:

```lean
symmetricFrequencyAnnihilator_cosineZeroPair
    (h gamma m lambda phase y : ℝ) :
    symmetricFrequencyAnnihilator h gamma
        (cosineZeroPair m lambda phase) y =
      2 * (Real.cos (lambda * h) - Real.cos (gamma * h)) *
        cosineZeroPair m lambda phase y
```

- Produces:

```lean
def frequencyAnnihilatorMultiplier
    (gamma lambda h : ℝ) : ℝ :=
  2 * (Real.cos (lambda * h) - Real.cos (gamma * h))

theorem frequencyAnnihilatorMultiplier_target
    (gamma h : ℝ) :
    frequencyAnnihilatorMultiplier gamma gamma h = 0

theorem intervalIntegral_frequencyAnnihilatorMultiplier_sq
    {gamma lambda H : ℝ}
    (hgamma : gamma ≠ 0) (hlambda : lambda ≠ 0)
    (hne : lambda ≠ gamma) (hneg : lambda ≠ -gamma) :
    (∫ h in (0 : ℝ)..H,
        frequencyAnnihilatorMultiplier gamma lambda h ^ 2) =
      4 * H +
        Real.sin (2 * lambda * H) / lambda +
        Real.sin (2 * gamma * H) / gamma -
        4 * Real.sin ((lambda - gamma) * H) / (lambda - gamma) -
        4 * Real.sin ((lambda + gamma) * H) / (lambda + gamma)
```

- [ ] **Step 1: Write the failing contract**

```lean
import PrimeNumberTheorem.VKEdgeTargetPairAnnihilatorAverage

open scoped Interval
open PrimeNumberTheorem.VKEdgePiOverTwo

#check frequencyAnnihilatorMultiplier
#check frequencyAnnihilatorMultiplier_target
#check intervalIntegral_frequencyAnnihilatorMultiplier_sq

example (gamma h : ℝ) :
    frequencyAnnihilatorMultiplier gamma gamma h = 0 :=
  frequencyAnnihilatorMultiplier_target gamma h
```

- [ ] **Step 2: Run the contract and verify the missing-module failure**

Run:

```bash
lake env lean Test/VKEdgeTargetPairAnnihilatorAverageContract.lean
```

Expected: failure because `PrimeNumberTheorem.VKEdgeTargetPairAnnihilatorAverage` does not exist.

- [ ] **Step 3: Add the module import and multiplier definition**

```lean
import PrimeNumberTheorem.VKEdgeTargetPairAnnihilator
import PrimeNumberTheorem.ZeroForcedOscillation

open Complex Filter MeasureTheory Set Topology
open scoped Interval

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

def frequencyAnnihilatorMultiplier
    (gamma lambda h : ℝ) : ℝ :=
  2 * (Real.cos (lambda * h) - Real.cos (gamma * h))
```

- [ ] **Step 4: Prove the target identity and exact integral**

Use `Real.cos_sq`, `Real.cos_mul_cos`, and antiderivatives of
`cos (c * h)`. The exact algebraic expansion must be:

```lean
4 * H +
  Real.sin (2 * lambda * H) / lambda +
  Real.sin (2 * gamma * H) / gamma -
  4 * Real.sin ((lambda - gamma) * H) / (lambda - gamma) -
  4 * Real.sin ((lambda + gamma) * H) / (lambda + gamma)
```

The proof must use all four nonzero denominator hypotheses explicitly.

- [ ] **Step 5: Run the focused contract**

Run:

```bash
lake env lean Test/VKEdgeTargetPairAnnihilatorAverageContract.lean
```

Expected: pass.

- [ ] **Step 6: Commit the exact calculus**

```bash
git add PrimeNumberTheorem/VKEdgeTargetPairAnnihilatorAverage.lean \
  Test/VKEdgeTargetPairAnnihilatorAverageContract.lean lakefile.lean
git commit -m "feat: add annihilator step multiplier calculus"
```

### Task 2: Mean Limit and Eventual Separation

**Files:**
- Modify: `PrimeNumberTheorem/VKEdgeTargetPairAnnihilatorAverage.lean`
- Modify: `Test/VKEdgeTargetPairAnnihilatorAverageContract.lean`

**Interfaces:**
- Consumes:

```lean
intervalIntegral_frequencyAnnihilatorMultiplier_sq
```

- Produces:

```lean
def normalizedStepMultiplierEnergy
    (gamma lambda H : ℝ) : ℝ :=
  H⁻¹ * ∫ h in (0 : ℝ)..H,
    frequencyAnnihilatorMultiplier gamma lambda h ^ 2

theorem tendsto_normalizedStepMultiplierEnergy
    {gamma lambda : ℝ}
    (hgamma : 0 < gamma) (hlambda : 0 < lambda)
    (hne : lambda ≠ gamma) :
    Tendsto (normalizedStepMultiplierEnergy gamma lambda)
      atTop (𝓝 4)

theorem eventually_two_le_normalizedStepMultiplierEnergy
    {gamma lambda : ℝ}
    (hgamma : 0 < gamma) (hlambda : 0 < lambda)
    (hne : lambda ≠ gamma) :
    ∀ᶠ H in atTop,
      2 ≤ normalizedStepMultiplierEnergy gamma lambda H
```

- [ ] **Step 1: Extend the contract before implementation**

```lean
#check normalizedStepMultiplierEnergy
#check tendsto_normalizedStepMultiplierEnergy
#check eventually_two_le_normalizedStepMultiplierEnergy
```

- [ ] **Step 2: Run the contract and verify missing declarations**

Run:

```bash
lake env lean Test/VKEdgeTargetPairAnnihilatorAverageContract.lean
```

Expected: failure naming `normalizedStepMultiplierEnergy`.

- [ ] **Step 3: Prove bounded oscillatory terms divided by `H` vanish**

For every fixed nonzero `c`, prove the local helper:

```lean
private theorem tendsto_sin_mul_div_atTop
    {c d : ℝ} :
    Tendsto (fun H => Real.sin (c * H) / (d * H))
      atTop (𝓝 0)
```

when `d ≠ 0`, using `|sin| ≤ 1`, `tendsto_const_nhds.div_atTop`, and squeeze.

- [ ] **Step 4: Rewrite the exact formula and prove the limit**

Normalize the Task 1 identity by `H`, split the five terms, prove the main
term is exactly `4`, and discharge the four oscillatory limits with the helper.

- [ ] **Step 5: Derive the eventual lower bound from the open neighborhood**

Use:

```lean
have hnhds : Set.Ioi (2 : ℝ) ∈ 𝓝 4 := Ioi_mem_nhds (by norm_num)
exact (tendsto_normalizedStepMultiplierEnergy
  hgamma hlambda hne).eventually hnhds
```

- [ ] **Step 6: Run the focused contract and commit**

```bash
lake env lean Test/VKEdgeTargetPairAnnihilatorAverageContract.lean
git add PrimeNumberTheorem/VKEdgeTargetPairAnnihilatorAverage.lean \
  Test/VKEdgeTargetPairAnnihilatorAverageContract.lean
git commit -m "feat: prove averaged frequency separation"
```

### Task 3: Simultaneous Separation of a Finite Collected Spectrum

**Files:**
- Modify: `PrimeNumberTheorem/VKEdgeTargetPairAnnihilatorAverage.lean`
- Modify: `Test/VKEdgeTargetPairAnnihilatorAverageContract.lean`

**Interfaces:**
- Consumes:

```lean
eventually_two_le_normalizedStepMultiplierEnergy
```

- Produces:

```lean
theorem eventually_two_le_normalizedStepMultiplierEnergy_finset
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (omega : ι → ℝ) {gamma : ℝ}
    (hgamma : 0 < gamma)
    (homega : ∀ i ∈ S, 0 < omega i)
    (hne : ∀ i ∈ S, omega i ≠ gamma) :
    ∀ᶠ H in atTop, ∀ i ∈ S,
      2 ≤ normalizedStepMultiplierEnergy gamma (omega i) H
```

- [ ] **Step 1: Add a failing finite-family contract**

```lean
#check eventually_two_le_normalizedStepMultiplierEnergy_finset

example {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (omega : ι → ℝ) {gamma : ℝ}
    (hgamma : 0 < gamma)
    (homega : ∀ i ∈ S, 0 < omega i)
    (hne : ∀ i ∈ S, omega i ≠ gamma) :
    ∀ᶠ H in atTop, ∀ i ∈ S,
      2 ≤ normalizedStepMultiplierEnergy gamma (omega i) H :=
  eventually_two_le_normalizedStepMultiplierEnergy_finset
    S omega hgamma homega hne
```

- [ ] **Step 2: Run the contract and verify the missing declaration**

Run:

```bash
lake env lean Test/VKEdgeTargetPairAnnihilatorAverageContract.lean
```

Expected: failure naming the finite-family theorem.

- [ ] **Step 3: Prove the finite intersection**

Use `Finset.eventually_all` or induction on `S`. For each `i ∈ S`, instantiate
Task 2 with `homega i hi` and `hne i hi`; do not introduce a numerical minimum
frequency gap.

- [ ] **Step 4: Run the focused contract and commit**

```bash
lake env lean Test/VKEdgeTargetPairAnnihilatorAverageContract.lean
git add PrimeNumberTheorem/VKEdgeTargetPairAnnihilatorAverage.lean \
  Test/VKEdgeTargetPairAnnihilatorAverageContract.lean
git commit -m "feat: separate finite frequency families by step average"
```

### Task 4: Finite-Package Diagonal Energy

**Files:**
- Modify: `PrimeNumberTheorem/VKEdgeTargetPairAnnihilatorAverage.lean`
- Modify: `Test/VKEdgeTargetPairAnnihilatorAverageContract.lean`

**Interfaces:**
- Consumes:

```lean
PrimeNumberTheorem.ZeroForcedOscillation.exponentialPolynomial
PrimeNumberTheorem.ZeroForcedOscillation.offDiagonalBound
PrimeNumberTheorem.ZeroForcedOscillation.abs_intervalIntegral_sqNorm_exponentialPolynomial_sub_diagonal_le
eventually_two_le_normalizedStepMultiplierEnergy_finset
```

- Produces:

```lean
def annihilatedExponentialPolynomial
    {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (omega : ι → ℝ) (gamma h y : ℝ) : ℂ :=
  PrimeNumberTheorem.ZeroForcedOscillation.exponentialPolynomial S
    (fun i => frequencyAnnihilatorMultiplier gamma (omega i) h * c i)
    omega y

def stepAveragedDiagonalEnergy
    {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (omega : ι → ℝ) (gamma H : ℝ) : ℝ :=
  ∑ i ∈ S, ‖c i‖ ^ 2 *
    normalizedStepMultiplierEnergy gamma (omega i) H

theorem eventually_two_mul_coefficientEnergy_le_stepAveragedDiagonalEnergy
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (c : ι → ℂ) (omega : ι → ℝ)
    {gamma : ℝ}
    (hgamma : 0 < gamma)
    (homega : ∀ i ∈ S, 0 < omega i)
    (hne : ∀ i ∈ S, omega i ≠ gamma) :
    ∀ᶠ H in atTop,
      2 * (∑ i ∈ S, ‖c i‖ ^ 2) ≤
        stepAveragedDiagonalEnergy S c omega gamma H
```

- [ ] **Step 1: Add failing package declarations to the contract**

```lean
#check annihilatedExponentialPolynomial
#check stepAveragedDiagonalEnergy
#check eventually_two_mul_coefficientEnergy_le_stepAveragedDiagonalEnergy
```

- [ ] **Step 2: Run the contract and verify failure**

Run:

```bash
lake env lean Test/VKEdgeTargetPairAnnihilatorAverageContract.lean
```

Expected: failure naming `annihilatedExponentialPolynomial`.

- [ ] **Step 3: Define the transformed package and diagonal energy**

The coefficient multiplier is coerced from `ℝ` to `ℂ`. Keep the real
multiplier separate so `norm_real` reduces its norm to an absolute value.

- [ ] **Step 4: Prove the diagonal lower bound**

Filter on Task 3's simultaneous lower bound. For each `i ∈ S`, multiply by
`‖c i‖² ≥ 0`, sum over `S`, and normalize with `Finset.mul_sum`.

- [ ] **Step 5: Expose the existing off-diagonal comparison**

Prove:

```lean
theorem abs_intervalIntegral_annihilatedExponentialPolynomial_sub_diagonal_le
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (c : ι → ℂ) (omega : ι → ℝ)
    {gamma h a b : ℝ}
    (homegaInj : Set.InjOn omega ↑S) :
    |(∫ y in a..b,
        ‖annihilatedExponentialPolynomial S c omega gamma h y‖ ^ 2) -
      (b - a) *
        ∑ i ∈ S,
          ‖(frequencyAnnihilatorMultiplier gamma (omega i) h : ℂ) *
            c i‖ ^ 2| ≤
      PrimeNumberTheorem.ZeroForcedOscillation.offDiagonalBound S
        (fun i =>
          (frequencyAnnihilatorMultiplier gamma (omega i) h : ℂ) * c i)
        omega
```

This must be a direct specialization of the existing generic theorem.

- [ ] **Step 6: Run the focused contract and commit**

```bash
lake env lean Test/VKEdgeTargetPairAnnihilatorAverageContract.lean
git add PrimeNumberTheorem/VKEdgeTargetPairAnnihilatorAverage.lean \
  Test/VKEdgeTargetPairAnnihilatorAverageContract.lean
git commit -m "feat: lift step separation to finite frequency packages"
```

### Task 5: Honest Zeta-Facing Conditional Endpoints

**Files:**
- Modify: `PrimeNumberTheorem/VKEdgeTargetPairAnnihilatorAverage.lean`
- Modify: `Test/VKEdgeTargetPairAnnihilatorAverageContract.lean`
- Create: `docs/research/vk-edge-target-pair-annihilator-average-audit.md`

**Interfaces:**
- Consumes:

```lean
annihilatedNormalizedPsiError_eq_residual
eventually_two_mul_coefficientEnergy_le_stepAveragedDiagonalEnergy
```

- Produces:

```lean
structure SameEdgeResidualPackage (rho : ℂ) where
  ι : Type
  instFintype : Fintype ι
  instDecidableEq : DecidableEq ι
  support : Finset ι
  coefficient : ι → ℂ
  frequency : ι → ℝ
  frequency_pos : ∀ i ∈ support, 0 < frequency i
  frequency_injective : Set.InjOn frequency ↑support
  avoids_target : ∀ i ∈ support, frequency i ≠ rho.im
  coefficientEnergy_pos : 0 < ∑ i ∈ support, ‖coefficient i‖ ^ 2

theorem sameEdgeResidualPackage_eventually_stepEnergy_pos
    {rho : ℂ} (hrhoIm : 0 < rho.im)
    (P : SameEdgeResidualPackage rho) :
    ∀ᶠ H in atTop,
      0 < stepAveragedDiagonalEnergy
        P.support P.coefficient P.frequency rho.im H

theorem no_sameEdge_conclusion_from_target_pair_alone
    {rho : ℂ} {h C a b : ℝ}
    (hC : 0 < C) (hab : a < b) :
    ¬ C * (b - a) ≤
      ∫ y in Set.Icc a b,
        symmetricFrequencyAnnihilator h rho.im
          (normalizedTargetZeroPair rho) y ^ 2
```

- [ ] **Step 1: Add the structure and endpoint signatures to the contract**

```lean
#check SameEdgeResidualPackage
#check sameEdgeResidualPackage_eventually_stepEnergy_pos
#check no_sameEdge_conclusion_from_target_pair_alone
```

- [ ] **Step 2: Run the contract and verify missing declarations**

Run:

```bash
lake env lean Test/VKEdgeTargetPairAnnihilatorAverageContract.lean
```

Expected: failure naming `SameEdgeResidualPackage`.

- [ ] **Step 3: Implement the finite-package positive endpoint**

Supply local instances with:

```lean
letI : Fintype P.ι := P.instFintype
letI : DecidableEq P.ι := P.instDecidableEq
```

Apply Task 4 and use `P.coefficientEnergy_pos` to turn the lower bound
`2 * coefficientEnergy` into strict positivity.

- [ ] **Step 4: Prove the target-only no-go by exact annihilation**

Unfold `normalizedTargetZeroPair`, use
`symmetricFrequencyAnnihilator_targetPair_eq_zero`, reduce the integral to
zero, then contradict `C * (b-a) > 0`.

- [ ] **Step 5: Write the audit boundary**

The audit must state:

```text
Proved: every fixed non-target positive frequency is separated after averaging h.
Proved: a finite collected non-target package has positive averaged diagonal energy.
Conditional: applying this to zeta requires an independently identified same-edge package
             and a uniform explicit-formula tail comparison.
Not proved: one off-line zero forces another zero with the same real part.
Not proved: a Carlson contradiction or RH.
```

- [ ] **Step 6: Run contract and commit**

```bash
lake env lean Test/VKEdgeTargetPairAnnihilatorAverageContract.lean
git add PrimeNumberTheorem/VKEdgeTargetPairAnnihilatorAverage.lean \
  Test/VKEdgeTargetPairAnnihilatorAverageContract.lean \
  docs/research/vk-edge-target-pair-annihilator-average-audit.md
git commit -m "research: state annihilator step-average dichotomy"
```

### Task 6: Axiom Audit and Full Verification

**Files:**
- Create: `Test/VKEdgeTargetPairAnnihilatorAverageAxiomAudit.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes: all public Task 1--5 declarations.
- Produces: focused executable audit and a clean Draft PR.

- [ ] **Step 1: Add the axiom audit**

```lean
import PrimeNumberTheorem.VKEdgeTargetPairAnnihilatorAverage

open PrimeNumberTheorem.VKEdgePiOverTwo

#print axioms frequencyAnnihilatorMultiplier_target
#print axioms intervalIntegral_frequencyAnnihilatorMultiplier_sq
#print axioms tendsto_normalizedStepMultiplierEnergy
#print axioms eventually_two_le_normalizedStepMultiplierEnergy
#print axioms eventually_two_le_normalizedStepMultiplierEnergy_finset
#print axioms eventually_two_mul_coefficientEnergy_le_stepAveragedDiagonalEnergy
#print axioms abs_intervalIntegral_annihilatedExponentialPolynomial_sub_diagonal_le
#print axioms sameEdgeResidualPackage_eventually_stepEnergy_pos
#print axioms no_sameEdge_conclusion_from_target_pair_alone
```

- [ ] **Step 2: Register focused executables in `lakefile.lean`**

```lean
lean_exe vkEdgeTargetPairAnnihilatorAverageContract where
  root := `Test.VKEdgeTargetPairAnnihilatorAverageContract

lean_exe vkEdgeTargetPairAnnihilatorAverageAxiomAudit where
  root := `Test.VKEdgeTargetPairAnnihilatorAverageAxiomAudit
```

- [ ] **Step 3: Run focused builds**

```bash
lake -Kjobs=1 build \
  vkEdgeTargetPairAnnihilatorAverageContract \
  vkEdgeTargetPairAnnihilatorAverageAxiomAudit
```

Expected: pass; printed axioms are subsets of
`[propext, Classical.choice, Quot.sound]`.

- [ ] **Step 4: Scan prohibited constructs and formatting**

```bash
rg -n "\\bsorry\\b|\\badmit\\b|^[[:space:]]*axiom\\b" \
  PrimeNumberTheorem/VKEdgeTargetPairAnnihilatorAverage.lean \
  Test/VKEdgeTargetPairAnnihilatorAverageContract.lean \
  Test/VKEdgeTargetPairAnnihilatorAverageAxiomAudit.lean
git diff --check
```

Expected: no prohibited source matches and no whitespace errors.

- [ ] **Step 5: Run repository verification**

```bash
./scripts/verify-baseline.sh
lake -Kjobs=1 build
```

Expected: both pass.

- [ ] **Step 6: Commit verification files**

```bash
git add Test/VKEdgeTargetPairAnnihilatorAverageAxiomAudit.lean lakefile.lean
git commit -m "test: audit annihilator step-average endpoints"
```

- [ ] **Step 7: Push and create a Draft PR**

```bash
git push -u origin research/vk-edge-annihilator-h-average
gh pr create --draft \
  --base research/vk-edge-target-annihilator \
  --head research/vk-edge-annihilator-h-average \
  --title "research: average target annihilator over its step" \
  --body-file /tmp/vk-edge-annihilator-h-average-pr.md
```

The PR body must distinguish the abstract spectral theorem, the conditional
same-edge package endpoint, and the unproved Carlson/RH bridge.
