# Actual Cubic Two-Height L2 Tail Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove an actual-zeta cubic high-to-low two-height L2 tail certificate with explicit Carlson exponents, `log^5` loss, finite-set deletion, and a contour estimate that retains the third-order kernel.

**Architecture:** The implementation stays at the second-Riesz/cubic explicit-formula level.  One module converts the existing reciprocal-square dyadic capacity into cubic coefficient-square capacity and aggregates it between `Y=x^gammaLow` and `H=x^alpha`; a second module estimates the actual cubic contour before de-smoothing and assembles target-scale negligibility.  The final certificate exposes the coefficient capacity to half-isolated without proving Gram/Schur or Occupancy.

**Tech Stack:** Lean 4, Mathlib complex analysis and asymptotics, existing zeta explicit-formula modules, Carlson zero density, analytic multiplicity, third-order Perron kernel.

## Global Constraints

- Work only in `research/pintz-carlson-actual-cubic-two-height-l2-tail` and its dedicated worktree.
- Do not modify Sharp, half-isolated, Gram/Schur, Occupancy, Gate B set-growth, or VK-edge modules.
- Keep `H=x^alpha`, `Y=x^gammaLow`, and the Carlson split `x^gammaHigh` distinct.
- Keep the exact target ordinate `R=norm rho0`; do not replace it by `H`.
- Do not use de-smoothed contour bounds to claim cubic decay.
- Every actual-zeta theorem must have a contract and axiom audit.
- The permitted axiom list is `propext`, `Classical.choice`, and `Quot.sound` only.
- The PR must contain no `sorry`, `admit`, or project `axiom` declaration.

---

### Task 1: Actual cubic dyadic square capacity

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualCubicTwoHeightL2Tail.lean`
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualCubicTwoHeightL2TailContract.lean`
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualCubicTwoHeightL2TailAxiomAudit.lean`

**Interfaces:**
- Consumes: `actualCarlsonDyadicZeroStrip`, `actualCarlsonDyadicStripSquareReciprocalCapacityExcluding`, and `exists_actualCarlsonDyadicStripSquareReciprocalCapacityExcluding_le_count`.
- Produces: `actualCubicDyadicStripSquareCapacity`, its finite-set version, and the actual block bound with denominator power six.

- [ ] **Step 1: Add failing contract checks**

```lean
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicTwoHeightL2Tail

open PrimeNumberTheorem

#check actualCubicDyadicStripSquareCapacity
#check actualCubicDyadicStripSquareCapacityExcluding
#check actualCubicDyadicStripSquareCapacityExcluding_le
#check exists_actualCubicDyadicStripSquareCapacityExcluding_le_count
```

- [ ] **Step 2: Compile the contract and confirm the new module is missing**

Run the contract with the isolated overlay.  The expected failure is an unknown import for `ZeroDensityLayerBudgetActualCubicTwoHeightL2Tail`.

- [ ] **Step 3: Define the actual capacities**

```lean
noncomputable def actualCubicDyadicStripSquareCapacity
    (x sigma tau : ℝ) (n : ℕ) : ℝ :=
  ∑ rho ∈ actualCarlsonDyadicZeroStrip sigma tau n,
    (analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 *
      (x ^ (2 * rho.re) / ‖rho‖ ^ 6)

noncomputable def actualCubicDyadicStripSquareCapacityExcluding
    (x sigma tau : ℝ) (n : ℕ) (S : Finset ℂ) : ℝ :=
  ∑ rho ∈ actualCarlsonDyadicZeroStrip sigma tau n \ S,
    (analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 *
      (x ^ (2 * rho.re) / ‖rho‖ ^ 6)
```

- [ ] **Step 4: Prove finite-set monotonicity**

Prove

```lean
theorem actualCubicDyadicStripSquareCapacityExcluding_le
    (hx : 0 ≤ x) :
    actualCubicDyadicStripSquareCapacityExcluding x sigma tau n S ≤
      actualCubicDyadicStripSquareCapacity x sigma tau n
```

using only `Finset.sdiff_subset`, nonnegativity of real powers, and
`Finset.sum_le_sum_of_subset_of_nonneg`.

- [ ] **Step 5: Lift the reciprocal-square capacity to cubic order**

For `1 ≤ x` and every zero in the strip, use `rho.re ≤ tau`,
`2^n < rho.im ≤ norm rho`, and

```text
1/norm(rho)^6 <= (1/(2^n)^4) * (1/norm(rho)^2)
```

to prove

```lean
theorem actualCubicDyadicStripSquareCapacityExcluding_le_reciprocal
    (hx : 1 ≤ x) :
    actualCubicDyadicStripSquareCapacityExcluding x sigma tau n S ≤
      x ^ (2 * tau) / (2 : ℝ) ^ (4 * n) *
        actualCarlsonDyadicStripSquareReciprocalCapacityExcluding sigma tau n S
```

- [ ] **Step 6: Compose with the actual multiplicity theorem**

Prove

```lean
theorem exists_actualCubicDyadicStripSquareCapacityExcluding_le_count :
  ∃ B : ℝ, 0 ≤ B ∧
    ∀ x sigma tau n, 1 ≤ x → 4 ≤ (2 : ℝ)^n →
    ∀ S : Finset ℂ,
      actualCubicDyadicStripSquareCapacityExcluding x sigma tau n S ≤
        B * x ^ (2 * tau) *
          (1 + Real.log ((2 : ℝ) ^ (n + 1) + 6)) *
          (actualCarlsonDyadicCount sigma (n + 1) / (2 : ℝ) ^ (6 * n))
```

with no density proof specialized to `S`.

- [ ] **Step 7: Add focused axiom prints**

The audit prints axioms for the monotonicity theorem, reciprocal lift, and
actual count bound.

- [ ] **Step 8: Compile source, contract, and audit**

Expected audit output is the standard three axioms only.

- [ ] **Step 9: Commit Task 1**

```bash
git add PrimeNumberTheorem/ZeroDensityLayerBudgetActualCubicTwoHeightL2Tail.lean PrimeNumberTheorem/ZeroDensityLayerBudgetActualCubicTwoHeightL2TailContract.lean PrimeNumberTheorem/ZeroDensityLayerBudgetActualCubicTwoHeightL2TailAxiomAudit.lean
git commit -m "feat: bound actual cubic dyadic square capacity"
```

### Task 2: Explicit polynomial exponent and two-height aggregation

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualCubicTwoHeightL2Tail.lean`
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualCubicTwoHeightL2TailContract.lean`
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualCubicTwoHeightL2TailAxiomAudit.lean`

**Interfaces:**
- Consumes: Task 1 block bound, `CarlsonEventualMajorant`, and `exists_jointTwoHeightTargetAmplitudeParameters`.
- Produces: the `q-6` exponent ledger, strict negativity on both two-height ranges, and finite aggregate capacity.

- [ ] **Step 1: Define the exponent ledger**

```lean
noncomputable def cubicCarlsonL2BlockExponent
    (beta sigma tau gamma : ℝ) : ℝ :=
  2 * (tau - beta) +
    gamma * (carlsonTwoHeightDensityExponent sigma - 6)
```

- [ ] **Step 2: Prove the unconditional cubic density slope**

Add the exact declarations

```lean
theorem pntCarlsonClassicalDensityExponent_sub_six_le_neg_five
    (sigma : ℝ) :
    pntCarlsonClassicalDensityExponent sigma - 6 ≤ -5

theorem pntCarlsonClassicalDensityExponent_half_sub_six_eq_neg_five :
    pntCarlsonClassicalDensityExponent (1 / 2) - 6 = -5
```

- [ ] **Step 3: Prove strict negativity on a polynomial block**

```lean
theorem cubicCarlsonL2BlockExponent_lt_zero
    (htau : tau < beta) (hgamma : 0 < gamma) :
    cubicCarlsonL2BlockExponent beta sigma tau gamma < 0
```

Use `pntCarlsonClassicalDensityExponent_sub_six_le_neg_five`; do not weaken
the result to nonpositivity.

- [ ] **Step 4: Define the finite two-height capacity**

```lean
noncomputable def actualCubicTwoHeightSquareTailCapacity
    (x sigma tau : ℝ) (nLow nSplit nHigh : ℕ) (S : Finset ℂ) : ℝ :=
  (∑ n ∈ Finset.Icc nLow nSplit,
      actualCubicDyadicStripSquareCapacityExcluding x sigma tau n S) +
    ∑ n ∈ Finset.Ioc nSplit nHigh,
      actualCubicDyadicStripSquareCapacityExcluding x sigma tau n S
```

- [ ] **Step 5: Prove the exact low/high partition identity**

Under `nLow ≤ nSplit` and `nSplit ≤ nHigh`, prove that the displayed two sums
equal the one sum over `Finset.Icc nLow nHigh`.  This is the place where
`gammaHigh` is represented; it is not reused as a contour height.

- [ ] **Step 6: Prove the aggregate bound**

Apply the Task 1 theorem termwise to both finite sums.  State the result with
the exact block majorant rather than an unspecified function.

- [ ] **Step 7: Expose the joint parameter package**

Prove an existence theorem returning the seven parameters from
`exists_jointTwoHeightTargetAmplitudeParameters`, all four original strict
inequalities, and

```lean
cubicCarlsonL2BlockExponent beta sigma tau gammaLow < 0
cubicCarlsonL2BlockExponent beta sigma tau gammaHigh < 0
cubicCarlsonL2BlockExponent beta sigma tau alpha < 0
```

- [ ] **Step 8: Compile and commit Task 2**

```bash
git add PrimeNumberTheorem/ZeroDensityLayerBudgetActualCubicTwoHeightL2Tail.lean PrimeNumberTheorem/ZeroDensityLayerBudgetActualCubicTwoHeightL2TailContract.lean PrimeNumberTheorem/ZeroDensityLayerBudgetActualCubicTwoHeightL2TailAxiomAudit.lean
git commit -m "feat: aggregate cubic two-height L2 tails"
```

### Task 3: Direct cubic contour budgets

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualCubicContourBudget.lean`
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualCubicContourBudgetContract.lean`
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualCubicContourBudgetAxiomAudit.lean`

**Interfaces:**
- Consumes: `thirdOrderExplicitFormulaIntegrand_eq_explicitFormulaIntegrand_div_sq`, actual good-height logarithmic-derivative control, the classical zero-free-region theorem, and the zeta functional equation.
- Produces: pointwise cubic horizontal/left bounds and an assembled contour bound without normalized second differences.

- [ ] **Step 1: Define the dynamic contour geometry**

```lean
noncomputable def dynamicCubicRightBoundary (x : ℝ) : ℝ :=
  1 + 1 / Real.log x

noncomputable def dynamicCubicLeftBoundary (k alpha x : ℝ) : ℝ :=
  k / (4 * Real.log (x ^ alpha))
```

Prove eventual positivity, `a(x)<1<c(x)`, and boundedness of `x^a(x)` for
`k>0`, `alpha>0`.

- [ ] **Step 2: Prove the cubic integrand norm identity**

For `x>0` and `s≠0`, prove

```lean
‖thirdOrderExplicitFormulaIntegrand x s‖ =
  ‖logDeriv riemannZeta s‖ * x ^ s.re / ‖s‖ ^ 3
```

directly from the existing factorization.

- [ ] **Step 3: Prove horizontal pointwise and integral bounds**

At the selected common height `T`, combine

```text
norm(logDeriv zeta) <= C*(1+log(H+6))^2,
T <= norm(s),
Re(s) <= c(x)
```

to obtain a horizontal integral majorant with denominator `T^3`.  Keep the
actual edge length `abs(c(x)-a(x))`.

- [ ] **Step 4: Prove reflected zero-freeness of the dynamic left line**

For `T0 ≤ abs t ≤ T`, instantiate

```lean
ZeroFreeRegion.exists_riemannZeta_ne_zero_and_norm_logDeriv_le_log_sq_on_inner_zeroFreeRegion
```

at `1-a(x)-I*t`, then use the functional equation to bound
`logDeriv riemannZeta (a(x)+I*t)`.  The bound must display the two digamma
terms and simplify them to a fixed power of `1+log(H+6)`.

- [ ] **Step 5: Bound the bounded-ordinate part of the left line**

Use the local pole theorem
`tendsto_sub_one_mul_neg_logDeriv_riemannZeta` at the reflected point near
`1`, the corresponding digamma pole control near `0`, and compactness away
from those poles.  Produce one constant `Csmall≥0` and the explicit bound

```text
norm(logDeriv zeta(a(x)+I*t))
  <= Csmall * (1 + 1/a(x) + log(H+6))
```

for `abs t ≤ T0` and sufficiently large `x`.

- [ ] **Step 6: Integrate the left cubic edge**

Split at `[-T0,T0]`.  Use `norm(a+I*t)≥a` on the bounded part and the
integrable `abs(t)^-3` tail on the large part.  State the resulting bound as
a concrete polynomial in `1/a(x)` and `1+log(H+6)` multiplied by `x^a(x)`.

- [ ] **Step 7: Assemble the direct cubic contour**

Prove

```lean
theorem exists_actualCubicContourPolynomialBudget ... :
  ∃ C ≥ 0, ∀ᶠ x in atTop,
    ‖thirdOrderContourRemainder x (a x) (c x) (W x)‖ ≤
      C * x ^ (c x) * (1 + Real.log (H x + 6)) ^ K / (H x)^3 +
      C * x ^ (a x) * (1 + Real.log (H x + 6)) ^ K
```

where `K` is the explicit natural exponent obtained in Steps 3-6, not a
variable or an existential.

- [ ] **Step 8: Compile and commit Task 3**

```bash
git add PrimeNumberTheorem/ZeroDensityLayerBudgetActualCubicContourBudget.lean PrimeNumberTheorem/ZeroDensityLayerBudgetActualCubicContourBudgetContract.lean PrimeNumberTheorem/ZeroDensityLayerBudgetActualCubicContourBudgetAxiomAudit.lean
git commit -m "feat: retain cubic decay on actual contour edges"
```

### Task 4: Target-scale contour and Perron decay

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualCubicContourBudget.lean`
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualCubicContourBudgetContract.lean`
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualCubicContourBudgetAxiomAudit.lean`

**Interfaces:**
- Consumes: Task 3 contour budget and the explicit `W^-2` cubic Perron truncation theorem.
- Produces: target-normalized decay at `x^beta/R^3` with all exponents recorded.

- [ ] **Step 1: Define the exact cubic target amplitude**

```lean
noncomputable def cubicTargetAmplitude
    (beta R x : ℝ) : ℝ := x ^ beta / R ^ 3
```

- [ ] **Step 2: Prove right truncation exponent negativity**

```lean
theorem cubicRightTruncationExponent_lt_zero
    (hcontour : 1 - beta < alpha) :
    1 - beta - 2 * alpha < 0
```

- [ ] **Step 3: Prove horizontal contour exponent negativity**

```lean
theorem cubicHorizontalContourExponent_lt_zero
    (hcontour : 1 - beta < alpha) :
    1 - beta - 3 * alpha < 0
```

- [ ] **Step 4: Prove actual contour negligibility**

For fixed `R>0`, combine Task 3 with power-beats-log lemmas to prove

```lean
theorem exists_actualCubicContourTargetNegligible ... :
  Tendsto
    (fun x => ‖thirdOrderContourRemainder ...‖ /
      cubicTargetAmplitude beta R x)
    atTop (nhds 0)
```

- [ ] **Step 5: Prove cubic Perron truncation negligibility**

Use `exists_norm_residue_sum_sub_thirdOrderContourRemainder_sub_secondRieszPsi_le`
with `c(x)=1+1/log x` and `W=T/(2*pi)`.  Bound the von Mangoldt Dirichlet
majorant by an explicit constant times `x^c(x)` and apply the exponent from
Step 2.

- [ ] **Step 6: Compile and commit Task 4**

```bash
git add PrimeNumberTheorem/ZeroDensityLayerBudgetActualCubicContourBudget.lean PrimeNumberTheorem/ZeroDensityLayerBudgetActualCubicContourBudgetContract.lean PrimeNumberTheorem/ZeroDensityLayerBudgetActualCubicContourBudgetAxiomAudit.lean
git commit -m "feat: decay cubic contour at the target scale"
```

### Task 5: Assemble the high-to-low certificate

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualCubicTwoHeightL2Tail.lean`
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualCubicTwoHeightL2TailContract.lean`
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualCubicTwoHeightL2TailAxiomAudit.lean`
- Create: `docs/research/pintz-carlson-actual-cubic-two-height-l2-tail.md`

**Interfaces:**
- Consumes: Tasks 1-4 and `exists_jointTwoHeightTargetAmplitudeParameters`.
- Produces: one certificate containing the actual cubic formula, low detector height, middle/high coefficient-square tail, contour decay, and precise half-isolated handoff.

- [ ] **Step 1: Define the certificate structure**

```lean
structure ActualCubicHighToLowL2TailCertificate (beta : ℝ) where
  sigma : ℝ
  tau : ℝ
  alpha : ℝ
  gammaLow : ℝ
  gammaHigh : ℝ
  epsilonLow : ℝ
  epsilonHigh : ℝ
  parameterConditions :
    1 / 2 < sigma ∧ sigma < tau ∧ tau < beta ∧
    gammaLow = alpha / 2 ∧
    gammaHigh = carlsonTwoHeightBalancedCut sigma alpha
  strictExponentConditions :
    gammaLow + sigma - beta + epsilonLow < 0 ∧
    alpha + sigma - beta - gammaLow + epsilonLow < 0 ∧
    targetAmplitudeCarlsonTwoHeightLowExponent
      beta sigma tau gammaHigh + epsilonHigh < 0 ∧
    targetAmplitudeCarlsonTwoHeightHighExponent
      beta sigma tau alpha gammaHigh + epsilonHigh < 0
  cubicBlockConditions :
    cubicCarlsonL2BlockExponent beta sigma tau gammaLow < 0 ∧
    cubicCarlsonL2BlockExponent beta sigma tau gammaHigh < 0 ∧
    cubicCarlsonL2BlockExponent beta sigma tau alpha < 0
```

The capacity and contour conclusions remain theorem fields parameterized by
`x`, dyadic brackets, target radius `R`, and finite deletion set `S`; they are
not hidden in an unconstrained proposition.

- [ ] **Step 2: Construct the certificate for every `2/3<beta<1`**

Prove

```lean
theorem exists_actualCubicHighToLowL2TailCertificate
    (hbeta : 2 / 3 < beta) (hbetaOne : beta < 1) :
    Nonempty (ActualCubicHighToLowL2TailCertificate beta)
```

by unpacking the joint parameter theorem and attaching the cubic block and
contour exponent lemmas.

- [ ] **Step 3: Expose the half-isolated handoff theorem**

State a theorem returning the coefficient-square tail bound after any finite
`S`.  Its conclusion names the exact capacity consumed by a later Occupancy
theorem and contains no Gram matrix premise or conclusion.

- [ ] **Step 4: Document the quantitative ledger**

The research note records:

```text
Carlson count exponent: q(sigma) <= 1
reciprocal-square L2 exponent: q(sigma)-2 <= -1
cubic L2 exponent: q(sigma)-6 <= -5
Carlson log loss: log^4
square multiplicity loss: one extra log
total dyadic loss: log^5
sigma=1/2 equality: q=1 only; L2 exponents remain -1 and -5
```

It also records the three contour exponents and the fact that no de-smoothed
contour estimate was used.

- [ ] **Step 5: Run the focused verification**

Compile both source modules, both contracts, and both axiom audits in an
isolated overlay.  Run the exact declaration scan for `sorry`, `admit`, and
project `axiom`.

- [ ] **Step 6: Commit Task 5**

```bash
git add PrimeNumberTheorem/ZeroDensityLayerBudgetActualCubicTwoHeightL2Tail.lean PrimeNumberTheorem/ZeroDensityLayerBudgetActualCubicTwoHeightL2TailContract.lean PrimeNumberTheorem/ZeroDensityLayerBudgetActualCubicTwoHeightL2TailAxiomAudit.lean docs/research/pintz-carlson-actual-cubic-two-height-l2-tail.md
git commit -m "feat: assemble actual cubic high-to-low L2 tail"
```

### Task 6: Publish the independent PR

**Files:**
- No source changes.

**Interfaces:**
- Consumes: verified commits from Tasks 1-5.
- Produces: the third independent draft PR with a diff only against the frozen cubic-L2 dependency base.

- [ ] **Step 1: Push the frozen base reference**

Push `research/pintz-carlson-actual-cubic-two-height-l2-tail-base` without
creating a PR for it.

- [ ] **Step 2: Push the feature branch**

Push `research/pintz-carlson-actual-cubic-two-height-l2-tail` and set its
upstream.

- [ ] **Step 3: Create the draft PR**

Use the frozen base branch as `--base`.  The PR body lists theorem names,
polynomial exponents, `log^5`, finite-set monotonicity, contour exponents,
focused build results, and the Sharp/half-isolated claim boundary.

- [ ] **Step 4: Confirm the GitHub diff**

Confirm that the PR does not contain the files introduced by PR #94 or PR
#258 and does not touch protected Sharp, half-isolated, or VK-edge modules.
