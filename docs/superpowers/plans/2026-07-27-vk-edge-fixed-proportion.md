# VK-Edge Fixed-Proportion Large Values Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove that the explicit local L2 lower bound forced by an off-line zeta zero yields a fixed-proportion large-value set whenever the true normalized PNT error has a matching local fourth-moment upper bound.

**Architecture:** A zeta-independent scaled Paley--Zygmund module converts second/fourth moments on a finite-measure set into an explicit measure lower bound. A separate VK-edge module instantiates it with the PR #23 L2 constant and the epsilon logarithmic interval. The true-error fourth moment remains a visible theorem hypothesis.

**Tech Stack:** Lean 4, Mathlib measure theory and Bochner integration, existing `MathlibAux.PaleyZygmund`, existing `PrimeNumberTheorem.VKEdgePiOverTwoSweptL2`.

## Global Constraints

- Base all work on `research/vk-edge-swept-l2` commit `8c88f56`.
- Do not modify `main`, PR #22, or PR #23.
- Do not introduce a `def ... : Prop` target.
- Do not instantiate the fourth-moment hypothesis with a finite exponential-polynomial estimate unless the true contour remainder is also controlled in fourth moment.
- Do not claim a Carlson contradiction, exclusion of off-line zeros, or RH.
- New public theorems may use only Lean/Mathlib standard logical axioms.

---

### Task 1: Lock the generic scaled Paley--Zygmund contract

**Files:**
- Create: `Test/ScaledPaleyZygmundContract.lean`

**Interfaces:**
- Consumes: `MathlibAux.paleyZygmund_mul_secondMoment_le_measure`.
- Produces: the exact public signature of `MathlibAux.measure_sq_largeSet_gt_of_scaled_moments`.

- [ ] **Step 1: Write the failing contract**

```lean
import MathlibAux.ScaledPaleyZygmund

open MeasureTheory Set

#check MathlibAux.measure_sq_largeSet_gt_of_scaled_moments

example
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} {g : α → ℝ} {ε L c2 C4 θ : ℝ}
    (hs : MeasurableSet s) (hμs : μ s ≠ ⊤)
    (hmeasure : μ.real s = ε * L)
    (hε : 0 < ε) (hL : 0 < L)
    (hc2 : 0 < c2) (hC4 : 0 < C4)
    (hg : Measurable g)
    (hg4 : IntegrableOn (fun x => g x ^ 4) s μ)
    (hsecond : c2 * L < ∫ x in s, g x ^ 2 ∂μ)
    (hfourth : (∫ x in s, g x ^ 4 ∂μ) ≤ C4 * L)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ((1 - θ) ^ 2 * c2 ^ 2 / C4) * L <
      μ.real {x ∈ s | θ * c2 / ε < g x ^ 2} :=
  MathlibAux.measure_sq_largeSet_gt_of_scaled_moments
    hs hμs hmeasure hε hL hc2 hC4 hg hg4 hsecond hfourth hθ0 hθ1
```

- [ ] **Step 2: Run the contract and verify RED**

Run:

```bash
lake build Test.ScaledPaleyZygmundContract
```

Expected: failure because `MathlibAux.ScaledPaleyZygmund` does not exist.

- [ ] **Step 3: Commit the RED contract**

```bash
git add Test/ScaledPaleyZygmundContract.lean
git commit -m "test: specify scaled Paley-Zygmund transfer"
```

### Task 2: Prove the generic scaled transfer

**Files:**
- Create: `MathlibAux/ScaledPaleyZygmund.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes: the Task 1 contract and `paleyZygmund_mul_secondMoment_le_measure`.
- Produces:

```lean
MathlibAux.measure_sq_largeSet_gt_of_scaled_moments
```

- [ ] **Step 1: Create the module and derive interval positivity**

Import `MathlibAux.PaleyZygmund`. Derive

```lean
0 < μ.real s
```

from `hmeasure`, `hε`, and `hL`.

- [ ] **Step 2: Apply product-form Paley--Zygmund to `g ^ 2`**

Use:

```lean
paleyZygmund_mul_secondMoment_le_measure
```

with `f := fun x => g x ^ 2`. Convert `(g ^ 2) ^ 2` to `g ^ 4` using
`← pow_mul`.

- [ ] **Step 3: Compare the moving threshold to the fixed threshold**

Prove:

```lean
{x ∈ s |
    θ * ((∫ y in s, g y ^ 2 ∂μ) / μ.real s) < g x ^ 2}
  ⊆
{x ∈ s | θ * c2 / ε < g x ^ 2}.
```

Use `hsecond`, `hmeasure`, `hε`, `hL`, and `hθ0`.

- [ ] **Step 4: Extract the explicit measure constant**

Combine:

```text
(1-theta)^2 * (integral g^2)^2
  <= measure(good) * integral g^4
  <= measure(good) * C4 * L
```

with `hsecond`. Cancel the positive factor `C4 * L` to obtain the contract
conclusion.

- [ ] **Step 5: Register and run GREEN**

Add:

```lean
`MathlibAux.ScaledPaleyZygmund,
`Test.ScaledPaleyZygmundContract,
```

to `lakefile.lean`, then run:

```bash
lake build MathlibAux.ScaledPaleyZygmund Test.ScaledPaleyZygmundContract
```

Expected: success.

- [ ] **Step 6: Commit**

```bash
git add MathlibAux/ScaledPaleyZygmund.lean lakefile.lean
git commit -m "feat: quantify scaled Paley-Zygmund large sets"
```

### Task 3: Lock the VK-edge fixed-proportion endpoint

**Files:**
- Create: `Test/VKEdgePiOverTwoFixedProportionContract.lean`

**Interfaces:**
- Consumes: `exists_eventually_ordinarySecondMoment_in_epsilonLogWindow_gt_linear` and Task 2.
- Produces the exact signature of:

```lean
exists_eventually_fixedProportion_largeNormalizedPsiError_of_fourthMoment
```

- [ ] **Step 1: Write the failing contract**

The endpoint takes:

```lean
(hC4 : 0 < C4)
(hfourth :
  ∀ᶠ Y : ℝ in Filter.atTop,
    IntegrableOn
      (fun y => normalizedPsiError rho y ^ 4)
      (Set.Icc (Real.log Y) ((1 + ε) * Real.log Y)) ∧
    (∫ y in Set.Icc (Real.log Y) ((1 + ε) * Real.log Y),
        normalizedPsiError rho y ^ 4) ≤ C4 * Real.log Y)
```

and returns a harmonic `k`, the missing-harmonic nonvanishing condition,
positivity of

```lean
c2 = centeredSharpenedSweptOrdinaryL2Constant ε rho k,
```

and eventually:

```lean
(c2 ^ 2 / (4 * C4)) * Real.log Y <
  volume.real
    {y ∈ Set.Icc (Real.log Y) ((1 + ε) * Real.log Y) |
      c2 / (2 * ε) < normalizedPsiError rho y ^ 2}.
```

- [ ] **Step 2: Run the contract and verify RED**

Run:

```bash
lake build Test.VKEdgePiOverTwoFixedProportionContract
```

Expected: failure because the endpoint module does not exist.

- [ ] **Step 3: Commit the RED contract**

```bash
git add Test/VKEdgePiOverTwoFixedProportionContract.lean
git commit -m "test: specify fixed-proportion VK-edge endpoint"
```

### Task 4: Implement the zeta endpoint

**Files:**
- Create: `PrimeNumberTheorem/VKEdgePiOverTwoFixedProportion.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes: Tasks 2 and 3, plus the PR #23 swept local L2 endpoint.
- Produces:

```lean
exists_eventually_fixedProportion_largeNormalizedPsiError_of_fourthMoment
```

- [ ] **Step 1: Expose measurability for normalized error**

Prove in the new module:

```lean
theorem measurable_normalizedPsiError (rho : ℂ) :
  Measurable (normalizedPsiError rho)
```

using `Chebyshev.psi_mono.measurable`, matching the private proof in
`VKEdgePiOverTwoPositiveMeasure.lean`.

- [ ] **Step 2: Obtain the harmonic and L2 lower bound**

Destructure:

```lean
exists_eventually_ordinarySecondMoment_in_epsilonLogWindow_gt_linear
```

to obtain `k`, `hmissing`, `hc2`, and the eventual second-moment inequality.

- [ ] **Step 3: Prove the epsilon-window measure identity**

For sufficiently large `Y`, prove `1 < Y` and:

```lean
volume.real
    (Set.Icc (Real.log Y) ((1 + ε) * Real.log Y))
  = ε * Real.log Y.
```

Use `Real.volume_Icc`, `Measure.real`, and
`ENNReal.toReal_ofReal`.

- [ ] **Step 4: Apply the generic theorem with `theta = 1 / 2`**

Combine the eventual L2 and L4 facts. Instantiate:

```text
L = log Y
c2 = centeredSharpenedSweptOrdinaryL2Constant epsilon rho k
theta = 1 / 2
```

Normalize the resulting constants with `ring_nf` and `field_simp`.

- [ ] **Step 5: Register and run GREEN**

Add the source and contract modules to `lakefile.lean`, then run:

```bash
lake build \
  PrimeNumberTheorem.VKEdgePiOverTwoFixedProportion \
  Test.VKEdgePiOverTwoFixedProportionContract
```

Expected: success.

- [ ] **Step 6: Commit**

```bash
git add \
  PrimeNumberTheorem/VKEdgePiOverTwoFixedProportion.lean \
  lakefile.lean
git commit -m "feat: derive fixed-proportion PNT-error large values"
```

### Task 5: Audit the theorem and contradiction boundary

**Files:**
- Create: `Test/VKEdgePiOverTwoFixedProportionAxiomAudit.lean`
- Create: `docs/research/vk-edge-fixed-proportion-contradiction-audit.md`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes: Task 4 public theorem.
- Produces: standard-axiom evidence and a precise inventory of missing RH inputs.

- [ ] **Step 1: Add axiom prints**

```lean
import PrimeNumberTheorem.VKEdgePiOverTwoFixedProportion

open PrimeNumberTheorem.VKEdgePiOverTwo

#print axioms MathlibAux.measure_sq_largeSet_gt_of_scaled_moments
#print axioms exists_eventually_fixedProportion_largeNormalizedPsiError_of_fourthMoment
```

- [ ] **Step 2: Record the upper-bound audit**

Document:

- why `ExponentialPolynomialFourthMoment` does not apply to the true error;
- the exact contour-remainder L4 estimate needed to instantiate the endpoint;
- why fixed-proportion error locations do not count distinct zeta zeros;
- what additional injection or incompatible upper bound would produce an RH contradiction.

- [ ] **Step 3: Run focused audit and source scan**

```bash
lake build \
  Test.ScaledPaleyZygmundContract \
  Test.VKEdgePiOverTwoFixedProportionContract \
  Test.VKEdgePiOverTwoFixedProportionAxiomAudit
rg -n '\\b(sorry|admit|axiom)\\b' \
  MathlibAux/ScaledPaleyZygmund.lean \
  PrimeNumberTheorem/VKEdgePiOverTwoFixedProportion.lean \
  Test/ScaledPaleyZygmundContract.lean \
  Test/VKEdgePiOverTwoFixedProportionContract.lean
```

Expected: build success, only standard logical axioms, no forbidden source
tokens.

- [ ] **Step 4: Commit**

```bash
git add \
  Test/VKEdgePiOverTwoFixedProportionAxiomAudit.lean \
  docs/research/vk-edge-fixed-proportion-contradiction-audit.md \
  lakefile.lean
git commit -m "test: audit fixed-proportion VK-edge theorem"
```

### Task 6: Full verification and dependent PR

**Files:**
- No new source files.

**Interfaces:**
- Consumes: all previous tasks.
- Produces: verified branch and dependent draft PR.

- [ ] **Step 1: Run full verification**

```bash
git diff --check
./scripts/verify-baseline.sh
```

Expected: full build success, target inventory consistency, chain-gap
consistency, and axiom allowlist success.

- [ ] **Step 2: Push**

```bash
git push -u origin research/vk-edge-fixed-proportion
```

- [ ] **Step 3: Open a dependent draft PR**

Create the PR with:

```text
base: research/vk-edge-swept-l2
head: research/vk-edge-fixed-proportion
```

The PR description must state that the theorem is conditional on both an
off-line zero and a matching fourth-moment upper bound, and that it does not
prove RH or a zero-density contradiction.
