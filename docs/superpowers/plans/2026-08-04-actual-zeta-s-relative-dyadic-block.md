# Actual-zeta S-relative Dyadic Block Gram Implementation Plan

> **For the implementing agent:** REQUIRED SUB-SKILL: Use
> superpowers:executing-plans to implement this plan task-by-task.  Steps use
> checkbox (`- [ ]`) syntax for tracking.  Do not delegate unless the user
> explicitly requests sub-agent execution.

**Goal:** Prove on current `main` that one actual, target-normalized, S-relative zeta dyadic block either contains a surviving zero strictly right of `beta` or has whole-Gram energy bounded by actual reciprocal-square Carlson capacity, with a single-block count corollary.

**Architecture:** Filter the existing bucket-labelled genuine zeta block to the actual positive-ordinate Carlson shell and delete `S`.  Split on a surviving zero with `beta < rho.re`; on the complementary branch identify the source set with the `rho.re <= beta` target set, apply the existing drifting whole-Gram Schur theorem, and dominate squared target masses by the existing S-relative square capacity.  A separate corollary combines actual occupancy `O(log H)` and the merged `m^2 -> log(H) m` Carlson capacity theorem without summing over blocks.

**Tech Stack:** Lean 4.29.1, Mathlib, `MathlibAux.DyadicDriftingGaussianSchur`, actual zeta dyadic adapters, actual Carlson dyadic capacity modules, Lake Contract/AxiomAudit targets.

## Global Constraints

- Work only in `codex/actual-zeta-s-relative-dyadic-block-main`, replayed onto the then-current `origin/main` before validation.
- Production code imports only modules already merged into `main`; do not import or copy PRs #268, #289, #294, or #304.
- Preserve actual zeta membership, target normalization, the strict `beta < rho.re` witness branch, and arbitrary finite deletion by `S`.
- Constants and height thresholds are quantified before `S` and must not depend on `S.card`.
- Do not alter any existing occupancy definition, global constant, theorem assumption, or protected module.
- Do not add finite-range aggregation, a high-tail sum, smoothing, two-height transfer, D1 cluster mass, Witness/Sharp input, set growth, a fixed-half-plane exclusion, or RH claims.
- Run no Lean/Lake command without an explicit single-build resource window; never treat an old-base result as current-head evidence.

---

## File map

- Create `PrimeNumberTheorem/ZeroDensityLayerBudgetActualTargetDyadicBlockGram.lean`: all new actual finite sets, target mass, occupancy, whole-Gram dichotomy, and the single-block Carlson corollary.
- Create `Test/ZeroDensityLayerBudgetActualTargetDyadicBlockGramContract.lean`: exact typed public-interface examples and boundary tests.
- Create `Test/ZeroDensityLayerBudgetActualTargetDyadicBlockGramAxiomAudit.lean`: `#print axioms` for every public theorem.
- Modify `RiemannPNT.lean`: import the production module only.
- Modify `lakefile.lean`: register production, Contract, and AxiomAudit modules.
- Modify `scripts/check_axiom_allowlist.py`: register only the new audit module and its public declarations.
- Preserve `docs/superpowers/specs/2026-08-04-actual-zeta-s-relative-dyadic-block-design.md`.
- Use this plan as the only implementation-plan addition.

---

### Task 1: Actual S-relative pair sets and occupancy

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualTargetDyadicBlockGram.lean`
- Create: `Test/ZeroDensityLayerBudgetActualTargetDyadicBlockGramContract.lean`

**Interfaces:**
- Consumes: `zetaDyadicBucketPairs`, `mem_zetaDyadicBucketPairs`, `zetaDyadicBucketPairs_snd_inj`, `actualCarlsonDyadicZeroShell`, and `actualCarlsonDyadicZeroStrip`.
- Produces:
  - `actualSRelativeDyadicBucketPairs (S : Finset ℂ) (sigma : ℝ) (k : ℕ) : Finset (ℕ × ℂ)`
  - `actualTargetDyadicBucketPairsExcluding (S : Finset ℂ) (sigma beta : ℝ) (k : ℕ) : Finset (ℕ × ℂ)`
  - `actualTargetDyadicOccupancy (S : Finset ℂ) (sigma beta : ℝ) (k : ℕ) : ℕ`
  - membership, injectivity, source-equals-target, projection-to-strip, and fibre-cardinality lemmas used by Tasks 2 and 3.

- [ ] **Step 1: Write the failing finite-set Contract**

Create the Contract with exact typed examples:

```lean
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualTargetDyadicBlockGram

open Complex

namespace PrimeNumberTheorem.VKEdgePiOverTwo

example (S : Finset ℂ) (sigma : ℝ) (k : ℕ) :
    actualSRelativeDyadicBucketPairs S sigma k =
      (zetaDyadicBucketPairs k).filter
        (fun p => p.2 ∈ actualCarlsonDyadicZeroShell sigma k \ S) := rfl

example (S : Finset ℂ) (sigma beta : ℝ) (k : ℕ) :
    actualTargetDyadicBucketPairsExcluding S sigma beta k =
      (actualSRelativeDyadicBucketPairs S sigma k).filter
        (fun p => p.2.re ≤ beta) := rfl

example {S : Finset ℂ} {sigma : ℝ} {k : ℕ} {p : ℕ × ℂ} :
    p ∈ actualSRelativeDyadicBucketPairs S sigma k ↔
      p ∈ zetaDyadicBucketPairs k ∧
        p.2 ∈ actualCarlsonDyadicZeroShell sigma k \ S :=
  mem_actualSRelativeDyadicBucketPairs

example {S : Finset ℂ} {sigma beta : ℝ} {k : ℕ} {p : ℕ × ℂ} :
    p ∈ actualTargetDyadicBucketPairsExcluding S sigma beta k ↔
      p ∈ actualSRelativeDyadicBucketPairs S sigma k ∧ p.2.re ≤ beta :=
  mem_actualTargetDyadicBucketPairsExcluding

example (S : Finset ℂ) (sigma beta : ℝ) (k : ℕ) :
    (actualTargetDyadicBucketPairsExcluding S sigma beta k).image Prod.snd ⊆
      actualCarlsonDyadicZeroStrip sigma beta k \ S :=
  image_snd_actualTargetDyadicBucketPairsExcluding_subset S sigma beta k

example {S : Finset ℂ} {sigma beta : ℝ} {k : ℕ}
    (hre : ∀ rho ∈ actualCarlsonDyadicZeroShell sigma k \ S,
      rho.re ≤ beta) :
    actualSRelativeDyadicBucketPairs S sigma k =
      actualTargetDyadicBucketPairsExcluding S sigma beta k :=
  actualSRelativeDyadicBucketPairs_eq_target_of_re_le hre

example (S : Finset ℂ) (sigma beta : ℝ) (k : ℕ) :
    actualTargetDyadicOccupancy S sigma beta k =
      ((actualTargetDyadicBucketPairsExcluding S sigma beta k).image
          Prod.fst).sup
        (fun n =>
          ((actualTargetDyadicBucketPairsExcluding S sigma beta k).filter
            (fun p => p.1 = n)).card) := rfl

example {S : Finset ℂ} {sigma beta : ℝ} {k n : ℕ} :
    ((actualTargetDyadicBucketPairsExcluding S sigma beta k).filter
      (fun p => p.1 = n)).card ≤
        actualTargetDyadicOccupancy S sigma beta k :=
  actualTargetDyadicBucket_fibre_card_le_occupancy S sigma beta k n

end PrimeNumberTheorem.VKEdgePiOverTwo
```

- [ ] **Step 2: Run the Contract and verify RED**

Run only after the resource window is granted:

```bash
lake -Kjobs=1 build Test.ZeroDensityLayerBudgetActualTargetDyadicBlockGramContract
```

Expected: failure because the production module or declarations do not exist.  A missing declaration is the intended RED result; an unrelated import-resolution error must be diagnosed before continuing.

- [ ] **Step 3: Implement the actual pair sets**

Start the production module with merged dependencies and the exact definitions:

```lean
import MathlibAux.DyadicDriftingGaussianSchur
import PrimeNumberTheorem.HalfIsolatedZetaDyadicAdapter
import PrimeNumberTheorem.ZeroDensityLayerBudgetDyadicSquareMultiplicityCapacity

open Complex Set
open scoped BigOperators

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

noncomputable def actualSRelativeDyadicBucketPairs
    (S : Finset ℂ) (sigma : ℝ) (k : ℕ) : Finset (ℕ × ℂ) :=
  (zetaDyadicBucketPairs k).filter fun p =>
    p.2 ∈ actualCarlsonDyadicZeroShell sigma k \ S

noncomputable def actualTargetDyadicBucketPairsExcluding
    (S : Finset ℂ) (sigma beta : ℝ) (k : ℕ) : Finset (ℕ × ℂ) :=
  (actualSRelativeDyadicBucketPairs S sigma k).filter fun p =>
    p.2.re ≤ beta
```

Prove simp membership lemmas by unfolding and `simp only [Finset.mem_filter]`.  Prove that `Prod.snd` is injective on both new sets by applying `zetaDyadicBucketPairs_snd_inj k` after extracting the filter membership.

Prove the projection-subset theorem

```lean
theorem image_snd_actualTargetDyadicBucketPairsExcluding_subset
    (S : Finset ℂ) (sigma beta : ℝ) (k : ℕ) :
    (actualTargetDyadicBucketPairsExcluding S sigma beta k).image Prod.snd ⊆
      actualCarlsonDyadicZeroStrip sigma beta k \ S
```

by eliminating `Finset.mem_image` and both filters.  Do not prove the reverse
inclusion: `zetaDyadicBucketPairs k` uses `[2^k, 2^(k+1))`, whereas
`actualCarlsonDyadicZeroShell sigma k` uses `(2^k, 2^(k+1)]`, so an actual zero
at the upper Carlson endpoint need not have a source pair.  Preserve both
existing height conventions unchanged.

Prove the branch identification theorem:

```lean
theorem actualSRelativeDyadicBucketPairs_eq_target_of_re_le
    {S : Finset ℂ} {sigma beta : ℝ} {k : ℕ}
    (hre : ∀ rho ∈ actualCarlsonDyadicZeroShell sigma k \ S,
      rho.re ≤ beta) :
    actualSRelativeDyadicBucketPairs S sigma k =
      actualTargetDyadicBucketPairsExcluding S sigma beta k
```

by extensionality, membership simplification, and `hre`.

- [ ] **Step 4: Implement exact actual occupancy**

Use the maximum of the target fibres without modifying any existing object:

```lean
noncomputable def actualTargetDyadicOccupancy
    (S : Finset ℂ) (sigma beta : ℝ) (k : ℕ) : ℕ :=
  ((actualTargetDyadicBucketPairsExcluding S sigma beta k).image Prod.fst).sup
    (fun n =>
      ((actualTargetDyadicBucketPairsExcluding S sigma beta k).filter
        (fun p => p.1 = n)).card)
```

For labels in the image, use `Finset.le_sup`; for labels outside the image,
prove the fibre is empty.  Package both cases as:

```lean
theorem actualTargetDyadicBucket_fibre_card_le_occupancy
    (S : Finset ℂ) (sigma beta : ℝ) (k n : ℕ) :
    ((actualTargetDyadicBucketPairsExcluding S sigma beta k).filter
      (fun p => p.1 = n)).card ≤
        actualTargetDyadicOccupancy S sigma beta k
```

- [ ] **Step 5: Run the finite-set Contract and verify GREEN**

```bash
lake -Kjobs=1 build \
  PrimeNumberTheorem.ZeroDensityLayerBudgetActualTargetDyadicBlockGram \
  Test.ZeroDensityLayerBudgetActualTargetDyadicBlockGramContract
```

Expected: both targets pass.  Confirm the empty-set and complete-deletion examples reduce by `simp`, and that the real-part filter uses `≤`, not `<`.

- [ ] **Step 6: Commit Task 1**

```bash
git add \
  PrimeNumberTheorem/ZeroDensityLayerBudgetActualTargetDyadicBlockGram.lean \
  Test/ZeroDensityLayerBudgetActualTargetDyadicBlockGramContract.lean
git commit -m "feat: define actual S-relative dyadic block"
```

---

### Task 2: Target mass, whole-Gram energy, and exact capacity dichotomy

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualTargetDyadicBlockGram.lean`
- Modify: `Test/ZeroDensityLayerBudgetActualTargetDyadicBlockGramContract.lean`

**Interfaces:**
- Consumes: all Task 1 sets and occupancy, `MathlibAux.dyadicDriftingGaussianGram_le_occupancy_mul_sum_sq`, `zeroReciprocalMultiplicityCoefficient`, and `actualCarlsonDyadicStripSquareReciprocalCapacityExcluding`.
- Produces:
  - `actualTargetDyadicBaseMass`
  - `actualTargetDyadicForwardDrift`
  - `actualSRelativeTargetDyadicGaussianGram`
  - `actualSRelativeDyadic_fartherRight_or_gram_le_capacity`

- [ ] **Step 1: Append the failing energy Contract**

Add exact typed examples:

```lean
example (beta a : ℝ) (p : ℕ × ℂ) :
    actualTargetDyadicBaseMass beta a p =
      zeroReciprocalMultiplicityCoefficient p.2 *
        Real.exp ((p.2.re - beta) * a) := rfl

example (beta : ℝ) (p : ℕ × ℂ) :
    actualTargetDyadicForwardDrift beta p = p.2.re - beta := rfl

example (S : Finset ℂ) (sigma beta a : ℝ) (k : ℕ) (t m : ℝ) :
    actualSRelativeTargetDyadicGaussianGram S sigma beta a k t m =
      MathlibAux.dyadicDriftingGaussianGram
        (actualSRelativeDyadicBucketPairs S sigma k)
        (actualTargetDyadicBaseMass beta a)
        (actualTargetDyadicForwardDrift beta)
        (fun p => p.2.im) t m := rfl
```

Also add an exact theorem example for the dichotomy, including the surviving shell membership, strict `beta < rho.re`, and the capacity RHS.

- [ ] **Step 2: Run the Contract and verify RED**

```bash
lake -Kjobs=1 build Test.ZeroDensityLayerBudgetActualTargetDyadicBlockGramContract
```

Expected: failure on the first new declaration.

- [ ] **Step 3: Implement the target mass and Gram object**

```lean
noncomputable def actualTargetDyadicBaseMass
    (beta a : ℝ) (p : ℕ × ℂ) : ℝ :=
  zeroReciprocalMultiplicityCoefficient p.2 *
    Real.exp ((p.2.re - beta) * a)

def actualTargetDyadicForwardDrift
    (beta : ℝ) (p : ℕ × ℂ) : ℝ :=
  p.2.re - beta

noncomputable def actualSRelativeTargetDyadicGaussianGram
    (S : Finset ℂ) (sigma beta a : ℝ) (k : ℕ) (t m : ℝ) : ℝ :=
  MathlibAux.dyadicDriftingGaussianGram
    (actualSRelativeDyadicBucketPairs S sigma k)
    (actualTargetDyadicBaseMass beta a)
    (actualTargetDyadicForwardDrift beta)
    (fun p => p.2.im) t m
```

Prove nonnegativity of base mass from `zeroReciprocalMultiplicityCoefficient` and `Real.exp_pos`.  Reuse the frequency-gap proof pattern from `zetaRightDyadic_frequency_gap`; derive both unit-bucket memberships from Task 1 membership rather than duplicating zero facts.

- [ ] **Step 4: Bound squared base mass by actual capacity**

Prove for `0 ≤ a`:

```lean
theorem sum_actualTargetDyadicBaseMass_sq_le_capacity
    (S : Finset ℂ) (sigma beta a : ℝ) (k : ℕ) (ha : 0 ≤ a) :
    (∑ p ∈ actualTargetDyadicBucketPairsExcluding S sigma beta k,
      actualTargetDyadicBaseMass beta a p ^ 2) ≤
        actualCarlsonDyadicStripSquareReciprocalCapacityExcluding
          sigma beta k S
```

For each target pair, `p.2.re - beta ≤ 0`, hence
`Real.exp ((p.2.re - beta) * a) ≤ 1`.  Square the nonnegative product and
bound it by `(analyticOrderNatAt riemannZeta p.2 : ℝ)^2 / ||p.2||^2`.
Use Task 1 injectivity to rewrite the pair sum as a sum over its second-image,
then use the projection-subset theorem and nonnegativity to enlarge it to the
S-relative actual strip.  Do not replace multiplicity by cardinality.

- [ ] **Step 5: Prove the exact farther-right/capacity dichotomy**

Implement:

```lean
theorem actualSRelativeDyadic_fartherRight_or_gram_le_capacity
    (S : Finset ℂ) (sigma beta a : ℝ) (k : ℕ) {t m : ℝ}
    (ha : 0 ≤ a) (ht : 0 ≤ t) (hm : 1 ≤ m) :
    (∃ rho ∈ actualCarlsonDyadicZeroShell sigma k \ S,
      beta < rho.re) ∨
      actualSRelativeTargetDyadicGaussianGram S sigma beta a k t m ≤
        MathlibAux.gaussianBucketSchurConstant *
          (1 + (actualTargetDyadicOccupancy S sigma beta k : ℝ)) *
            actualCarlsonDyadicStripSquareReciprocalCapacityExcluding
              sigma beta k S
```

Split with `by_cases hfar`.  Return `Or.inl hfar` directly in the first case.
In the negative case, push negation to obtain `rho.re ≤ beta` for every
surviving shell zero, rewrite the source pair set with Task 1's
source-equals-target theorem, and apply
`MathlibAux.dyadicDriftingGaussianGram_le_occupancy_mul_sum_sq` with:

- `bucket := Prod.fst`;
- `occupancy := actualTargetDyadicOccupancy S sigma beta k`;
- nonpositive drift from the no-far hypothesis;
- Task 1's fibre bound, weakened to `card ≤ occupancy + 1`; and
- the existing unit-bucket frequency-gap lemma.

Finish by `sum_actualTargetDyadicBaseMass_sq_le_capacity` and nonnegative
constant multiplication.  Keep the full Gram on the left throughout.

- [ ] **Step 6: Run the energy Contract and verify GREEN**

```bash
lake -Kjobs=1 build \
  PrimeNumberTheorem.ZeroDensityLayerBudgetActualTargetDyadicBlockGram \
  Test.ZeroDensityLayerBudgetActualTargetDyadicBlockGramContract
```

Expected: pass.  Inspect the theorem type to verify strict `beta < rho.re`,
`≤ beta` in the target set, and no assumption excluding farther-right zeros.

- [ ] **Step 7: Commit Task 2**

```bash
git add \
  PrimeNumberTheorem/ZeroDensityLayerBudgetActualTargetDyadicBlockGram.lean \
  Test/ZeroDensityLayerBudgetActualTargetDyadicBlockGramContract.lean
git commit -m "feat: bound actual target dyadic Gram energy"
```

---

### Task 3: Uniform occupancy and single-block Carlson count corollary

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetActualTargetDyadicBlockGram.lean`
- Modify: `Test/ZeroDensityLayerBudgetActualTargetDyadicBlockGramContract.lean`

**Interfaces:**
- Consumes: Task 2 exact dichotomy, `exists_zeroOrdinateUnitBucketMultiplicity_le_log`, and `exists_actualCarlsonDyadicStripSquareReciprocalCapacityExcluding_le_count`.
- Produces:
  - `exists_actualTargetDyadicOccupancy_le_log`
  - `exists_actualSRelativeDyadic_fartherRight_or_gram_le_count`

- [ ] **Step 1: Append failing uniform-constant Contracts**

Add exact examples with constant order before `S`:

```lean
example : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (S : Finset ℂ) (sigma beta : ℝ) (k : ℕ),
      4 ≤ 2 ^ k →
      (actualTargetDyadicOccupancy S sigma beta k : ℝ) ≤
        C * (1 + Real.log ((2 : ℝ) ^ (k + 1) + 7)) :=
  exists_actualTargetDyadicOccupancy_le_log
```

Add the exact single-block count dichotomy with one `D` quantified before
`S`, the high-block hypothesis `4 ≤ 2^k`, and no summation over `k`.

- [ ] **Step 2: Run the Contract and verify RED**

```bash
lake -Kjobs=1 build Test.ZeroDensityLayerBudgetActualTargetDyadicBlockGramContract
```

Expected: failure on `exists_actualTargetDyadicOccupancy_le_log`.

- [ ] **Step 3: Prove logarithmic actual occupancy**

Obtain `C` from `exists_zeroOrdinateUnitBucketMultiplicity_le_log`.  For every
target fibre:

1. inject its second projections into `zeroOrdinateUnitBucket n`;
2. bound fibre cardinality by the sum of analytic multiplicities because each
   zero in the finite zero set has positive analytic order;
3. apply the unit-bucket multiplicity theorem at `n`;
4. use `n < 2^(k+1)` and monotonicity of `Real.log` to replace `n + 7` by
   `2^(k+1) + 7`; and
5. take the finite supremum.

The theorem type is exactly:

```lean
theorem exists_actualTargetDyadicOccupancy_le_log :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : Finset ℂ) (sigma beta : ℝ) (k : ℕ), 4 ≤ 2 ^ k →
        (actualTargetDyadicOccupancy S sigma beta k : ℝ) ≤
          C * (1 + Real.log ((2 : ℝ) ^ (k + 1) + 7))
```

The proof chooses `C` before introducing `S`.

- [ ] **Step 4: Prove the single-block Carlson-count corollary**

Obtain `Cocc` from the occupancy theorem and `Ccap` from
`exists_actualCarlsonDyadicStripSquareReciprocalCapacityExcluding_le_count`.
Choose a nonnegative uniform constant such as

```lean
let D := MathlibAux.gaussianBucketSchurConstant * (Cocc + 1) * Ccap
```

and prove:

```lean
theorem exists_actualSRelativeDyadic_fartherRight_or_gram_le_count :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (S : Finset ℂ) (sigma beta a : ℝ) (k : ℕ) {t m : ℝ},
        0 ≤ a → 0 ≤ t → 1 ≤ m → 4 ≤ 2 ^ k →
        (∃ rho ∈ actualCarlsonDyadicZeroShell sigma k \ S,
          beta < rho.re) ∨
          actualSRelativeTargetDyadicGaussianGram S sigma beta a k t m ≤
            D * (1 + Real.log ((2 : ℝ) ^ (k + 1) + 7)) ^ 2 *
              (actualCarlsonDyadicCount sigma (k + 1) /
                ((2 : ℝ) ^ k) ^ 2)
```

Use Task 2's exact dichotomy.  In the energy branch, apply the occupancy and
capacity bounds, use `1 ≤ 1 + log(...)`, and monotonically replace the
capacity logarithm with the common `+7` logarithm.  Normalize products by
`ring`; do not expand or sum `actualCarlsonDyadicCount`.

- [ ] **Step 5: Run the full Contract and inspect quantifier order**

```bash
lake -Kjobs=1 build \
  PrimeNumberTheorem.ZeroDensityLayerBudgetActualTargetDyadicBlockGram \
  Test.ZeroDensityLayerBudgetActualTargetDyadicBlockGramContract
```

Expected: pass.  Confirm in the compiled Contract that `D` precedes `S`, and
that the result is one-block only.

- [ ] **Step 6: Commit Task 3**

```bash
git add \
  PrimeNumberTheorem/ZeroDensityLayerBudgetActualTargetDyadicBlockGram.lean \
  Test/ZeroDensityLayerBudgetActualTargetDyadicBlockGramContract.lean
git commit -m "feat: connect actual dyadic Gram to Carlson count"
```

---

### Task 4: Axiom audit, repository wiring, and current-main gates

**Files:**
- Create: `Test/ZeroDensityLayerBudgetActualTargetDyadicBlockGramAxiomAudit.lean`
- Modify: `RiemannPNT.lean`
- Modify: `lakefile.lean`
- Modify: `scripts/check_axiom_allowlist.py`
- Modify: `Test/ZeroDensityLayerBudgetActualTargetDyadicBlockGramContract.lean`

**Interfaces:**
- Consumes: every public declaration from Tasks 1-3.
- Produces: registered production/Contract/AxiomAudit targets and exact allowlist coverage.

- [ ] **Step 1: Write the AxiomAudit**

Create an audit importing only the production module and printing axioms for
all public theorems, including:

```lean
#print axioms mem_actualSRelativeDyadicBucketPairs
#print axioms mem_actualTargetDyadicBucketPairsExcluding
#print axioms image_snd_actualTargetDyadicBucketPairsExcluding_subset
#print axioms actualSRelativeDyadicBucketPairs_eq_target_of_re_le
#print axioms actualTargetDyadicBucket_fibre_card_le_occupancy
#print axioms sum_actualTargetDyadicBaseMass_sq_le_capacity
#print axioms actualSRelativeDyadic_fartherRight_or_gram_le_capacity
#print axioms exists_actualTargetDyadicOccupancy_le_log
#print axioms exists_actualSRelativeDyadic_fartherRight_or_gram_le_count
```

The public surface of this slice is exactly the nine declarations listed
above.  Keep every proof-only helper private, and do not add another public
declaration without first revising and re-approving this plan and its design
specification.

- [ ] **Step 2: Register repository wiring**

Add exactly one production import to `RiemannPNT.lean`.  Register the
production, Contract, and AxiomAudit modules in `lakefile.lean`.  Add the audit
module and each public theorem to `scripts/check_axiom_allowlist.py`, preserving
the existing ordering conventions.

- [ ] **Step 3: Run serial focused gates on current main**

After fetching and replaying the then-current `origin/main`, obtain an explicit
resource window and run one command at a time:

```bash
lake -Kjobs=1 build PrimeNumberTheorem.ZeroDensityLayerBudgetActualTargetDyadicBlockGram
lake -Kjobs=1 build Test.ZeroDensityLayerBudgetActualTargetDyadicBlockGramContract
lake -Kjobs=1 build Test.ZeroDensityLayerBudgetActualTargetDyadicBlockGramAxiomAudit
python3 scripts/check_axiom_allowlist.py
git diff --check origin/main...HEAD
git diff --name-only -z origin/main...HEAD -- '*.lean' |
  xargs -0 rg -n '^\s*(axiom|opaque)\b|\bsorry\b|\badmit\b|\bunsafe\b'
```

Expected:

- all three Lake targets pass;
- Contract contains exact typed examples, not bare `#check`;
- AxiomAudit reports only the repository-approved foundational axioms;
- allowlist exits zero with the exact new declaration count;
- `git diff --check` is silent; and
- the forbidden-declaration scan is silent.

- [ ] **Step 4: Commit wiring and audit**

```bash
git add \
  RiemannPNT.lean \
  lakefile.lean \
  scripts/check_axiom_allowlist.py \
  Test/ZeroDensityLayerBudgetActualTargetDyadicBlockGramAxiomAudit.lean \
  Test/ZeroDensityLayerBudgetActualTargetDyadicBlockGramContract.lean
git commit -m "test: audit actual S-relative dyadic block Gram bound"
```

- [ ] **Step 5: Prepare controlled integration evidence**

Record the exact base SHA, head SHA, focused job counts, Contract example
count, audited public theorem count, allowlist count, and static-scan results.
Do not run the full repository baseline locally unless the coordinator assigns
the exclusive baseline window.  Keep the PR Draft until the controlled
current-head baseline and independent fixed-head review pass.

---

## Plan self-review checklist

- Every spec-owned object appears in Tasks 1-3.
- The strict farther-right branch is explicit and no zero-free assumption is hidden.
- The energy is one full Gram matrix; no pairwise cross-term summation is planned.
- `S` appears only in finite deletion and is introduced after uniform constants.
- Analytic multiplicity remains squared with reciprocal-square height weight.
- Occupancy is a new local actual object; no existing occupancy is edited.
- The Carlson theorem is single-block and contains no dyadic sum.
- No forbidden downstream milestone appears in the implementation tasks.
- All code and test files have exact names, signatures, commands, and commit boundaries.
