# Exceptional-Zero Dyadic Carlson Summation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Complete the centered-frozen E2 upper bound by reindexing packet capacities onto actual zeta dyadic blocks, applying local multiplicity and Carlson estimates, and proving a whole-Gram finite-range bound with a uniform summable high tail.

**Architecture:** A reindex module proves exact packet/block identities and all one-block capacity estimates. A summation module applies the existing dynamic whole-Gram Schur theorem once to an entire dyadic bucket range, then reindexes only the diagonal packet-mass-square sum. Carlson's fixed-strip `IsBigO` theorem supplies a polynomial-geometric block majorant whose summability yields a uniform finite-range high-tail dichotomy.

**Tech Stack:** Lean 4.29.1, Mathlib finite sums and asymptotics, existing dynamic zeta packets, Gaussian Schur bounds, actual-zeta dyadic capacities, local multiplicity bounds, and `CarlsonZeroDensity.carlson_zeroDensity_isBigO`.

## Global Constraints

- Stack the branch on Draft PR #268 at commit `5e648509` and open a new Draft PR; do not merge.
- Add no `sorry`, `admit`, new axiom, Sharp hypothesis, Witness interface, smoothing interface, or two-height interface.
- Apply Schur once to the entire finite bucket range; do not sum isolated block energies as a substitute for cross-block control.
- Preserve the explicit alternative that returns a surviving zero with `beta < rho.re`.
- Every constant in the high-tail theorem may depend on `sigma` but must be independent of `S.card`, `T`, `Told`, `K`, and `L`.
- Keep `4 ≤ Told`, `0 ≤ a`, `1 ≤ m`, and `(2 : ℝ)^L ≤ T` explicit at the public endpoint.
- Run only one Lean process at a time in this worktree.

---

### Task 1: Exact Packet-to-Actual-Block Reindexing

**Files:**

- Create: `PrimeNumberTheorem/ExceptionalZeroDyadicCapacityReindex.lean`
- Create: `Test/ExceptionalZeroDyadicCapacityReindexContract.lean`
- Create: `Test/ExceptionalZeroDyadicCapacityReindexAxiomAudit.lean`
- Modify: `lakefile.lean`

**Interfaces:**

- Consumes: `dyadicUnitBucketIndexSet`, `dynamicComplementZeroPacket`, `actualZetaDyadicZeroBlock_eq_biUnion_zeroOrdinateUnitBucket`, and both existing actual-zeta reciprocal capacities.
- Produces:
  - `dynamicComplementDyadicLinearReciprocalCapacity`;
  - `dynamicComplementZeroPacket_eq_zeroOrdinateUnitBucket_sdiff_of_dyadic`;
  - `dynamicComplementDyadicSquareReciprocalCapacity_eq_actual`;
  - `dynamicComplementDyadicLinearReciprocalCapacity_eq_actual`.

- [ ] **Step 1: Write the failing exact-type contract**

Create the contract with the intended signatures:

```lean
import PrimeNumberTheorem.ExceptionalZeroDyadicCapacityReindex

open Complex
open scoped BigOperators

namespace PrimeNumberTheorem.VKEdgePiOverTwo

#check dynamicComplementDyadicLinearReciprocalCapacity

#check
  (dynamicComplementZeroPacket_eq_zeroOrdinateUnitBucket_sdiff_of_dyadic :
    ∀ (S : Finset ℂ) {T : ℝ} {k n : ℕ},
      n ∈ dyadicUnitBucketIndexSet k →
      (2 : ℝ) ^ (k + 1) ≤ T →
      dynamicComplementZeroPacket S T n = zeroOrdinateUnitBucket n \ S)

#check
  (dynamicComplementDyadicSquareReciprocalCapacity_eq_actual :
    ∀ (S : Finset ℂ) {T : ℝ} (k : ℕ),
      (2 : ℝ) ^ (k + 1) ≤ T →
      dynamicComplementDyadicSquareReciprocalCapacity S T k =
        actualZetaDyadicSquareReciprocalCapacityExcluding k S)

#check
  (dynamicComplementDyadicLinearReciprocalCapacity_eq_actual :
    ∀ (S : Finset ℂ) {T : ℝ} (k : ℕ),
      (2 : ℝ) ^ (k + 1) ≤ T →
      dynamicComplementDyadicLinearReciprocalCapacity S T k =
        actualZetaDyadicLinearReciprocalCapacityExcluding k S)

end PrimeNumberTheorem.VKEdgePiOverTwo
```

- [ ] **Step 2: Register and verify RED**

Add the implementation, contract, and audit module roots to `lakefile.lean`, then run:

```bash
lake -Kjobs=1 build Test.ExceptionalZeroDyadicCapacityReindexContract
```

Expected: failure because `ExceptionalZeroDyadicCapacityReindex.lean` does not exist.

- [ ] **Step 3: Prove packet equality**

Define

```lean
noncomputable def dynamicComplementDyadicLinearReciprocalCapacity
    (S : Finset ℂ) (T : ℝ) (k : ℕ) : ℝ :=
  ∑ n ∈ dyadicUnitBucketIndexSet k,
    ∑ rho ∈ dynamicComplementZeroPacket S T n,
      (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖ ^ 2
```

For packet equality, extensionalize membership. From unit-bucket membership obtain
`|rho.im| < n + 1`; from dyadic membership obtain `n + 1 ≤ 2^(k+1)`; combine with the height assumption to insert `rho` into `nontrivialZerosFinset T`. Simplify the intersection and deletion membership without changing the packet definition.

- [ ] **Step 4: Prove the two capacity equalities**

Rewrite every packet with Step 3. Use
`actualZetaDyadicZeroBlock_eq_biUnion_zeroOrdinateUnitBucket`, prove pairwise disjointness of distinct unit buckets from their half-open absolute-ordinate intervals, and apply `Finset.sum_biUnion`. Distribute deletion across the disjoint union and prove the square and linear identities separately.

- [ ] **Step 5: Verify GREEN and audit axioms**

```bash
lake -Kjobs=1 build \
  PrimeNumberTheorem.ExceptionalZeroDyadicCapacityReindex \
  Test.ExceptionalZeroDyadicCapacityReindexContract \
  Test.ExceptionalZeroDyadicCapacityReindexAxiomAudit
```

The audit prints the three equality theorems and may contain only `propext`, `Classical.choice`, and `Quot.sound`.

- [ ] **Step 6: Commit**

```bash
git add PrimeNumberTheorem/ExceptionalZeroDyadicCapacityReindex.lean \
  Test/ExceptionalZeroDyadicCapacityReindexContract.lean \
  Test/ExceptionalZeroDyadicCapacityReindexAxiomAudit.lean lakefile.lean
git commit -m "feat: reindex dyadic packet capacities"
```

### Task 2: Local Occupancy, Low-Zero Absorption, and Block Carlson Capacity

**Files:**

- Modify: `PrimeNumberTheorem/ExceptionalZeroDyadicCapacityReindex.lean`
- Modify: `Test/ExceptionalZeroDyadicCapacityReindexContract.lean`
- Modify: `Test/ExceptionalZeroDyadicCapacityReindexAxiomAudit.lean`

**Interfaces:**

- Consumes: Task 1 identities, `exists_zeroOrdinateUnitBucketMultiplicity_le_log`, `exists_actualZetaDyadicSquareReciprocalCapacityExcluding_le_log_linear`, and `directedWitness_of_not_mem_rightHigherExclusionSet`.
- Produces:
  - `exists_dynamicComplementDyadicOccupancy_le_log`;
  - `low_actualZetaDyadicZero_mem_rightHigherExclusionSet`;
  - `exists_rightHigherDyadicSquareCapacity_le_log_linear`;
  - `rightHigherActualZetaDyadicLinearCapacity_le_zeroDensityCount`.

- [ ] **Step 1: Extend the contract before implementation**

Add exact checks:

```lean
#check
  (exists_dynamicComplementDyadicOccupancy_le_log :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : Finset ℂ) (T : ℝ) (k : ℕ),
      2 ≤ k →
      (dynamicComplementDyadicOccupancy S T k : ℝ) ≤
        C * (1 + Real.log ((2 : ℝ) ^ (k + 1) + 7)))

#check low_actualZetaDyadicZero_mem_rightHigherExclusionSet
#check exists_rightHigherDyadicSquareCapacity_le_log_linear
#check rightHigherActualZetaDyadicLinearCapacity_le_zeroDensityCount
```

Temporarily comment out no declarations; run the unchanged contract and confirm it fails only on the four missing declarations.

- [ ] **Step 2: Bound occupancy by local multiplicity**

For each packet first prove the natural-number estimate with
`Finset.card_nsmul_le_sum`, exactly as in `VKEdgePiOverTwoCarlson.lean`,
and cast that estimate to `ℝ`.  Use the pointwise fact

```lean
0 < analyticOrderNatAt riemannZeta rho
```

obtained from `ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero` and unit-bucket nontrivial-zero membership. Bound packet multiplicity by the full unit-bucket multiplicity, then take the finite supremum. For `n` in block `k ≥ 2`, prove `4 ≤ n` and

```text
log(n + 7) ≤ log(2^(k+1) + 7).
```

- [ ] **Step 3: Prove low-zero absorption**

Expose a theorem whose conclusion is

```lean
rho ∈ rightHigherExclusionSet S Told sigma T
```

from:

```lean
rho ∈ actualZetaDyadicZeroBlock k
|rho.im| < 4
4 ≤ Told
(2 : ℝ)^(k+1) ≤ T.
```

Use actual-block membership to obtain `rho ∈ nontrivialZerosFinset T`; then `rho.im ≤ |rho.im| < 4 ≤ Told` selects the low-height side of the exclusion filter.

- [ ] **Step 4: Reuse the square-to-linear theorem**

Instantiate
`exists_actualZetaDyadicSquareReciprocalCapacityExcluding_le_log_linear`
with `rightHigherExclusionSet S Told sigma T` and the low-zero absorption theorem. Return the original constant `B` explicitly; do not hide a new `S`-dependent constant.

- [ ] **Step 5: Bound the linear capacity by Carlson count**

Prove the exact public inequality:

```lean
theorem rightHigherActualZetaDyadicLinearCapacity_le_zeroDensityCount
    (S : Finset ℂ) {Told sigma T : ℝ} (k : ℕ)
    (hTold : 0 ≤ Told) (hheight : (2 : ℝ) ^ (k + 1) ≤ T) :
    actualZetaDyadicLinearReciprocalCapacityExcluding k
        (rightHigherExclusionSet S Told sigma T) ≤
      (((2 : ℝ) ^ k) ^ 2)⁻¹ *
        (ZeroDensity.zeroDensityCount sigma ((2 : ℝ) ^ (k + 1)) : ℝ)
```

For each surviving zero, use `directedWitness_of_not_mem_rightHigherExclusionSet`, block membership, and `Complex.abs_im_le_norm`. Bound the weighted sum by the multiplicity sum over `zeroDensityZerosFinset sigma (2^(k+1))` using subset monotonicity.

- [ ] **Step 6: Verify and commit**

Run the Task 1 three-target build again, extend the audit with all new theorems, then commit:

```bash
git add PrimeNumberTheorem/ExceptionalZeroDyadicCapacityReindex.lean \
  Test/ExceptionalZeroDyadicCapacityReindexContract.lean \
  Test/ExceptionalZeroDyadicCapacityReindexAxiomAudit.lean
git commit -m "feat: bound right-higher dyadic capacity"
```

### Task 3: One Whole-Gram Estimate Across a Finite Dyadic Range

**Files:**

- Create: `PrimeNumberTheorem/ExceptionalZeroDyadicCarlsonSummation.lean`
- Create: `Test/ExceptionalZeroDyadicCarlsonSummationContract.lean`
- Create: `Test/ExceptionalZeroDyadicCarlsonSummationAxiomAudit.lean`
- Modify: `lakefile.lean`

**Interfaces:**

- Consumes: Tasks 1–2, `dynamicComplementGaussianMajorantEnergy_le`, and `dynamicComplementCenteredFrozenGaussianSecondMoment_le_majorant`.
- Produces:
  - `dyadicUnitBucketRange`;
  - `dyadicUnitBucketRange_eq_biUnion`;
  - `dynamicComplementDyadicRangeWeightedSquareCapacity`;
  - `dynamicComplementDyadicRangeCenteredFrozenGaussianSecondMoment_le`;
  - `rightHigherDyadicRange_fartherRight_or_centeredFrozen_le_unweighted`.

- [ ] **Step 1: Write and run the failing range contract**

The contract fixes the whole-range energy shape:

```lean
import PrimeNumberTheorem.ExceptionalZeroDyadicCarlsonSummation

open Complex
open scoped BigOperators

namespace PrimeNumberTheorem.VKEdgePiOverTwo

#check dyadicUnitBucketRange
#check dyadicUnitBucketRange_eq_biUnion

#check
  (dynamicComplementDyadicRangeCenteredFrozenGaussianSecondMoment_le :
    ∀ (S : Finset ℂ) (T beta a : ℝ) {K L : ℕ} {m : ℝ},
      K ≤ L → 1 ≤ m →
      dynamicComplementCenteredFrozenGaussianSecondMoment S T beta a
          (dyadicUnitBucketRange K L) m ≤
        MathlibAux.gaussianBucketSchurConstant *
          ∑ k ∈ Finset.Ico K L,
            (1 + (dynamicComplementDyadicOccupancy S T k : ℝ)) *
              dynamicComplementDyadicTargetSquareCapacity S T beta a k)

#check rightHigherDyadicRange_fartherRight_or_centeredFrozen_le_unweighted

end PrimeNumberTheorem.VKEdgePiOverTwo
```

Register the module roots and verify RED from the missing implementation module.

- [ ] **Step 2: Define and partition the bucket range**

```lean
def dyadicUnitBucketRange (K L : ℕ) : Finset ℕ :=
  Finset.Icc (2 ^ K) (2 ^ L - 1)
```

For `K ≤ L`, prove it equals

```lean
(Finset.Ico K L).biUnion dyadicUnitBucketIndexSet.
```

Prove pairwise disjointness from disjoint half-open natural intervals.

- [ ] **Step 3: Apply Schur once to the union**

Apply `dynamicComplementGaussianMajorantEnergy_le` with
`dyadicUnitBucketRange K L`. Rewrite its packet-mass-square sum using the
biUnion equality. Inside each block reproduce the finite Cauchy--Schwarz
step from PR #268 with the block's local occupancy and exact coefficient
square identity. Do not invoke the one-block energy theorem or sum its left
sides.

Compose with
`dynamicComplementCenteredFrozenGaussianSecondMoment_le_majorant` to obtain
the contract theorem.

- [ ] **Step 4: Preserve the farther-right branch across the range**

Split on

```lean
∃ n ∈ dyadicUnitBucketRange K L, ∃ rho,
  rho ∈ dynamicComplementZeroPacket
    (rightHigherExclusionSet S Told sigma T) T n ∧ beta < rho.re.
```

In the positive branch return `rho`, its bucket membership, Carlson-strip
membership, `Told < rho.im`, and `rho ∉ S`. In the negative branch prove
`rho.re ≤ beta` for every range packet and remove target weights using
`0 ≤ a`. The right side is the sum over `k ∈ Ico K L` of local occupancy
times unweighted packet square capacity.

- [ ] **Step 5: Verify the two-block cross-term contract**

Add an exact check at `K = 2`, `L = 4` whose left side remains

```lean
dynamicComplementCenteredFrozenGaussianSecondMoment ...
  (dyadicUnitBucketRange 2 4) m
```

rather than a sum of two energy objects. Build implementation, contract, and
axiom audit serially.

- [ ] **Step 6: Commit**

```bash
git add PrimeNumberTheorem/ExceptionalZeroDyadicCarlsonSummation.lean \
  Test/ExceptionalZeroDyadicCarlsonSummationContract.lean \
  Test/ExceptionalZeroDyadicCarlsonSummationAxiomAudit.lean lakefile.lean
git commit -m "feat: aggregate dyadic whole-Gram energy"
```

### Task 4: Carlson Polynomial-Geometric Majorant

**Files:**

- Modify: `PrimeNumberTheorem/ExceptionalZeroDyadicCarlsonSummation.lean`
- Modify: `Test/ExceptionalZeroDyadicCarlsonSummationContract.lean`
- Modify: `Test/ExceptionalZeroDyadicCarlsonSummationAxiomAudit.lean`

**Interfaces:**

- Consumes: Tasks 2–3 and `CarlsonZeroDensity.carlson_zeroDensity_isBigO`.
- Produces:
  - `carlsonDyadicExponent`;
  - `carlsonDyadicEnergyRatio`;
  - `carlsonDyadicExponent_lt_one`;
  - `summable_carlsonDyadicEnergyMajorant`;
  - `exists_rightHigherDyadicCapacity_le_carlsonMajorant`.

- [ ] **Step 1: Add the failing majorant contract**

Fix the definitions and endpoint:

```lean
noncomputable def carlsonDyadicExponent (sigma : ℝ) : ℝ :=
  4 * sigma * (1 - sigma)

noncomputable def carlsonDyadicEnergyRatio (sigma : ℝ) : ℝ :=
  (2 : ℝ) ^ (carlsonDyadicExponent sigma - 2)

noncomputable def carlsonDyadicEnergyMajorant (sigma : ℝ) (k : ℕ) : ℝ :=
  ((k + 1 : ℕ) : ℝ) ^ 6 * carlsonDyadicEnergyRatio sigma ^ k

#check carlsonDyadicExponent_lt_one
#check summable_carlsonDyadicEnergyMajorant
#check exists_rightHigherDyadicCapacity_le_carlsonMajorant
```

Run the contract and confirm failure on the missing declarations.

- [ ] **Step 2: Prove the ratio lies strictly between zero and one**

From `1/2 < sigma < 1`, prove

```text
4*sigma*(1-sigma) < 1
```

by completing the square or `nlinarith [sq_pos (sigma - 1/2)]`. Then use
`Real.rpow_pos_of_pos` and `Real.rpow_lt_one_of_one_lt_of_neg` at base `2`
to prove `0 < carlsonDyadicEnergyRatio sigma < 1`.

- [ ] **Step 3: Prove summability of the majorant**

Use the Mathlib polynomial-times-geometric summability lemma if its exact
signature fits. Otherwise apply the ratio test to
`(k+1)^6 * r^k`, using `0 < r < 1` and the fact that
`((k+2)/(k+1))^6 → 1`. Keep this proof in the summation module; do not add a
new general-purpose MathlibAux interface unless the proof is reused twice.

- [ ] **Step 4: Specialize Carlson along dyadic heights**

Use `carlson_zeroDensity_isBigO hσ hσ1`. Compose its eventual bound with
the map `k ↦ (2 : ℝ)^(k+1)`, which tends to `atTop`. Convert
`log(2^(k+1))` exactly to `(k+1)*log 2`, absorb the fixed shift and the two
additional logarithmic factors from Task 2, and rewrite

```text
2^(-2k) * 2^(q*(k+1))
```

as a fixed sigma-dependent constant times
`carlsonDyadicEnergyRatio sigma ^ k`.

Return an explicit existential shape:

```lean
∃ A : ℝ, 0 ≤ A ∧ ∃ K0 : ℕ, 2 ≤ K0 ∧
  ∀ (S : Finset ℂ) (Told T : ℝ) (k : ℕ),
    4 ≤ Told → K0 ≤ k → (2 : ℝ)^(k+1) ≤ T →
    (1 + (dynamicComplementDyadicOccupancy
      (rightHigherExclusionSet S Told sigma T) T k : ℝ)) *
      dynamicComplementDyadicSquareReciprocalCapacity
        (rightHigherExclusionSet S Told sigma T) T k ≤
      A * carlsonDyadicEnergyMajorant sigma k
```

- [ ] **Step 5: Verify and commit**

Build the summation implementation, contract, and audit. Confirm the theorem
quantifies `A` and `K0` before `S`, `T`, and `Told`. Commit:

```bash
git add PrimeNumberTheorem/ExceptionalZeroDyadicCarlsonSummation.lean \
  Test/ExceptionalZeroDyadicCarlsonSummationContract.lean \
  Test/ExceptionalZeroDyadicCarlsonSummationAxiomAudit.lean
git commit -m "feat: derive summable Carlson block majorant"
```

### Task 5: Uniform S-Relative High-Tail Dichotomy

**Files:**

- Modify: `PrimeNumberTheorem/ExceptionalZeroDyadicCarlsonSummation.lean`
- Modify: `Test/ExceptionalZeroDyadicCarlsonSummationContract.lean`
- Modify: `Test/ExceptionalZeroDyadicCarlsonSummationAxiomAudit.lean`

**Interfaces:**

- Consumes: Tasks 3–4 and summable-series tail smallness.
- Produces:
  - `rightHigherDyadicRangeCenteredFrozenEnergy` if a short public alias is needed by the contract;
  - `eventually_rightHigherDyadicRange_fartherRight_or_energy_lt`.

- [ ] **Step 1: Lock the final endpoint in RED**

Add an exact-type contract of the following shape:

```lean
#check
  (eventually_rightHigherDyadicRange_fartherRight_or_energy_lt :
    ∀ {sigma beta eta : ℝ},
      1 / 2 < sigma → sigma < 1 → sigma < beta → 0 < eta →
      ∃ Keta : ℕ, 2 ≤ Keta ∧
        ∀ (S : Finset ℂ) {Told T a : ℝ} {K L : ℕ} {m : ℝ},
          4 ≤ Told → 0 ≤ a → 1 ≤ m →
          Keta ≤ K → K < L → (2 : ℝ)^L ≤ T →
          (∃ n ∈ dyadicUnitBucketRange K L, ∃ rho,
            rho ∈ dynamicComplementZeroPacket
                (rightHigherExclusionSet S Told sigma T) T n ∧
              beta < rho.re ∧
              rho ∈ ZeroDensity.zeroDensityZerosFinset sigma T ∧
              Told < rho.im ∧ rho ∉ S) ∨
            dynamicComplementCenteredFrozenGaussianSecondMoment
                (rightHigherExclusionSet S Told sigma T) T beta a
                (dyadicUnitBucketRange K L) m < eta)
```

Run the contract and verify failure because the endpoint is missing.

- [ ] **Step 2: Extract a uniform summable-series tail cutoff**

From `summable_carlsonDyadicEnergyMajorant`, use
`summable_iff_vanishing_norm` or the repository's existing finite-tail
pattern to choose `Keta` such that every finite set disjoint from
`Finset.range Keta` has majorant sum less than

```text
eta / gaussianBucketSchurConstant.
```

Absorb the existential coefficient `A` from Task 4 before choosing the
cutoff. Handle `A = 0` separately or use a positive denominator
`gaussianBucketSchurConstant * max A 1`.

- [ ] **Step 3: Combine the range dichotomy and block majorant**

Apply `rightHigherDyadicRange_fartherRight_or_centeredFrozen_le_unweighted`.
Return its farther-right witness unchanged. In the no-farther-right branch:

1. rewrite every packet square capacity to the actual block using
   `(2 : ℝ)^L ≤ T` and `k < L`;
2. apply the Task 4 block majorant for each `k ∈ Ico K L`;
3. sum by monotonicity;
4. apply the selected finite-tail cutoff;
5. multiply by the positive Gaussian Schur constant.

The final strict inequality must remain uniform in `S`, `T`, `Told`, and
`L`.

- [ ] **Step 4: Run final verification and scans**

Run exactly one Lean process:

```bash
lake -Kjobs=1 build \
  PrimeNumberTheorem.ExceptionalZeroDyadicCapacityReindex \
  Test.ExceptionalZeroDyadicCapacityReindexContract \
  Test.ExceptionalZeroDyadicCapacityReindexAxiomAudit \
  PrimeNumberTheorem.ExceptionalZeroDyadicCarlsonSummation \
  Test.ExceptionalZeroDyadicCarlsonSummationContract \
  Test.ExceptionalZeroDyadicCarlsonSummationAxiomAudit
```

Then run:

```bash
git diff --check 5e648509..HEAD
rg -n '\b(sorry|admit)\b|^\s*(axiom|constant)\b' \
  PrimeNumberTheorem/ExceptionalZeroDyadicCapacityReindex.lean \
  PrimeNumberTheorem/ExceptionalZeroDyadicCarlsonSummation.lean \
  Test/ExceptionalZeroDyadicCapacityReindexContract.lean \
  Test/ExceptionalZeroDyadicCapacityReindexAxiomAudit.lean \
  Test/ExceptionalZeroDyadicCarlsonSummationContract.lean \
  Test/ExceptionalZeroDyadicCarlsonSummationAxiomAudit.lean
```

Expected: focused build succeeds; only foundational permitted axioms appear;
the source scan returns no declaration hit.

- [ ] **Step 5: Commit and publish the stacked Draft PR**

```bash
git add PrimeNumberTheorem/ExceptionalZeroDyadicCarlsonSummation.lean \
  Test/ExceptionalZeroDyadicCarlsonSummationContract.lean \
  Test/ExceptionalZeroDyadicCarlsonSummationAxiomAudit.lean
git commit -m "feat: prove uniform dyadic Carlson energy tail"
git push -u origin codex/exceptional-zero-dyadic-carlson-summation
```

Open a Draft PR with base
`codex/exceptional-zero-target-dyadic-gram-schur` and state explicitly that
the result completes only centered-frozen E2. Preserve the worktree for
review fixes and do not merge.
