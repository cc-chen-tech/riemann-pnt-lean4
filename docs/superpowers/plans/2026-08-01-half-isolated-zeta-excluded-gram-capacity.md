# Excluded Dyadic Zeta Gram Capacity Bridge Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Instantiate the actual dyadic drifting Gaussian Gram/Schur theorem on the zeta block after deleting an arbitrary finite set `S`, then connect its occupancy and detect-or-count conclusions to PR #274's full four-Carlson-capacity bound.

**Architecture:** Add one narrow source module stacked on PR #274.  Its finite index set is exactly `zetaRightDyadicPairsExcluding beta k S`; local private lemmas restrict the existing genuine-zeta mass, drift, and frequency-gap facts to that set.  Public theorems expose an occupancy upper bound, a quantitative excluded-cluster alternative, and thin four-capacity compositions without changing any upstream module.

**Tech Stack:** Lean 4, Mathlib finite sums and `Finset`, `MathlibAux.dyadicDriftingGaussianGram`, the actual-zeta dyadic adapter, PR #274's full excluded mass, and actual Carlson reciprocal-square capacities.

## Global Constraints

- Work only in `/Users/luicy/AI/Riemann/riemann-pnt-lean4/.worktrees/half-isolated-zeta-excluded-gram-capacity-bridge` on branch `codex/half-isolated-zeta-excluded-gram-capacity-bridge`.
- Stack on PR #274 commit `be130196e84e9180c8ab78991beb6e3c07d583c4`; do not modify or reopen PR #274.
- Do not modify `HalfIsolatedZetaDyadicAdapter.lean`, Sharp, Pintz-Carlson, or their worktrees.
- Do not add a class, structure, abstract descendant tree, replacement capacity object, or conjugation-closure assumption on `S`.
- Use the actual excluded finite set `zetaRightDyadicPairsExcluding beta k S` in both the Gram and square-mass terms.
- Retain `MathlibAux.gaussianBucketSchurConstant`, `occupancy + 1`, `(x ^ (1 - beta)) ^ 2`, and all four PR #274 capacity terms exactly.
- At most four Lean threads may run; never run two builds that write the same target concurrently.
- Do not claim an unconditional occupancy estimate, repeatable Sharp energy, two-height transfer, multi-window growth, Carlson contradiction, exclusion of off-line zeros, or RH.

---

## File Structure

- Create `PrimeNumberTheorem/HalfIsolatedZetaExcludedDyadicGramCapacityBridge.lean`: excluded Gram definition, restricted zeta lemmas, occupancy theorem, excluded cluster, detect-or-count, and four-capacity compositions.
- Create `PrimeNumberTheorem/HalfIsolatedZetaExcludedDyadicGramCapacityBridge/Contract.lean`: public signature checks only.
- Create `PrimeNumberTheorem/HalfIsolatedZetaExcludedDyadicGramCapacityBridge/AxiomAudit.lean`: `#print axioms` for every exported theorem.
- Do not modify existing source modules; consume PR #274 and the actual-zeta adapter as stable interfaces.

---

### Task 1: Excluded Actual-Zeta Gram and Occupancy Bound

**Files:**
- Create: `PrimeNumberTheorem/HalfIsolatedZetaExcludedDyadicGramCapacityBridge.lean`
- Create: `PrimeNumberTheorem/HalfIsolatedZetaExcludedDyadicGramCapacityBridge/Contract.lean`

**Interfaces:**
- Consumes: `zetaRightDyadicPairsExcluding`, `zetaRightDyadicFullMassSquareExcluding`, `zetaDyadicBaseMass`, `zetaDyadicBackwardDrift`, `mem_zetaRightDyadicBucketPairs`, `mem_zetaDyadicBucketPairs`, and `MathlibAux.dyadicDriftingGaussianGram_le_occupancy_mul_sum_sq`.
- Produces: `zetaRightDyadicGaussianGramExcluding` and `zetaRightDyadicGaussianGramExcluding_le_occupancy_mul_fullMass`.

- [ ] **Step 1: Write the failing Contract first**

Create the Contract with these exact checks:

```lean
import PrimeNumberTheorem.HalfIsolatedZetaExcludedDyadicGramCapacityBridge

#check PrimeNumberTheorem.VKEdgePiOverTwo.zetaRightDyadicGaussianGramExcluding
#check PrimeNumberTheorem.VKEdgePiOverTwo.zetaRightDyadicGaussianGramExcluding_le_occupancy_mul_fullMass
```

- [ ] **Step 2: Run the Contract and verify the expected missing-module failure**

Run:

```bash
LEAN_NUM_THREADS=4 lake build \
  PrimeNumberTheorem.HalfIsolatedZetaExcludedDyadicGramCapacityBridge.Contract
```

Expected: failure because `HalfIsolatedZetaExcludedDyadicGramCapacityBridge` or its declarations do not yet exist.  Stop if the failure is instead in an existing protected module.

- [ ] **Step 3: Define the actual excluded Gram**

Create the source with imports and definition:

```lean
import PrimeNumberTheorem.HalfIsolatedZetaFullDyadicCapacityBridge
import PrimeNumberTheorem.HalfIsolatedZetaDyadicAdapter

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

open Complex
open scoped BigOperators

noncomputable section

def zetaRightDyadicGaussianGramExcluding
    (x beta : ℝ) (k : ℕ) (S : Finset ℂ) (t m : ℝ) : ℝ :=
  MathlibAux.dyadicDriftingGaussianGram
    (zetaRightDyadicPairsExcluding beta k S)
    (zetaDyadicBaseMass x beta)
    (zetaDyadicBackwardDrift beta)
    (fun p => p.2.im) t m
```

- [ ] **Step 4: Prove mass nonnegativity locally without changing the adapter**

Add a private theorem:

```lean
private theorem zetaDyadicBaseMass_nonneg_excluding
    {x beta : ℝ} (hx : 0 < x) (p : ℕ × ℂ) :
    0 ≤ zetaDyadicBaseMass x beta p := by
  exact mul_nonneg
    (div_nonneg (Nat.cast_nonneg _) (norm_nonneg p.2))
    (Real.rpow_nonneg hx.le _)
```

- [ ] **Step 5: Restrict the genuine-zeta frequency gap to the excluded set**

Add a private theorem.  Strip the exclusion filter first, then reproduce the adapter's unit-bucket argument:

```lean
private theorem zetaRightDyadic_frequency_gap_excluding
    {beta : ℝ} {k : ℕ} {S : Finset ℂ} {p q : ℕ × ℂ}
    (hp : p ∈ zetaRightDyadicPairsExcluding beta k S)
    (hq : q ∈ zetaRightDyadicPairsExcluding beta k S) :
    (((p.1).dist q.1 - 1 : ℕ) : ℝ) ≤ |p.2.im - q.2.im| := by
  have hpRight := (Finset.mem_filter.mp hp).1
  have hqRight := (Finset.mem_filter.mp hq).1
  have hpBucket := (mem_zetaDyadicBucketPairs.mp
    (mem_zetaRightDyadicBucketPairs.mp hpRight).1).2
  have hqBucket := (mem_zetaDyadicBucketPairs.mp
    (mem_zetaRightDyadicBucketPairs.mp hqRight).1).2
  have hpBounds := (Finset.mem_filter.mp hpBucket).2
  have hqBounds := (Finset.mem_filter.mp hqBucket).2
  exact (MathlibAux.natDist_sub_one_le_abs_sub_of_mem_unit
    hpBounds.1 hpBounds.2 hqBounds.1 hqBounds.2).trans
      (abs_abs_sub_abs_le_abs_sub p.2.im q.2.im)
```

- [ ] **Step 6: Prove the excluded Occupancy-Gram theorem**

Add the public theorem:

```lean
theorem zetaRightDyadicGaussianGramExcluding_le_occupancy_mul_fullMass
    {x beta t m : ℝ} (k occupancy : ℕ) (S : Finset ℂ)
    (hx : 0 < x) (ht : 0 ≤ t) (hm : 1 ≤ m)
    (hoccupancy : ∀ n ∈
      (zetaRightDyadicPairsExcluding beta k S).image Prod.fst,
      ((zetaRightDyadicPairsExcluding beta k S).filter
        fun p => p.1 = n).card ≤ occupancy + 1) :
    zetaRightDyadicGaussianGramExcluding x beta k S t m ≤
      MathlibAux.gaussianBucketSchurConstant *
        ((occupancy + 1 : ℕ) : ℝ) *
          zetaRightDyadicFullMassSquareExcluding x beta k S := by
  unfold zetaRightDyadicGaussianGramExcluding
    zetaRightDyadicFullMassSquareExcluding
  apply MathlibAux.dyadicDriftingGaussianGram_le_occupancy_mul_sum_sq
    (bucket := Prod.fst) (occupancy := occupancy)
  · exact ht
  · exact hm
  · intro p _hp
    exact zetaDyadicBaseMass_nonneg_excluding hx p
  · intro p hp
    exact sub_nonpos.mpr
      (mem_zetaRightDyadicBucketPairs.mp (Finset.mem_filter.mp hp).1).2
  · intro p hp q hq
    exact zetaRightDyadic_frequency_gap_excluding hp hq
  · exact hoccupancy
```

- [ ] **Step 7: Run focused source and Contract builds**

Run serially:

```bash
LEAN_NUM_THREADS=4 lake build \
  PrimeNumberTheorem.HalfIsolatedZetaExcludedDyadicGramCapacityBridge
LEAN_NUM_THREADS=4 lake build \
  PrimeNumberTheorem.HalfIsolatedZetaExcludedDyadicGramCapacityBridge.Contract
```

Expected: both targets pass, and Contract prints the exact excluded set in both the occupancy hypothesis and the full-mass conclusion.

- [ ] **Step 8: Commit the Occupancy-Gram checkpoint**

```bash
git add \
  PrimeNumberTheorem/HalfIsolatedZetaExcludedDyadicGramCapacityBridge.lean \
  PrimeNumberTheorem/HalfIsolatedZetaExcludedDyadicGramCapacityBridge/Contract.lean
git commit -m "feat: bound excluded dyadic zeta Gram by full mass"
```

---

### Task 2: Excluded Detect-or-Count and Four-Capacity Composition

**Files:**
- Modify: `PrimeNumberTheorem/HalfIsolatedZetaExcludedDyadicGramCapacityBridge.lean`
- Modify: `PrimeNumberTheorem/HalfIsolatedZetaExcludedDyadicGramCapacityBridge/Contract.lean`

**Interfaces:**
- Consumes: Task 1's excluded Gram theorem, `zetaDyadicBucketPairs_snd_inj`, `MathlibAux.dyadicDriftingGaussianGram_le_or_quantitativeCluster`, and PR #274's `zetaRightDyadicFullMassSquareExcluding_le_fourCarlsonCapacities`.
- Produces: `zetaRightDyadicUnitClusterExcluding`, `card_zetaRightDyadicUnitClusterExcluding`, `zetaRightDyadicGaussianGramExcluding_le_or_quantitativeCluster`, `zetaRightDyadicGaussianGramExcluding_le_fourCarlsonCapacities`, and `zetaRightDyadicGaussianGramExcluding_le_fourCarlsonCapacities_or_quantitativeCluster`.

- [ ] **Step 1: Extend Contract checks before adding declarations**

Append:

```lean
#check PrimeNumberTheorem.VKEdgePiOverTwo.zetaRightDyadicUnitClusterExcluding
#check PrimeNumberTheorem.VKEdgePiOverTwo.card_zetaRightDyadicUnitClusterExcluding
#check PrimeNumberTheorem.VKEdgePiOverTwo.zetaRightDyadicGaussianGramExcluding_le_or_quantitativeCluster
#check PrimeNumberTheorem.VKEdgePiOverTwo.zetaRightDyadicGaussianGramExcluding_le_fourCarlsonCapacities
#check PrimeNumberTheorem.VKEdgePiOverTwo.zetaRightDyadicGaussianGramExcluding_le_fourCarlsonCapacities_or_quantitativeCluster
```

- [ ] **Step 2: Run Contract and verify missing-declaration failure**

```bash
LEAN_NUM_THREADS=4 lake build \
  PrimeNumberTheorem.HalfIsolatedZetaExcludedDyadicGramCapacityBridge.Contract
```

Expected: failure naming the new Task 2 declarations only.

- [ ] **Step 3: Define the excluded unit cluster and prove distinct-zero cardinality**

```lean
def zetaRightDyadicUnitClusterExcluding
    (beta : ℝ) (k : ℕ) (S : Finset ℂ) (n : ℕ) : Finset ℂ :=
  ((zetaRightDyadicPairsExcluding beta k S).filter
    fun p => p.1 = n).image Prod.snd

theorem card_zetaRightDyadicUnitClusterExcluding
    (beta : ℝ) (k : ℕ) (S : Finset ℂ) (n : ℕ) :
    (zetaRightDyadicUnitClusterExcluding beta k S n).card =
      ((zetaRightDyadicPairsExcluding beta k S).filter
        fun p => p.1 = n).card := by
  apply Finset.card_image_iff.mpr
  intro p hp q hq hsnd
  exact zetaDyadicBucketPairs_snd_inj k
    (mem_zetaRightDyadicBucketPairs.mp
      (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
    (mem_zetaRightDyadicBucketPairs.mp
      (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).1
    hsnd
```

- [ ] **Step 4: Prove the excluded detect-or-count theorem**

Instantiate the abstract dichotomy with the same local mass and frequency lemmas as Task 1:

```lean
theorem zetaRightDyadicGaussianGramExcluding_le_or_quantitativeCluster
    {x beta t m : ℝ} (k occupancy : ℕ) (S : Finset ℂ)
    (hx : 0 < x) (ht : 0 ≤ t) (hm : 1 ≤ m) :
    zetaRightDyadicGaussianGramExcluding x beta k S t m ≤
        MathlibAux.gaussianBucketSchurConstant *
          ((occupancy + 1 : ℕ) : ℝ) *
            zetaRightDyadicFullMassSquareExcluding x beta k S ∨
      ∃ n ∈ (zetaRightDyadicPairsExcluding beta k S).image Prod.fst,
        occupancy + 1 <
          (zetaRightDyadicUnitClusterExcluding beta k S n).card := by
  have hresult := MathlibAux.dyadicDriftingGaussianGram_le_or_quantitativeCluster
    (zetaRightDyadicPairsExcluding beta k S)
    (zetaDyadicBaseMass x beta)
    (zetaDyadicBackwardDrift beta)
    (fun p => p.2.im) Prod.fst occupancy ht hm
    (fun p _hp => zetaDyadicBaseMass_nonneg_excluding hx p)
    (fun p hp => sub_nonpos.mpr
      (mem_zetaRightDyadicBucketPairs.mp (Finset.mem_filter.mp hp).1).2)
    (fun p hp q hq => zetaRightDyadic_frequency_gap_excluding hp hq)
  rcases hresult with henergy | ⟨n, hn, hcard⟩
  · exact Or.inl (by simpa [zetaRightDyadicGaussianGramExcluding,
      zetaRightDyadicFullMassSquareExcluding] using henergy)
  · exact Or.inr ⟨n, hn, by
      rwa [card_zetaRightDyadicUnitClusterExcluding]⟩
```

- [ ] **Step 5: Prove the conditional four-capacity Gram upper bound**

Add a theorem with assumptions
`hx : 1 ≤ x`, `ht : 0 ≤ t`, `hm : 1 ≤ m`, `hk : 1 ≤ k`,
`hsigma : sigma < beta`, and the same excluded occupancy hypothesis as Task 1.
Its conclusion must be exactly:

```lean
zetaRightDyadicGaussianGramExcluding x beta k S t m ≤
  MathlibAux.gaussianBucketSchurConstant *
    ((occupancy + 1 : ℕ) : ℝ) *
      ((x ^ (1 - beta)) ^ 2 *
        ((actualCarlsonDyadicStripSquareReciprocalCapacityExcluding
              sigma 1 (k - 1) S +
            actualCarlsonDyadicStripSquareReciprocalCapacityExcluding
              sigma 1 k S) +
          (actualCarlsonDyadicStripSquareReciprocalCapacityExcluding
              sigma 1 (k - 1) (conjugateFinset S) +
            actualCarlsonDyadicStripSquareReciprocalCapacityExcluding
              sigma 1 k (conjugateFinset S))))
```

Proof structure:

```lean
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hgram :=
    zetaRightDyadicGaussianGramExcluding_le_occupancy_mul_fullMass
      k occupancy S hxpos ht hm hoccupancy
  have hcapacity :=
    zetaRightDyadicFullMassSquareExcluding_le_fourCarlsonCapacities
      (S := S) hx hk hsigma
  exact hgram.trans <| mul_le_mul_of_nonneg_left hcapacity
    (mul_nonneg MathlibAux.gaussianBucketSchurConstant_pos.le (by positivity))
```

- [ ] **Step 6: Prove detect-or-four-capacity without an occupancy assumption**

State the same disjunction as Step 4, but replace its first right-hand side by
the exact four-capacity expression from Step 5.  Use Step 4, then compose its
energy branch with PR #274's full-mass capacity bound by the same nonnegative
multiplier.  Preserve the quantitative cluster branch unchanged.

- [ ] **Step 7: Run focused source and Contract builds**

```bash
LEAN_NUM_THREADS=4 lake build \
  PrimeNumberTheorem.HalfIsolatedZetaExcludedDyadicGramCapacityBridge
LEAN_NUM_THREADS=4 lake build \
  PrimeNumberTheorem.HalfIsolatedZetaExcludedDyadicGramCapacityBridge.Contract
```

Expected: both pass.  Contract must show the exact excluded set, all four
capacity terms, and a cluster cardinality rather than mere `Nonempty`.

- [ ] **Step 8: Commit the detect-or-count checkpoint**

```bash
git add \
  PrimeNumberTheorem/HalfIsolatedZetaExcludedDyadicGramCapacityBridge.lean \
  PrimeNumberTheorem/HalfIsolatedZetaExcludedDyadicGramCapacityBridge/Contract.lean
git commit -m "feat: connect excluded zeta Gram to Carlson or clustering"
```

---

### Task 3: Axiom Audit and Stacked Draft PR

**Files:**
- Create: `PrimeNumberTheorem/HalfIsolatedZetaExcludedDyadicGramCapacityBridge/AxiomAudit.lean`
- Verify: `PrimeNumberTheorem/HalfIsolatedZetaExcludedDyadicGramCapacityBridge.lean`
- Verify: `PrimeNumberTheorem/HalfIsolatedZetaExcludedDyadicGramCapacityBridge/Contract.lean`

**Interfaces:**
- Consumes: every public theorem from Tasks 1 and 2.
- Produces: reproducible focused build evidence and one narrow Draft PR stacked on PR #274.

- [ ] **Step 1: Add the axiom-audit module**

```lean
import PrimeNumberTheorem.HalfIsolatedZetaExcludedDyadicGramCapacityBridge

open PrimeNumberTheorem
open PrimeNumberTheorem.VKEdgePiOverTwo

#print axioms card_zetaRightDyadicUnitClusterExcluding
#print axioms zetaRightDyadicGaussianGramExcluding_le_occupancy_mul_fullMass
#print axioms zetaRightDyadicGaussianGramExcluding_le_or_quantitativeCluster
#print axioms zetaRightDyadicGaussianGramExcluding_le_fourCarlsonCapacities
#print axioms zetaRightDyadicGaussianGramExcluding_le_fourCarlsonCapacities_or_quantitativeCluster
```

- [ ] **Step 2: Run all focused targets serially**

```bash
LEAN_NUM_THREADS=4 lake build \
  PrimeNumberTheorem.HalfIsolatedZetaExcludedDyadicGramCapacityBridge
LEAN_NUM_THREADS=4 lake build \
  PrimeNumberTheorem.HalfIsolatedZetaExcludedDyadicGramCapacityBridge.Contract
LEAN_NUM_THREADS=4 lake build \
  PrimeNumberTheorem.HalfIsolatedZetaExcludedDyadicGramCapacityBridge.AxiomAudit
```

Expected: all three exit successfully.  Do not substitute a full repository build.

- [ ] **Step 3: Inspect exact axioms**

Run:

```bash
LEAN_NUM_THREADS=1 lake env lean \
  PrimeNumberTheorem/HalfIsolatedZetaExcludedDyadicGramCapacityBridge/AxiomAudit.lean
```

Expected: each theorem uses only standard logical axioms such as `propext`,
`Classical.choice`, and `Quot.sound`.

- [ ] **Step 4: Run scoped static checks**

```bash
git diff --check
! rg -n '\b(sorry|admit|axiom)\b' \
  PrimeNumberTheorem/HalfIsolatedZetaExcludedDyadicGramCapacityBridge.lean \
  PrimeNumberTheorem/HalfIsolatedZetaExcludedDyadicGramCapacityBridge/Contract.lean \
  PrimeNumberTheorem/HalfIsolatedZetaExcludedDyadicGramCapacityBridge/AxiomAudit.lean
git status --short --branch
```

Expected: no placeholders or added axiom declaration, no whitespace errors, and
only the three intended Lean files plus the committed design and plan documents.

- [ ] **Step 5: Commit the audit checkpoint**

```bash
git add PrimeNumberTheorem/HalfIsolatedZetaExcludedDyadicGramCapacityBridge/AxiomAudit.lean
git commit -m "audit: certify excluded dyadic zeta Gram capacity bridge"
```

- [ ] **Step 6: Push and create the stacked Draft PR**

```bash
git push -u origin codex/half-isolated-zeta-excluded-gram-capacity-bridge
```

Create a Draft PR with:

- base: `codex/half-isolated-zeta-full-dyadic-capacity-bridge`;
- head: `codex/half-isolated-zeta-excluded-gram-capacity-bridge`;
- claim: excluded actual-zeta Gram/Schur upper bound, four-capacity composition,
  and quantitative excluded-cluster alternative;
- explicit exclusions: unconditional occupancy, repeatable Sharp energy,
  two-height tail transfer, multi-window accumulation, Carlson contradiction,
  off-line-zero exclusion, and RH.
