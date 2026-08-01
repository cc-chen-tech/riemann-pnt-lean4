# Full Dyadic Zeta Capacity Bridge Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Transfer the negative-ordinate excluded zeta mass through exact conjugation of the exclusion set, then combine it with PR #271's positive theorem into a complete dyadic four-capacity upper bound.

**Architecture:** Work in one new Lean source module stacked on PR #271.  Represent exclusion-set conjugation by `Finset.image conj`, map negative bucket pairs to positive bucket pairs without changing bucket labels, and reuse the positive two-shell Carlson theorem with `conjugateFinset S`.  Split the full mass exactly by the sign of the ordinate after proving the dyadic block contains no zero ordinate.

**Tech Stack:** Lean 4, Mathlib finite sums and `Finset.image`, repository zeta-zero objects, PR #271 positive capacity bridge, PR #258 actual Carlson reciprocal-square capacity.

## Global Constraints

- Do not assume `S` is closed under complex conjugation.
- Do not modify PR #271, PR #259, PR #256, Sharp, or Pintz-Carlson worktrees.
- Do not add a class, structure, abstract descendant tree, or replacement capacity object.
- Retain actual analytic multiplicity and the exact `(x ^ (1 - beta)) ^ 2` normalization.
- Treat only conjugation transfer and complete dyadic mass aggregation.
- Do not claim an Occupancy estimate, Sharp lower bound, Carlson contradiction, or RH consequence.
- Use at most four Lean build threads and never run two builds that write the same target concurrently.

---

## File Structure

- Create `PrimeNumberTheorem/HalfIsolatedZetaFullDyadicCapacityBridge.lean`: all conjugation, negative-mass, exact split, and full-capacity theorems.
- Create `PrimeNumberTheorem/HalfIsolatedZetaFullDyadicCapacityBridge/Contract.lean`: public theorem signature checks only.
- Create `PrimeNumberTheorem/HalfIsolatedZetaFullDyadicCapacityBridge/AxiomAudit.lean`: `#print axioms` for each exported theorem.
- Do not modify `PrimeNumberTheorem/HalfIsolatedZetaDyadicCapacityBridge.lean`; consume it as the stable PR #271 interface.

---

### Task 1: Exact conjugated exclusion set and negative-pair transfer

**Files:**
- Create: `PrimeNumberTheorem/HalfIsolatedZetaFullDyadicCapacityBridge.lean`
- Create: `PrimeNumberTheorem/HalfIsolatedZetaFullDyadicCapacityBridge/Contract.lean`

**Interfaces:**
- Consumes: `zetaRightDyadicBucketPairs`, `zetaDyadicBaseMass`, `zetaRightDyadicPositiveMassSquareExcluding`, `RiemannVonMangoldt.isNontrivialZero_conj`, and `RiemannVonMangoldt.analyticOrderNatAt_riemannZeta_conj_of_nontrivialZero`.
- Produces: `conjugateFinset`, `zetaRightDyadicNegativePairsExcluding`, `zetaRightDyadicNegativeMassSquareExcluding`, `not_mem_conjugateFinset_iff`, and `zetaRightDyadicNegativeMassSquareExcluding_eq_positive_conjugateFinset`.

- [ ] **Step 1: Write the contract checks before the source declarations**

```lean
import PrimeNumberTheorem.HalfIsolatedZetaFullDyadicCapacityBridge

namespace PrimeNumberTheorem.VKEdgePiOverTwo

#check conjugateFinset
#check not_mem_conjugateFinset_iff
#check zetaRightDyadicNegativeMassSquareExcluding
#check zetaRightDyadicNegativeMassSquareExcluding_eq_positive_conjugateFinset

end PrimeNumberTheorem.VKEdgePiOverTwo
```

- [ ] **Step 2: Run the contract target and confirm it fails because the new source module does not exist**

Run:

```bash
LEAN_NUM_THREADS=1 lake build PrimeNumberTheorem.HalfIsolatedZetaFullDyadicCapacityBridge.Contract
```

Expected: failure naming the missing module or missing declarations, not a failure in an existing protected module.

- [ ] **Step 3: Define exact exclusion-set conjugation and prove membership equivalence**

```lean
noncomputable def conjugateFinset (S : Finset ℂ) : Finset ℂ :=
  S.image conj

theorem mem_conjugateFinset_iff {S : Finset ℂ} {rho : ℂ} :
    rho ∈ conjugateFinset S ↔ conj rho ∈ S := by
  simp [conjugateFinset]

theorem not_mem_conjugateFinset_iff {S : Finset ℂ} {rho : ℂ} :
    rho ∉ conjugateFinset S ↔ conj rho ∉ S := by
  simp [mem_conjugateFinset_iff]
```

If simplification chooses the opposite orientation, prove it by `Finset.mem_image` and apply conjugation twice; do not add a closure hypothesis on `S`.

- [ ] **Step 4: Define negative pairs and negative square mass**

```lean
noncomputable def zetaRightDyadicNegativePairsExcluding
    (beta : ℝ) (k : ℕ) (S : Finset ℂ) : Finset (ℕ × ℂ) :=
  (zetaRightDyadicBucketPairs beta k).filter fun p =>
    p.2.im < 0 ∧ p.2 ∉ S

noncomputable def zetaRightDyadicNegativeMassSquareExcluding
    (x beta : ℝ) (k : ℕ) (S : Finset ℂ) : ℝ :=
  ∑ p ∈ zetaRightDyadicNegativePairsExcluding beta k S,
    zetaDyadicBaseMass x beta p ^ 2
```

- [ ] **Step 5: Prove the bucket-pair conjugation bijection**

Use the map

```lean
fun p : ℕ × ℂ => (p.1, conj p.2)
```

and prove it bijects

```lean
zetaRightDyadicNegativePairsExcluding beta k S
```

with

```lean
zetaRightDyadicPositivePairsExcluding beta k (conjugateFinset S).
```

For membership, retain the same bucket label and establish:

```lean
|(conj p.2).im| = |p.2.im|
(conj p.2).re = p.2.re
0 < (conj p.2).im
conj p.2 ∉ conjugateFinset S
```

Use conjugation involutivity for injectivity and surjectivity.

- [ ] **Step 6: Prove equality of the square masses under conjugation**

```lean
theorem zetaRightDyadicNegativeMassSquareExcluding_eq_positive_conjugateFinset
    (x beta : ℝ) (k : ℕ) (S : Finset ℂ) :
    zetaRightDyadicNegativeMassSquareExcluding x beta k S =
      zetaRightDyadicPositiveMassSquareExcluding
        x beta k (conjugateFinset S) := by
  -- Finset.sum_bij using `(n, rho) ↦ (n, conj rho)`.
  -- Rewrite norm and analytic multiplicity by the existing zeta theorems.
```

- [ ] **Step 7: Run the focused source and contract builds**

```bash
LEAN_NUM_THREADS=2 lake build PrimeNumberTheorem.HalfIsolatedZetaFullDyadicCapacityBridge
LEAN_NUM_THREADS=2 lake build PrimeNumberTheorem.HalfIsolatedZetaFullDyadicCapacityBridge.Contract
```

Expected: both targets pass; no existing theorem statement changes.

- [ ] **Step 8: Commit the conjugation transfer checkpoint**

```bash
git add PrimeNumberTheorem/HalfIsolatedZetaFullDyadicCapacityBridge.lean \
  PrimeNumberTheorem/HalfIsolatedZetaFullDyadicCapacityBridge/Contract.lean
git commit -m "feat: transfer negative dyadic zeta mass through conjugation"
```

---

### Task 2: Negative Carlson bound and complete dyadic mass

**Files:**
- Modify: `PrimeNumberTheorem/HalfIsolatedZetaFullDyadicCapacityBridge.lean`
- Modify: `PrimeNumberTheorem/HalfIsolatedZetaFullDyadicCapacityBridge/Contract.lean`

**Interfaces:**
- Consumes: Task 1's exact mass equality and PR #271's `zetaRightDyadicPositiveMassSquareExcluding_le_twoCarlsonCapacities`.
- Produces: `zetaRightDyadicNegativeMassSquareExcluding_le_twoCarlsonCapacities`, `zetaRightDyadicFullMassSquareExcluding`, `zetaRightDyadicFullMassSquareExcluding_eq_pos_add_neg`, and `zetaRightDyadicFullMassSquareExcluding_le_fourCarlsonCapacities`.

- [ ] **Step 1: Extend the contract with the final signatures**

```lean
#check zetaRightDyadicNegativeMassSquareExcluding_le_twoCarlsonCapacities
#check zetaRightDyadicFullMassSquareExcluding
#check zetaRightDyadicFullMassSquareExcluding_eq_pos_add_neg
#check zetaRightDyadicFullMassSquareExcluding_le_fourCarlsonCapacities
```

- [ ] **Step 2: Derive the negative two-capacity theorem without new analytic input**

```lean
theorem zetaRightDyadicNegativeMassSquareExcluding_le_twoCarlsonCapacities
    {x sigma beta : ℝ} {k : ℕ} {S : Finset ℂ}
    (hx : 1 ≤ x) (hk : 1 ≤ k) (hsigma : sigma < beta) :
    zetaRightDyadicNegativeMassSquareExcluding x beta k S ≤
      (x ^ (1 - beta)) ^ 2 *
        (actualCarlsonDyadicStripSquareReciprocalCapacityExcluding
            sigma 1 (k - 1) (conjugateFinset S) +
         actualCarlsonDyadicStripSquareReciprocalCapacityExcluding
            sigma 1 k (conjugateFinset S)) := by
  rw [zetaRightDyadicNegativeMassSquareExcluding_eq_positive_conjugateFinset]
  exact zetaRightDyadicPositiveMassSquareExcluding_le_twoCarlsonCapacities
    hx hk hsigma
```

- [ ] **Step 3: Define the complete excluded mass**

```lean
noncomputable def zetaRightDyadicFullMassSquareExcluding
    (x beta : ℝ) (k : ℕ) (S : Finset ℂ) : ℝ :=
  ∑ p ∈ (zetaRightDyadicBucketPairs beta k).filter (fun p => p.2 ∉ S),
    zetaDyadicBaseMass x beta p ^ 2
```

- [ ] **Step 4: Prove every full-mass member has nonzero ordinate**

For a filtered pair `p`, put `p.2` into `zetaRightDyadicZeros beta k` and apply `zetaRightDyadicZeros_spec`.  Combine

```lean
(2 : ℝ) ^ k ≤ |p.2.im|
0 < (2 : ℝ) ^ k
```

to prove `p.2.im ≠ 0`.

- [ ] **Step 5: Prove the exact positive-negative finite-sum split**

```lean
theorem zetaRightDyadicFullMassSquareExcluding_eq_pos_add_neg
    (x beta : ℝ) (k : ℕ) (S : Finset ℂ) :
    zetaRightDyadicFullMassSquareExcluding x beta k S =
      zetaRightDyadicPositiveMassSquareExcluding x beta k S +
      zetaRightDyadicNegativeMassSquareExcluding x beta k S := by
  -- Partition by `0 < p.2.im`; the nonzero-ordinate lemma turns the complement
  -- into `p.2.im < 0`.  Use `Finset.sum_filter_add_sum_filter_not`.
```

- [ ] **Step 6: Combine positive and negative bounds**

```lean
theorem zetaRightDyadicFullMassSquareExcluding_le_fourCarlsonCapacities
    {x sigma beta : ℝ} {k : ℕ} {S : Finset ℂ}
    (hx : 1 ≤ x) (hk : 1 ≤ k) (hsigma : sigma < beta) :
    zetaRightDyadicFullMassSquareExcluding x beta k S ≤
      (x ^ (1 - beta)) ^ 2 *
        (actualCarlsonDyadicStripSquareReciprocalCapacityExcluding
            sigma 1 (k - 1) S +
         actualCarlsonDyadicStripSquareReciprocalCapacityExcluding sigma 1 k S +
         actualCarlsonDyadicStripSquareReciprocalCapacityExcluding
            sigma 1 (k - 1) (conjugateFinset S) +
         actualCarlsonDyadicStripSquareReciprocalCapacityExcluding
            sigma 1 k (conjugateFinset S)) := by
  rw [zetaRightDyadicFullMassSquareExcluding_eq_pos_add_neg]
  have hpos := zetaRightDyadicPositiveMassSquareExcluding_le_twoCarlsonCapacities
    (S := S) hx hk hsigma
  have hneg := zetaRightDyadicNegativeMassSquareExcluding_le_twoCarlsonCapacities
    (S := S) hx hk hsigma
  linarith
```

If associativity prevents the final `linarith`, normalize only ring syntax with `ring_nf`; do not change the four capacity terms.

- [ ] **Step 7: Run focused source and contract builds**

```bash
LEAN_NUM_THREADS=2 lake build PrimeNumberTheorem.HalfIsolatedZetaFullDyadicCapacityBridge
LEAN_NUM_THREADS=2 lake build PrimeNumberTheorem.HalfIsolatedZetaFullDyadicCapacityBridge.Contract
```

Expected: both pass and the contract prints the exact four-capacity theorem.

- [ ] **Step 8: Commit the complete-mass checkpoint**

```bash
git add PrimeNumberTheorem/HalfIsolatedZetaFullDyadicCapacityBridge.lean \
  PrimeNumberTheorem/HalfIsolatedZetaFullDyadicCapacityBridge/Contract.lean
git commit -m "feat: bound full dyadic zeta mass by Carlson capacities"
```

---

### Task 3: Axiom audit and stacked Draft PR

**Files:**
- Create: `PrimeNumberTheorem/HalfIsolatedZetaFullDyadicCapacityBridge/AxiomAudit.lean`
- Verify: `PrimeNumberTheorem/HalfIsolatedZetaFullDyadicCapacityBridge.lean`
- Verify: `PrimeNumberTheorem/HalfIsolatedZetaFullDyadicCapacityBridge/Contract.lean`

**Interfaces:**
- Consumes: all public theorems from Tasks 1 and 2.
- Produces: reproducible focused build evidence and a narrow stacked Draft PR over PR #271.

- [ ] **Step 1: Add the axiom-audit module**

```lean
import PrimeNumberTheorem.HalfIsolatedZetaFullDyadicCapacityBridge

namespace PrimeNumberTheorem.VKEdgePiOverTwo

#print axioms mem_conjugateFinset_iff
#print axioms not_mem_conjugateFinset_iff
#print axioms zetaRightDyadicNegativeMassSquareExcluding_eq_positive_conjugateFinset
#print axioms zetaRightDyadicNegativeMassSquareExcluding_le_twoCarlsonCapacities
#print axioms zetaRightDyadicFullMassSquareExcluding_eq_pos_add_neg
#print axioms zetaRightDyadicFullMassSquareExcluding_le_fourCarlsonCapacities

end PrimeNumberTheorem.VKEdgePiOverTwo
```

- [ ] **Step 2: Run the three focused builds**

```bash
LEAN_NUM_THREADS=4 lake build PrimeNumberTheorem.HalfIsolatedZetaFullDyadicCapacityBridge
LEAN_NUM_THREADS=2 lake build PrimeNumberTheorem.HalfIsolatedZetaFullDyadicCapacityBridge.Contract
LEAN_NUM_THREADS=2 lake build PrimeNumberTheorem.HalfIsolatedZetaFullDyadicCapacityBridge.AxiomAudit
```

Expected: all pass.  Contract and audit may run concurrently only after the source target passes.

- [ ] **Step 3: Capture the exact axiom output**

```bash
LEAN_NUM_THREADS=1 lake env lean \
  PrimeNumberTheorem/HalfIsolatedZetaFullDyadicCapacityBridge/AxiomAudit.lean
```

Expected: each theorem depends only on standard logical axioms such as `propext`, `Classical.choice`, and `Quot.sound`.

- [ ] **Step 4: Run static boundary checks**

```bash
git diff --check
! rg -n '\b(sorry|admit|axiom)\b' \
  PrimeNumberTheorem/HalfIsolatedZetaFullDyadicCapacityBridge.lean \
  PrimeNumberTheorem/HalfIsolatedZetaFullDyadicCapacityBridge/Contract.lean \
  PrimeNumberTheorem/HalfIsolatedZetaFullDyadicCapacityBridge/AxiomAudit.lean
git status --short --branch
```

Expected: no placeholders, no added axiom declaration, and only the three intended Lean files plus the already committed design and plan documents.

- [ ] **Step 5: Commit and push the audit checkpoint**

```bash
git add PrimeNumberTheorem/HalfIsolatedZetaFullDyadicCapacityBridge/AxiomAudit.lean
git commit -m "test: audit full dyadic zeta capacity bridge"
git push -u origin codex/half-isolated-zeta-full-dyadic-capacity-bridge
```

- [ ] **Step 6: Open a stacked Draft PR**

Use base `codex/half-isolated-dyadic-capacity-bridge` and head `codex/half-isolated-zeta-full-dyadic-capacity-bridge`.  The PR body must claim only exact `conj(S)` transfer, negative two-shell capacity, exact positive-negative mass decomposition, and the full four-capacity upper bound.

The PR body must explicitly exclude Occupancy-Gram integration, repeatable Sharp energy, two-height tail transfer, multi-window accumulation, Carlson contradiction, and RH.
