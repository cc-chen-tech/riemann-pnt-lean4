# Riemann-von Mangoldt Feasibility Spike Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build the three verified Lean 4 interfaces that decide whether the project should continue toward the full Riemann-von Mangoldt formula: multiplicity-weighted one-sided zero counting, a good-height rectangle count identity, and the exact completed-zeta Gamma decomposition.

**Architecture:** Add a focused `PrimeNumberTheorem.RiemannVonMangoldt` module family. The zero-count module filters the existing finite nontrivial-zero set and sums analytic multiplicities; the completed-zeta module proves the entire/zero/multiplicity/boundary facts needed by both later modules; the rectangle module applies the existing finite-principal-part regularization and `MathlibAux.boundaryRectIntegral` residue theorem; the Gamma module reuses the already-proved `Gammaℝ` logarithmic derivative. A single contract module fixes the public signatures and a single axiom-audit module checks the final theorem surface.

**Tech Stack:** Lean 4.29.1, Mathlib, Lake, project modules `PrimeNumberTheorem.NontrivialZeroMultiplicity`, `ZeroFreeRegion.MeromorphicAux`, `MathlibAux.BoundaryRectResidue`, and `PrimeNumberTheorem.LeftVerticalEdge`.

## Global Constraints

- The branch contains exactly three mathematical deliverables: `riemannZeroCount`, the good-height rectangle count identity, and the exact Gamma-factor logarithmic-derivative decomposition.
- Every exported result is a proved Lean theorem; do not add a `def ... : Prop` substitute.
- Count nontrivial zeta zeros satisfying `0 < Im rho` and `Im rho <= T`, with `analyticOrderNatAt riemannZeta rho` multiplicity.
- Reuse `RiemannHypothesis.completedZeta`; do not introduce another xi function.
- Use the project-specific finite-principal-part route; do not add a general meromorphic argument-principle target.
- The contour is `0 <= Re s <= 1`, `U <= Im s <= T`, with `0 < U < T` and both heights satisfying `ExplicitFormulaAux.goodHeight`.
- Do not prove or state the full Riemann-von Mangoldt asymptotic, an `O(log T)` boundary-argument estimate, an all-height extension, a new zero-free region, a zero-density estimate, or an RH consequence.
- The final axiom surface may contain only `propext`, `Classical.choice`, and `Quot.sound`.

---

## File Map

- Create `PrimeNumberTheorem/RiemannVonMangoldt/ZeroCount.lean`: positive-height finite zero sets, interval zero sets, `riemannZeroCount`, monotonicity, and count-difference identities.
- Create `PrimeNumberTheorem/RiemannVonMangoldt/CompletedZeta.lean`: entire completed zeta, local factorization, critical-strip zero and multiplicity equivalence, and zero-free vertical edges.
- Create `PrimeNumberTheorem/RiemannVonMangoldt/GammaDecomposition.lean`: exact logarithmic derivative decomposition.
- Create `PrimeNumberTheorem/RiemannVonMangoldt/RectangleCount.lean`: compact rectangle regularization and the two residue/count equalities.
- Create `PrimeNumberTheorem/RiemannVonMangoldt.lean`: aggregate import only.
- Create `Test/RiemannVonMangoldtContract.lean`: exact public signature checks for all three deliverables.
- Create `Test/RiemannVonMangoldtAxiomAudit.lean`: `#print axioms` checks for the final theorem surface.
- Modify `lakefile.lean`: add the aggregate module and both test modules to the default target.

---

### Task 1: Multiplicity-Weighted One-Sided Zero Count

**Files:**
- Create: `PrimeNumberTheorem/RiemannVonMangoldt/ZeroCount.lean`
- Create: `Test/RiemannVonMangoldtContract.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes: `PrimeNumberTheorem.nontrivialZerosFinset`, `PrimeNumberTheorem.mem_nontrivialZerosFinset`, `analyticOrderNatAt riemannZeta`.
- Produces: `positiveNontrivialZerosFinset`, `positiveNontrivialZerosBetween`, `riemannZeroCount`, `riemannZeroCount_mono`, `riemannZeroCount_add_between`, and `riemannZeroCount_sub_eq_between`.

- [ ] **Step 1: Write the failing contract**

Create `Test/RiemannVonMangoldtContract.lean` with:

```lean
import PrimeNumberTheorem.RiemannVonMangoldt.ZeroCount

open Complex
open scoped BigOperators

namespace PrimeNumberTheorem.RiemannVonMangoldt

example {rho : ℂ} {T : ℝ} :
    rho ∈ positiveNontrivialZerosFinset T ↔
      RiemannHypothesis.IsNontrivialZero rho ∧ 0 < rho.im ∧ rho.im ≤ T :=
  mem_positiveNontrivialZerosFinset

example (T : ℝ) :
    riemannZeroCount T =
      ∑ rho ∈ positiveNontrivialZerosFinset T,
        analyticOrderNatAt riemannZeta rho :=
  rfl

example {U T : ℝ} (hUT : U ≤ T) :
    riemannZeroCount U +
        ∑ rho ∈ positiveNontrivialZerosBetween U T,
          analyticOrderNatAt riemannZeta rho =
      riemannZeroCount T :=
  riemannZeroCount_add_between hUT

example {U T : ℝ} (hUT : U ≤ T) :
    riemannZeroCount T - riemannZeroCount U =
      ∑ rho ∈ positiveNontrivialZerosBetween U T,
        analyticOrderNatAt riemannZeta rho :=
  riemannZeroCount_sub_eq_between hUT

end PrimeNumberTheorem.RiemannVonMangoldt
```

Add `` `Test.RiemannVonMangoldtContract `` to the default roots in `lakefile.lean`.

- [ ] **Step 2: Run the contract and confirm the expected failure**

Run:

```bash
lake -Kjobs=1 build Test.RiemannVonMangoldtContract
```

Expected: failure because `PrimeNumberTheorem.RiemannVonMangoldt.ZeroCount` does not exist. A missing dependency `.olean` is not an acceptable red state; build the named dependency first and rerun until the failure is specifically the missing new module or declaration.

- [ ] **Step 3: Implement the finite sets and membership normal forms**

Create `PrimeNumberTheorem/RiemannVonMangoldt/ZeroCount.lean` with this declaration surface:

```lean
import PrimeNumberTheorem.NontrivialZeroMultiplicity

open Complex
open scoped BigOperators

namespace PrimeNumberTheorem
namespace RiemannVonMangoldt

noncomputable def positiveNontrivialZerosFinset (T : ℝ) : Finset ℂ :=
  (nontrivialZerosFinset T).filter fun rho : ℂ => 0 < rho.im

lemma mem_positiveNontrivialZerosFinset {rho : ℂ} {T : ℝ} :
    rho ∈ positiveNontrivialZerosFinset T ↔
      RiemannHypothesis.IsNontrivialZero rho ∧ 0 < rho.im ∧ rho.im ≤ T := by
  simp only [positiveNontrivialZerosFinset, Finset.mem_filter,
    mem_nontrivialZerosFinset]
  constructor
  · rintro ⟨⟨hzero, hheight⟩, him⟩
    exact ⟨hzero, him, by simpa [abs_of_pos him] using hheight⟩
  · rintro ⟨hzero, him, hheight⟩
    exact ⟨⟨hzero, by simpa [abs_of_pos him] using hheight⟩, him⟩

lemma positiveNontrivialZerosFinset_subset {U T : ℝ} (hUT : U ≤ T) :
    positiveNontrivialZerosFinset U ⊆ positiveNontrivialZerosFinset T := by
  intro rho hrho
  rcases mem_positiveNontrivialZerosFinset.mp hrho with
    ⟨hzero, him, hheight⟩
  exact mem_positiveNontrivialZerosFinset.mpr
    ⟨hzero, him, hheight.trans hUT⟩

noncomputable def positiveNontrivialZerosBetween (U T : ℝ) : Finset ℂ :=
  positiveNontrivialZerosFinset T \ positiveNontrivialZerosFinset U

lemma mem_positiveNontrivialZerosBetween {rho : ℂ} {U T : ℝ} (hU : 0 ≤ U) :
    rho ∈ positiveNontrivialZerosBetween U T ↔
      RiemannHypothesis.IsNontrivialZero rho ∧ U < rho.im ∧ rho.im ≤ T := by
  constructor
  · intro hrho
    rcases Finset.mem_sdiff.mp hrho with ⟨hrhoT, hrhoU⟩
    rcases mem_positiveNontrivialZerosFinset.mp hrhoT with
      ⟨hzero, him, hheightT⟩
    have hheightU : U < rho.im := by
      by_contra hnot
      exact hrhoU (mem_positiveNontrivialZerosFinset.mpr
        ⟨hzero, him, le_of_not_gt hnot⟩)
    exact ⟨hzero, hheightU, hheightT⟩
  · rintro ⟨hzero, hheightU, hheightT⟩
    have him : 0 < rho.im := lt_of_le_of_lt hU hheightU
    apply Finset.mem_sdiff.mpr
    exact ⟨mem_positiveNontrivialZerosFinset.mpr
      ⟨hzero, him, hheightT⟩, by
        intro hrhoU
        exact (not_le_of_gt hheightU)
          (mem_positiveNontrivialZerosFinset.mp hrhoU).2.2⟩
```

- [ ] **Step 4: Implement the count and exact difference identities**

Append:

```lean
noncomputable def riemannZeroCount (T : ℝ) : ℕ :=
  ∑ rho ∈ positiveNontrivialZerosFinset T,
    analyticOrderNatAt riemannZeta rho

lemma riemannZeroCount_nonneg (T : ℝ) : 0 ≤ riemannZeroCount T :=
  Nat.zero_le _

theorem riemannZeroCount_add_between {U T : ℝ} (hUT : U ≤ T) :
    riemannZeroCount U +
        ∑ rho ∈ positiveNontrivialZerosBetween U T,
          analyticOrderNatAt riemannZeta rho =
      riemannZeroCount T := by
  classical
  have hsubset := positiveNontrivialZerosFinset_subset hUT
  unfold riemannZeroCount positiveNontrivialZerosBetween
  rw [add_comm]
  exact Finset.sum_sdiff hsubset

theorem riemannZeroCount_mono {U T : ℝ} (hUT : U ≤ T) :
    riemannZeroCount U ≤ riemannZeroCount T := by
  have hsplit := riemannZeroCount_add_between hUT
  omega

theorem riemannZeroCount_sub_eq_between {U T : ℝ} (hUT : U ≤ T) :
    riemannZeroCount T - riemannZeroCount U =
      ∑ rho ∈ positiveNontrivialZerosBetween U T,
        analyticOrderNatAt riemannZeta rho := by
  have hsplit := riemannZeroCount_add_between hUT
  omega

end RiemannVonMangoldt
end PrimeNumberTheorem
```

- [ ] **Step 5: Run the focused contract**

Run:

```bash
lake -Kjobs=1 build Test.RiemannVonMangoldtContract
```

Expected: `Build completed successfully` with no declaration errors.

- [ ] **Step 6: Commit Task 1**

```bash
git add PrimeNumberTheorem/RiemannVonMangoldt/ZeroCount.lean Test/RiemannVonMangoldtContract.lean lakefile.lean
git commit -m "feat(zeta): add multiplicity-weighted one-sided zero count"
```

---

### Task 2: Completed-Zeta Core Facts

**Files:**
- Create: `PrimeNumberTheorem/RiemannVonMangoldt/CompletedZeta.lean`
- Modify: `Test/RiemannVonMangoldtContract.lean`

**Interfaces:**
- Consumes: `RiemannHypothesis.completedZeta`, `completedRiemannZeta_eq`, `riemannZeta_def_of_ne_zero`, `completedRiemannZeta_one_sub`, `Gammaℝ_ne_zero_of_re_pos`, and `analyticOrderAt_mul`.
- Produces: `differentiable_completedZeta`, `completedZeta_eventuallyEq_factorization`, `completedZeta_eq_zero_iff_riemannZeta_eq_zero_of_mem_criticalStrip`, `analyticOrderNatAt_completedZeta_eq_riemannZeta_of_mem_criticalStrip`, and zero-free lemmas on `Re s = 0, 1` away from the real-axis endpoints.

- [ ] **Step 1: Extend the contract before implementation**

Append before the namespace end in `Test/RiemannVonMangoldtContract.lean`:

```lean
example : Differentiable ℂ RiemannHypothesis.completedZeta :=
  differentiable_completedZeta

example {s : ℂ} (hsre : 0 < s.re) (hsre' : s.re < 1) :
    RiemannHypothesis.completedZeta s = 0 ↔ riemannZeta s = 0 :=
  completedZeta_eq_zero_iff_riemannZeta_eq_zero_of_mem_criticalStrip
    hsre hsre'

example {s : ℂ} (hsre : 0 < s.re) (hsre' : s.re < 1) :
    analyticOrderNatAt RiemannHypothesis.completedZeta s =
      analyticOrderNatAt riemannZeta s :=
  analyticOrderNatAt_completedZeta_eq_riemannZeta_of_mem_criticalStrip
    hsre hsre'

example {s : ℂ} (hsre : s.re = 1) (hsim : s.im ≠ 0) :
    RiemannHypothesis.completedZeta s ≠ 0 :=
  completedZeta_ne_zero_of_re_eq_one_of_im_ne_zero hsre hsim

example {s : ℂ} (hsre : s.re = 0) (hsim : s.im ≠ 0) :
    RiemannHypothesis.completedZeta s ≠ 0 :=
  completedZeta_ne_zero_of_re_eq_zero_of_im_ne_zero hsre hsim
```

Add `import PrimeNumberTheorem.RiemannVonMangoldt.CompletedZeta` to the contract.

- [ ] **Step 2: Run the contract and confirm missing declarations**

Run:

```bash
lake -Kjobs=1 build Test.RiemannVonMangoldtContract
```

Expected: failure on the new completed-zeta module or the first new declaration.

- [ ] **Step 3: Prove entire-ness and the local factorization**

Create `PrimeNumberTheorem/RiemannVonMangoldt/CompletedZeta.lean` importing `PrimeNumberTheorem.NontrivialZeroMultiplicity`. Keep all declarations in `PrimeNumberTheorem.RiemannVonMangoldt`.

Use the literal definition of `RiemannHypothesis.completedZeta` to prove:

```lean
theorem differentiable_completedZeta :
    Differentiable ℂ RiemannHypothesis.completedZeta := by
  unfold RiemannHypothesis.completedZeta
  fun_prop

lemma completedZeta_eventuallyEq_factorization {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    RiemannHypothesis.completedZeta =ᶠ[nhds s]
      fun z : ℂ => (1 / 2) * z * (z - 1) * completedRiemannZeta z := by
  filter_upwards [eventually_ne_nhds hs0, eventually_ne_nhds hs1] with z hz0 hz1
  rw [RiemannHypothesis.completedZeta, completedRiemannZeta_eq]
  field_simp [hz0, hz1]
  ring
```

The `field_simp` line is the first permitted normalization. If Lean leaves `1 - z` denominators, first rewrite `one_sub z = -(z - 1)` and then run the same `field_simp`; do not change the mathematical factorization.

- [ ] **Step 4: Prove zero and multiplicity equivalence in the open strip**

Add private helpers proving `s ≠ 0`, `s ≠ 1`, Gamma regularity/nonvanishing from `0 < s.re`, and the local equality

```lean
completedRiemannZeta =ᶠ[nhds s]
  fun z : ℂ => Gammaℝ z * riemannZeta z
```

using `eventually_ne_nhds hs0`, `riemannZeta_def_of_ne_zero`, and division cancellation by `Gammaℝ_ne_zero_of_re_pos`. Then prove the public zero equivalence by evaluating both eventual equalities at `s` and applying `mul_eq_zero` to the nonzero prefactor and Gamma factor.

For the multiplicity theorem, use these exact reductions:

```lean
have hxi := analyticOrderAt_congr
  (completedZeta_eventuallyEq_factorization hs0 hs1)
have hLambda := analyticOrderAt_congr hcompleted
rw [hxi, analyticOrderAt_mul, analyticOrderAt_mul,
  analyticOrderAt_mul]
rw [analyticOrderAt_eq_zero.mpr (Or.inr hhalf_ne),
  analyticOrderAt_eq_zero.mpr (Or.inr hs0),
  analyticOrderAt_eq_zero.mpr (Or.inr (sub_ne_zero.mpr hs1))]
rw [hLambda, analyticOrderAt_mul]
rw [analyticOrderAt_eq_zero.mpr (Or.inr hGamma_ne)]
simp
```

Supply the corresponding `AnalyticAt` proofs to each `analyticOrderAt_mul`; obtain the zeta proof from `differentiableAt_riemannZeta hs1`, the completed-zeta proof from `differentiable_completedZeta.analyticAt`, and the Gamma proof directly from `Gammaℝ_def` plus `Complex.differentiableAt_Gamma`. Finish the natural-order statement with `congrArg ENat.toNat`.

- [ ] **Step 5: Prove the two vertical-edge nonvanishing lemmas**

For `Re s = 1`, derive `s ≠ 0` and `s ≠ 1` from `hsre` and `hsim`, use `riemannZeta_ne_zero_of_one_le_re`, Gamma nonvanishing, and the factorization value at `s`.

For `Re s = 0`, set `w := 1 - s`; prove `w.re = 1` and `w.im ≠ 0`, apply the `Re = 1` lemma to `w`, and rewrite with `RiemannHypothesis.functional_equation s`.

The exported signatures must be exactly those in the contract. These lemmas are about completed zeta, not the false statement that ordinary zeta has no trivial zeros on the whole line `Re s = 0`.

- [ ] **Step 6: Run focused builds**

```bash
lake -Kjobs=1 build PrimeNumberTheorem.RiemannVonMangoldt.CompletedZeta
lake -Kjobs=1 build Test.RiemannVonMangoldtContract
```

Expected: both builds complete successfully.

- [ ] **Step 7: Commit Task 2**

```bash
git add PrimeNumberTheorem/RiemannVonMangoldt/CompletedZeta.lean Test/RiemannVonMangoldtContract.lean
git commit -m "feat(zeta): prove completed-zeta contour core facts"
```

---

### Task 3: Exact Gamma-Factor Decomposition

**Files:**
- Create: `PrimeNumberTheorem/RiemannVonMangoldt/GammaDecomposition.lean`
- Modify: `Test/RiemannVonMangoldtContract.lean`

**Interfaces:**
- Consumes: `completedZeta_eventuallyEq_factorization`, `ExplicitFormulaResidues.logDeriv_Gammaℝ`, `ExplicitFormulaResidues.differentiableAt_Gammaℝ_of_regular`, and `ExplicitFormulaResidues.logDeriv_riemannZeta_eq_completed_sub_Gammaℝ`.
- Produces: `logDeriv_completedZeta_eq_zeta_add_gamma` with the exact elementary and digamma terms.

- [ ] **Step 1: Add the failing signature check**

Append:

```lean
example {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hzeta : riemannZeta s ≠ 0) :
    logDeriv RiemannHypothesis.completedZeta s =
      1 / s + 1 / (s - 1) - Complex.log Real.pi / 2 +
        Complex.digamma (s / 2) / 2 + logDeriv riemannZeta s :=
  logDeriv_completedZeta_eq_zeta_add_gamma hs0 hs1 hzeta
```

Add the Gamma module import and run the contract. Expected: missing module/declaration failure.

- [ ] **Step 2: Isolate the only Gamma-regularity case split**

Create `PrimeNumberTheorem/RiemannVonMangoldt/GammaDecomposition.lean` importing `PrimeNumberTheorem.RiemannVonMangoldt.CompletedZeta` and `PrimeNumberTheorem.LeftVerticalEdge`.

Prove the helper:

```lean
private lemma gamma_regular_of_ne_zero_of_riemannZeta_ne_zero
    {s : ℂ} (hs0 : s ≠ 0) (hzeta : riemannZeta s ≠ 0) :
    ∀ n : ℕ, s / 2 ≠ -(n : ℂ) := by
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    apply hs0
    linear_combination 2 * hn
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have hs : s = -2 * ((k : ℂ) + 1) := by
      linear_combination 2 * hn
    apply hzeta
    rw [hs]
    exact riemannZeta_neg_two_mul_nat_add_one k
```

If `linear_combination` needs casts normalized, run `push_cast at hn` first. Keep this helper private; it is plumbing, not a fourth deliverable.

- [ ] **Step 3: Split the completed-zeta logarithmic derivative**

Use `completedZeta_eventuallyEq_factorization hs0 hs1` to transport both the function value and derivative at `s`. Apply `logDeriv_mul` successively to `(1/2) * s`, `s - 1`, and `completedRiemannZeta s`. Normalize the elementary factors with `logDeriv_const_mul`, `logDeriv_id`, and `simp [logDeriv_apply]` to prove the internal identity:

```lean
private lemma logDeriv_completedZeta_eq_elementary_add_completed
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hcompleted : completedRiemannZeta s ≠ 0) :
    logDeriv RiemannHypothesis.completedZeta s =
      1 / s + 1 / (s - 1) + logDeriv completedRiemannZeta s := by
  let F : ℂ → ℂ := fun z => (1 / 2) * z
  let G : ℂ → ℂ := fun z => z - 1
  have hFne : F s ≠ 0 := mul_ne_zero (by norm_num) hs0
  have hGne : G s ≠ 0 := sub_ne_zero.mpr hs1
  have hFdiff : DifferentiableAt ℂ F s := by
    dsimp [F]
    fun_prop
  have hGdiff : DifferentiableAt ℂ G s := by
    dsimp [G]
    fun_prop
  have hFGne : F s * G s ≠ 0 := mul_ne_zero hFne hGne
  have hFGdiff : DifferentiableAt ℂ (fun z => F z * G z) s :=
    hFdiff.mul hGdiff
  have hcompletedDiff : DifferentiableAt ℂ completedRiemannZeta s :=
    differentiableAt_completedZeta hs0 hs1
  have heq := completedZeta_eventuallyEq_factorization hs0 hs1
  have hlogeq :
      logDeriv RiemannHypothesis.completedZeta s =
        logDeriv (fun z : ℂ => F z * G z * completedRiemannZeta z) s := by
    simp only [logDeriv_apply]
    rw [heq.deriv_eq]
    congr 1
    simpa [F, G] using heq.self_of_nhds
  have hFlog : logDeriv F s = 1 / s := by
    dsimp [F]
    rw [logDeriv_const_mul s (1 / 2) (by norm_num)]
    simpa using logDeriv_id' s
  have hGlog : logDeriv G s = 1 / (s - 1) := by
    simp [G, logDeriv_apply]
  rw [hlogeq,
    logDeriv_mul s hFGne hcompleted hFGdiff hcompletedDiff,
    logDeriv_mul s hFne hGne hFdiff hGdiff, hFlog, hGlog]
  ring
```

The proof deliberately uses `heq.deriv_eq` and `heq.self_of_nhds`; an extensional rewrite of `completedRiemannZeta` at `0` or `1` is not valid.

- [ ] **Step 4: Assemble the public exact formula**

In the public theorem:

1. Obtain `hsGamma` from the private regularity helper.
2. Obtain `hGammaDiff` from `ExplicitFormulaResidues.differentiableAt_Gammaℝ_of_regular hsGamma`.
3. Obtain `hGammaNe` from `Gammaℝ_def`, `Complex.cpow_ne_zero_iff`, and `Complex.Gamma_ne_zero hsGamma`, or from `Gammaℝ_eq_zero_iff` plus the same regularity helper.
4. Prove `completedRiemannZeta s ≠ 0` by rewriting `riemannZeta_def_of_ne_zero hs0` and using `hzeta`.
5. Apply `logDeriv_completedZeta_eq_elementary_add_completed`.
6. Rearrange `ExplicitFormulaResidues.logDeriv_riemannZeta_eq_completed_sub_Gammaℝ hs0 hs1 hGammaNe hGammaDiff hzeta` to solve for `logDeriv completedRiemannZeta s`.
7. Rewrite `ExplicitFormulaResidues.logDeriv_Gammaℝ hsGamma` and finish with `ring`.

This yields exactly the contract statement; do not add an asymptotic corollary.

- [ ] **Step 5: Run focused builds and commit**

```bash
lake -Kjobs=1 build PrimeNumberTheorem.RiemannVonMangoldt.GammaDecomposition
lake -Kjobs=1 build Test.RiemannVonMangoldtContract
git add PrimeNumberTheorem/RiemannVonMangoldt/GammaDecomposition.lean Test/RiemannVonMangoldtContract.lean
git commit -m "feat(zeta): decompose completed-zeta logarithmic derivative"
```

Expected: both builds pass before the commit.

---

### Task 4: Good-Height Rectangle Counts Zeros

**Files:**
- Create: `PrimeNumberTheorem/RiemannVonMangoldt/RectangleCount.lean`
- Modify: `Test/RiemannVonMangoldtContract.lean`

**Interfaces:**
- Consumes: Task 1 finite sets/count identities; Task 2 entire, zero-equivalence, multiplicity, and vertical-edge lemmas; `ZeroFreeRegion.analyticOnNhd_toMeromorphicNFOn_logDeriv_sub_finset_principalParts`; `MathlibAux.boundaryRectIntegral_congr_of_eqOn_boundary`; and `MathlibAux.boundaryRectIntegral_eq_finite_simple_pole_residue_sum_of_differentiableOn`.
- Produces: `boundaryRectIntegral_logDeriv_completedZeta_eq_between_sum` and `boundaryRectIntegral_logDeriv_completedZeta_eq_zeroCount_sub`.

- [ ] **Step 1: Add both failing contour contracts**

Append:

```lean
example {U T : ℝ} (hU : 0 < U) (hUT : U < T)
    (hUgood : ExplicitFormulaAux.goodHeight U)
    (hTgood : ExplicitFormulaAux.goodHeight T) :
    MathlibAux.boundaryRectIntegral
        (logDeriv RiemannHypothesis.completedZeta) 0 1 U T =
      (2 * Real.pi * I) *
        ∑ rho ∈ positiveNontrivialZerosBetween U T,
          (analyticOrderNatAt riemannZeta rho : ℂ) :=
  boundaryRectIntegral_logDeriv_completedZeta_eq_between_sum
    hU hUT hUgood hTgood

example {U T : ℝ} (hU : 0 < U) (hUT : U < T)
    (hUgood : ExplicitFormulaAux.goodHeight U)
    (hTgood : ExplicitFormulaAux.goodHeight T) :
    MathlibAux.boundaryRectIntegral
        (logDeriv RiemannHypothesis.completedZeta) 0 1 U T =
      (2 * Real.pi * I) *
        ((riemannZeroCount T - riemannZeroCount U : ℕ) : ℂ) :=
  boundaryRectIntegral_logDeriv_completedZeta_eq_zeroCount_sub
    hU hUT hUgood hTgood
```

Add the rectangle module import and run the contract. Expected: missing module/declaration failure.

- [ ] **Step 2: Define only the approved rectangle and pole support**

Create `PrimeNumberTheorem/RiemannVonMangoldt/RectangleCount.lean` importing `PrimeNumberTheorem.RiemannVonMangoldt.ZeroCount`, `PrimeNumberTheorem.RiemannVonMangoldt.CompletedZeta`, `ZeroFreeRegion.MeromorphicAux`, and `MathlibAux.BoundaryRectResidue`.

Use private abbreviations:

```lean
private def zeroCountRectangle (U T : ℝ) : Set ℂ :=
  [[(0 : ℝ), 1]] ×ℂ [[U, T]]

private noncomputable def zeroCountRectanglePoles (U T : ℝ) : Finset ℂ :=
  positiveNontrivialZerosBetween U T
```

Do not build a divisor-derived second finset. The Task 1 interval finset is already finite and is exactly the support that must be identified with the count difference.

- [ ] **Step 3: Prove boundary zero-freeness and interior classification**

Prove one private lemma with this signature:

```lean
private lemma completedZeta_zero_iff_mem_between_on_rectangle
    {U T : ℝ} (hU : 0 < U) (hUT : U < T)
    (hUgood : ExplicitFormulaAux.goodHeight U)
    (hTgood : ExplicitFormulaAux.goodHeight T)
    {z : ℂ} (hz : z ∈ zeroCountRectangle U T) :
    RiemannHypothesis.completedZeta z = 0 ↔
      z ∈ zeroCountRectanglePoles U T
```

Prove it by the following fixed sequence:

1. Normalize `hz` using `Complex.mem_reProdIm`, `Set.uIcc_of_le zero_le_one`, and `Set.uIcc_of_le hUT.le`, obtaining `0 ≤ z.re`, `z.re ≤ 1`, `U ≤ z.im`, and `z.im ≤ T`.
2. In the forward direction, exclude `z.re = 0` with `completedZeta_ne_zero_of_re_eq_zero_of_im_ne_zero`; `z.im ≠ 0` follows from `hU` and `U ≤ z.im`.
3. Exclude `z.re = 1` in the same way with `completedZeta_ne_zero_of_re_eq_one_of_im_ne_zero`.
4. Apply `completedZeta_eq_zero_iff_riemannZeta_eq_zero_of_mem_criticalStrip` to obtain the zeta zero and strict real-part inequalities.
5. Exclude `z.im = U` and `z.im = T` with `hUgood` and `hTgood`; because `0 < z.im`, rewrite `|z.im|` using `abs_of_pos`.
6. Finish the forward direction with `mem_positiveNontrivialZerosBetween hU.le`.
7. In the reverse direction, unpack `mem_positiveNontrivialZerosBetween hU.le`; use `hTgood` to turn `z.im ≤ T` into `z.im < T`; then apply the critical-strip zero equivalence in the reverse direction.

Also prove:

```lean
private lemma zeroCountRectanglePoles_mem_interior ... :
  ∀ rho ∈ zeroCountRectanglePoles U T,
    0 < rho.re ∧ rho.re < 1 ∧ U < rho.im ∧ rho.im < T
```

from `mem_positiveNontrivialZerosBetween` and `hTgood`. This is the exact hypothesis expected by the boundary residue theorem.

- [ ] **Step 4: Build the analytic regularized remainder**

Let

```lean
let K := zeroCountRectangle U T
let poles := zeroCountRectanglePoles U T
let multiplicity : ℂ → ℕ := fun rho => analyticOrderNatAt riemannZeta rho
let raw : ℂ → ℂ := fun z =>
  logDeriv RiemannHypothesis.completedZeta z -
    ∑ rho ∈ poles, (multiplicity rho : ℂ) * (z - rho)⁻¹
let g := toMeromorphicNFOn raw K
```

Prove `AnalyticOnNhd ℂ g K` by applying
`ZeroFreeRegion.analyticOnNhd_toMeromorphicNFOn_logDeriv_sub_finset_principalParts` with:

- `differentiable_completedZeta.analytic` for analyticity on `K`;
- `completedZeta_zero_iff_mem_between_on_rectangle` for `hzero`;
- Task 2's multiplicity equivalence, cast back with `Nat.cast_analyticOrderNatAt`, for `horder`.

The poles are in the open strip, so the Task 2 multiplicity theorem applies to every member.

- [ ] **Step 5: Identify the boundary values and apply the rectangle residue theorem**

For every boundary point `z`, use the classification lemma to show `z ∉ poles` and `completedZeta z ≠ 0`. Prove `AnalyticAt ℂ raw z` from:

- analyticity of `logDeriv completedZeta` at a nonzero point via `hf.deriv.div hf hzero`;
- analyticity of each principal part because `z ≠ rho` for every `rho ∈ poles`.

Then obtain the actual pointwise equality `g z = raw z` with:

```lean
rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hrawMeromorphic hzK]
rw [toMeromorphicNFAt_eq_self.mpr hrawAnalytic.meromorphicNFAt]
```

Use that equality to prove the boundary integrand identity and apply:

```lean
MathlibAux.boundaryRectIntegral_eq_finite_simple_pole_residue_sum_of_differentiableOn
  poles (fun rho => (analyticOrderNatAt riemannZeta rho : ℂ))
  hregular.differentiableOn hpoles
```

Normalize the commuted principal-part product with `ring` or `simp [mul_comm]`. This proves `boundaryRectIntegral_logDeriv_completedZeta_eq_between_sum`.

- [ ] **Step 6: Rewrite the residue sum as the count difference**

Use `riemannZeroCount_sub_eq_between hUT.le`, cast the equality to `ℂ`, and normalize `Nat.cast_sum` to prove `boundaryRectIntegral_logDeriv_completedZeta_eq_zeroCount_sub`. Do not divide by `2 * pi * I`; the exported identity remains in integral form and avoids a new nonzero-denominator interface.

- [ ] **Step 7: Run focused builds and commit**

```bash
lake -Kjobs=1 build PrimeNumberTheorem.RiemannVonMangoldt.RectangleCount
lake -Kjobs=1 build Test.RiemannVonMangoldtContract
git add PrimeNumberTheorem/RiemannVonMangoldt/RectangleCount.lean Test/RiemannVonMangoldtContract.lean
git commit -m "feat(zeta): count zeros with a completed-zeta rectangle integral"
```

Expected: both builds pass. Any need for a new unproved argument-principle predicate is a feasibility failure, not permission to add an axiom.

---

### Task 5: Aggregate Module, Axiom Audit, and Feasibility Gate

**Files:**
- Create: `PrimeNumberTheorem/RiemannVonMangoldt.lean`
- Create: `Test/RiemannVonMangoldtAxiomAudit.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes: all Tasks 1-4.
- Produces: one import root and auditable final theorem surface; no new mathematics.

- [ ] **Step 1: Create the aggregate module**

```lean
import PrimeNumberTheorem.RiemannVonMangoldt.ZeroCount
import PrimeNumberTheorem.RiemannVonMangoldt.CompletedZeta
import PrimeNumberTheorem.RiemannVonMangoldt.GammaDecomposition
import PrimeNumberTheorem.RiemannVonMangoldt.RectangleCount
```

- [ ] **Step 2: Create the axiom audit**

Create `Test/RiemannVonMangoldtAxiomAudit.lean`:

```lean
import PrimeNumberTheorem.RiemannVonMangoldt

#print axioms PrimeNumberTheorem.RiemannVonMangoldt.riemannZeroCount_mono
#print axioms PrimeNumberTheorem.RiemannVonMangoldt.analyticOrderNatAt_completedZeta_eq_riemannZeta_of_mem_criticalStrip
#print axioms PrimeNumberTheorem.RiemannVonMangoldt.logDeriv_completedZeta_eq_zeta_add_gamma
#print axioms PrimeNumberTheorem.RiemannVonMangoldt.boundaryRectIntegral_logDeriv_completedZeta_eq_between_sum
#print axioms PrimeNumberTheorem.RiemannVonMangoldt.boundaryRectIntegral_logDeriv_completedZeta_eq_zeroCount_sub
```

Add `` `PrimeNumberTheorem.RiemannVonMangoldt `` and `` `Test.RiemannVonMangoldtAxiomAudit `` to the default roots in `lakefile.lean`.

- [ ] **Step 3: Run the three required focused builds**

```bash
lake -Kjobs=1 build PrimeNumberTheorem.RiemannVonMangoldt
lake -Kjobs=1 build Test.RiemannVonMangoldtContract
lake -Kjobs=1 build Test.RiemannVonMangoldtAxiomAudit
```

Expected: all three complete successfully. Inspect the axiom output and confirm that every printed theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.

- [ ] **Step 4: Run repository gates**

Run, in order and with `-Kjobs=1` where Lake is involved:

```bash
rg -n '\b(sorry|admit|axiom)\b' --glob '*.lean' --glob '!vendor/**' --glob '!.lake/**' --glob '!.worktrees/**'
python3 scripts/check-targets-consistent.py
python3 scripts/check-chain-gaps.py
./scripts/verify-baseline.sh
```

Expected:

- the source scan reports no newly introduced `sorry`, `admit`, or `axiom`;
- target inventory is consistent;
- the chain-gap check passes;
- `verify-baseline.sh` completes successfully.

If the machine is already running another full Lean build, wait for that build to finish before running `verify-baseline.sh`; do not run competing full builds and then interpret resource exhaustion as a proof failure.

- [ ] **Step 5: Record the feasibility decision without broadening claims**

Add a short commit-body note or branch handoff stating only:

```text
The feasibility spike closes the three approved interfaces: one-sided
multiplicity count, good-height rectangle count identity, and exact Gamma
decomposition. It does not prove the Riemann-von Mangoldt asymptotic or RH.
The next investment decision is whether to formalize the O(log T) boundary
argument estimate.
```

Do not edit the paper, README publication claims, target inventory, or chain-gap inventory unless an existing checker requires the new proved module to be registered.

- [ ] **Step 6: Commit the audit and aggregate**

```bash
git add PrimeNumberTheorem/RiemannVonMangoldt.lean Test/RiemannVonMangoldtAxiomAudit.lean lakefile.lean
git commit -m "test(zeta): audit Riemann-von Mangoldt spike"
```

- [ ] **Step 7: Final clean-state verification**

```bash
git status --short --branch
git log -5 --oneline --decorate
git diff --check integration/pnt-hardy-baseline...HEAD
```

Expected: clean `feat/riemann-von-mangoldt-spike`, a small sequence of scoped commits, and no whitespace errors.

---

## Self-Review Record

- Spec coverage: Task 1 proves the standard one-sided multiplicity count; Task 4 proves the rectangle residue identity and identifies it with the count difference; Task 3 proves the exact Gamma decomposition; Task 2 supplies only the completed-zeta facts required by those deliverables.
- Non-goal check: no task adds the full asymptotic, boundary `O(log T)`, all-height extension, general argument principle, zero-density theorem, zero-free region, RH implication, or publication rewrite.
- Type consistency: every count is `Nat`; the contour residue sum casts multiplicities and the final count difference to `ℂ`; all contour heights are `ℝ`; the integrand is `logDeriv RiemannHypothesis.completedZeta`.
- Execution-detail check: every public signature, dependency, red/green command, contour hypothesis, and residue normalization is fixed in this plan; implementation remains limited to filling the stated Lean proofs without changing the theorem surface.
