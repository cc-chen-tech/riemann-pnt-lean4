# Dynamic Zero Transfer Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove a machine-checked, bidirectional transfer framework in which finite real-part layers and a dynamic truncation height control the PNT upper error, while nonzero rightmost-cluster energy produces quantitative oscillation witnesses.

**Architecture:** The implementation first proves an explicit finite-layer norm budget independent of zeta. A second module connects this budget and an admissible height schedule to a truncated explicit formula, with Carlson supplied through a separate density adapter. A third module converts the existing rightmost-zero-package mean-square lower bound into witness scales. A facade then returns upper and lower conclusions without conflating their hypotheses.

**Tech Stack:** Lean 4, Mathlib finite sums and normed spaces, existing `PrimeNumberTheorem` zero-density, explicit-formula, Pintz-envelope, and zero-forced-oscillation modules.

## Global Constraints

- Work only in `/Users/luicy/AI/Riemann/riemann-pnt-lean4/.worktrees/explicit-formula-unified-next` on branch `feat/explicit-formula-unified-next`.
- Preserve the half-open real-part convention `lo < re z ∧ re z ≤ hi`.
- Keep Carlson out of the generic layer-budget theorem; expose it through an adapter.
- Treat dynamic-height optimality as an explicit certificate, not an inferred global minimizer.
- The lower theorem first proves unsigned `Omega`; `Omega_plus_minus` requires an explicit sign-balance hypothesis.
- Do not describe any theorem here as RH, an RH criterion, or a proof of a Vinogradov-Korobov boundary.
- Report inherited analytic axioms separately from axioms introduced by new files.

---

### Task 1: Finite Layer Budget Contract and Core Theorem

**Files:**

- Create: `PrimeNumberTheorem/ZeroDensityLayerBudget.lean`
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetContract.lean`

**Interfaces:**

- Consumes: finite zero sets, a real-part map, a normed additive target, and per-layer count/kernel bounds.
- Produces:

```lean
def realPartLayer
    (zeros : Finset ρ) (re : ρ → ℝ) (lo hi : ℝ) : Finset ρ

structure LayerCertificate
    (ρ E : Type*) [DecidableEq ρ] [NormedAddCommGroup E] where
  tail : Finset ρ
  layerCount : ℕ
  layer : Fin layerCount → Finset ρ
  pairwise_disjoint :
    ∀ ⦃i j⦄, i ≠ j → Disjoint (layer i) (layer j)
  sum_decomposition :
    ∀ term : ρ → E,
      ∑ z ∈ tail, term z = ∑ i, ∑ z ∈ layer i, term z

def layeredTailBudget
    (C : LayerCertificate ρ E)
    (occupancy kernelWeight : Fin C.layerCount → ℝ) : ℝ

theorem norm_tail_sum_le_layeredTailBudget
    (C : LayerCertificate ρ E)
    (term : ρ → E)
    (occupancy kernelWeight : Fin C.layerCount → ℝ)
    (hoccupancy : ∀ i, (C.layer i).card ≤ occupancy i)
    (hkernel : ∀ i z, z ∈ C.layer i → ‖term z‖ ≤ kernelWeight i)
    (hocc_nonneg : ∀ i, 0 ≤ occupancy i)
    (hkernel_nonneg : ∀ i, 0 ≤ kernelWeight i) :
    ‖∑ z ∈ C.tail, term z‖ ≤
      layeredTailBudget C occupancy kernelWeight
```

- [ ] **Step 1: Write the failing contract**

Create `PrimeNumberTheorem/ZeroDensityLayerBudgetContract.lean`:

```lean
import PrimeNumberTheorem.ZeroDensityLayerBudget

open scoped BigOperators

namespace PrimeNumberTheorem

example :
    realPartLayer ({0, 1, 2} : Finset ℕ) (fun n => (n : ℝ)) 0 2 = {1, 2} := by
  native_decide

example :
    layeredTailBudget
      ({
        tail := ∅
        layerCount := 0
        layer := Fin.elim0
        pairwise_disjoint := by simp
        sum_decomposition := by simp
      } : LayerCertificate ℕ ℝ)
      Fin.elim0 Fin.elim0 = 0 := by
  simp [layeredTailBudget]

end PrimeNumberTheorem
```

- [ ] **Step 2: Run the contract to verify RED**

Run:

```bash
lake env lean PrimeNumberTheorem/ZeroDensityLayerBudgetContract.lean
```

Expected: failure because `PrimeNumberTheorem.ZeroDensityLayerBudget` and its declarations do not exist.

- [ ] **Step 3: Implement the finite-layer primitives**

Create `PrimeNumberTheorem/ZeroDensityLayerBudget.lean` with the exact public declarations above. Implement:

```lean
def realPartLayer
    (zeros : Finset ρ) (re : ρ → ℝ) (lo hi : ℝ) : Finset ρ :=
  zeros.filter fun z => lo < re z ∧ re z ≤ hi

def layeredTailBudget
    (C : LayerCertificate ρ E)
    (occupancy kernelWeight : Fin C.layerCount → ℝ) : ℝ :=
  ∑ i, occupancy i * kernelWeight i
```

Prove `norm_tail_sum_le_layeredTailBudget` by:

1. rewrite with `C.sum_decomposition term`;
2. apply the triangle inequality to the outer finite sum;
3. apply the triangle inequality inside each layer;
4. bound each summand with `hkernel`;
5. rewrite the constant sum as `card * kernelWeight`;
6. use `hoccupancy` and nonnegativity.

- [ ] **Step 4: Run the focused contract to verify GREEN**

Run:

```bash
lake env lean PrimeNumberTheorem/ZeroDensityLayerBudgetContract.lean
```

Expected: exit code `0`.

- [ ] **Step 5: Add real-part strip certificate constructor**

Add:

```lean
structure RealPartLayering (ρ : Type*) [DecidableEq ρ] where
  zeros : Finset ρ
  re : ρ → ℝ
  cutoffCount : ℕ
  lower upper : Fin cutoffCount → ℝ
  strict_strip : ∀ i, lower i < upper i
  ordered :
    ∀ i j, i ≠ j →
      Disjoint
        (realPartLayer zeros re (lower i) (upper i))
        (realPartLayer zeros re (lower j) (upper j))
  covered :
    ∀ z ∈ zeros,
      ∃ i, z ∈ realPartLayer zeros re (lower i) (upper i)

def RealPartLayering.certificate
    (L : RealPartLayering ρ) : LayerCertificate ρ E
```

The constructor uses `covered` and `ordered` to prove the exact finite-sum decomposition. Add a three-zero/two-strip contract showing that a boundary zero belongs to the strip ending at that boundary and not to the next strip.

- [ ] **Step 6: Re-run the focused contract**

Run:

```bash
lake env lean PrimeNumberTheorem/ZeroDensityLayerBudgetContract.lean
```

Expected: exit code `0`.

- [ ] **Step 7: Commit**

```bash
git add PrimeNumberTheorem/ZeroDensityLayerBudget.lean \
  PrimeNumberTheorem/ZeroDensityLayerBudgetContract.lean
git commit -m "feat: prove finite zero-layer budget"
```

### Task 2: Density Majorants and Carlson Adapter

**Files:**

- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudget.lean`
- Create: `PrimeNumberTheorem/CarlsonLayerBudget.lean`
- Create: `PrimeNumberTheorem/CarlsonLayerBudgetContract.lean`

**Interfaces:**

- Consumes: `zeroDensityCount`, an abstract count majorant, a real-part layering, and per-strip kernel bounds.
- Produces:

```lean
def ZeroDensityMajorant
    (count : ℝ → ℝ → ℕ) (D : ℝ → ℝ → ℝ) : Prop :=
  ∀ σ T, (count σ T : ℝ) ≤ D σ T

def stripOccupancy
    (count : ℝ → ℝ → ℕ)
    (T : ℝ) (L : RealPartLayering ρ) (i : Fin L.cutoffCount) : ℕ

theorem stripOccupancy_le_densityDifference
    (hmono : Antitone fun σ => count σ T)
    (L : RealPartLayering ρ)

theorem carlson_layered_tail_bound
    {ρ : Type*} [DecidableEq ρ]
    (L : RealPartLayering ρ)
    (T : ℝ)
    (term : ρ → ℂ)
    (carlsonMajorant : Fin L.cutoffCount → ℝ)
    (kernelWeight : Fin L.cutoffCount → ℝ)
    (hCarlson :
      ∀ i, ((L.certificate.layer i).card : ℝ) ≤ carlsonMajorant i)
    (hkernel :
      ∀ i z, z ∈ L.certificate.layer i → ‖term z‖ ≤ kernelWeight i)
    (hmajorant_nonneg : ∀ i, 0 ≤ carlsonMajorant i)
    (hkernel_nonneg : ∀ i, 0 ≤ kernelWeight i) :
    ‖∑ ρ ∈ L.zeros, term ρ‖ ≤
      layeredTailBudget L.certificate
        carlsonMajorant
        kernelWeight
```

- [ ] **Step 1: Write a failing abstract-density contract**

The contract instantiates `ZeroDensityMajorant` with
`count σ T = 0` and `D σ T = 0`, then checks that every strip occupancy is
bounded by zero.

- [ ] **Step 2: Run the contract to verify RED**

Run:

```bash
lake env lean PrimeNumberTheorem/CarlsonLayerBudgetContract.lean
```

Expected: failure because the density adapter declarations are absent.

- [ ] **Step 3: Add the abstract density adapter**

Implement `ZeroDensityMajorant` and prove a safe occupancy bound using the
count at the strip's lower endpoint. Use a difference of counts only when the
project's monotonicity theorem supplies the required orientation; otherwise
retain the endpoint majorant to avoid an unjustified subtraction.

- [ ] **Step 4: Add the Carlson specialization**

In `CarlsonLayerBudget.lean`, map the actual zero finset and
`zeroDensityCount` from `ZeroDensityCount.lean` into the abstract majorant.
The public theorem must expose Carlson's existing range conditions and
constants verbatim.

- [ ] **Step 5: Run the focused contracts**

Run:

```bash
lake env lean PrimeNumberTheorem/ZeroDensityLayerBudgetContract.lean
lake env lean PrimeNumberTheorem/CarlsonLayerBudgetContract.lean
```

Expected: both exit with code `0`.

- [ ] **Step 6: Commit**

```bash
git add PrimeNumberTheorem/ZeroDensityLayerBudget.lean \
  PrimeNumberTheorem/CarlsonLayerBudget.lean \
  PrimeNumberTheorem/CarlsonLayerBudgetContract.lean
git commit -m "feat: adapt Carlson density to zero layers"
```

### Task 3: Dynamic Height and Explicit-Formula Upper Transfer

**Files:**

- Create: `PrimeNumberTheorem/DynamicExplicitFormulaUpper.lean`
- Create: `PrimeNumberTheorem/DynamicExplicitFormulaUpperContract.lean`

**Interfaces:**

- Consumes: a layered zero-tail estimate, the project's truncated explicit formula, and all imported height thresholds.
- Produces:

```lean
def AdmissibleHeight
    (heightThreshold : ℝ) (x T : ℝ) : Prop :=
  2 ≤ x ∧ heightThreshold ≤ T

structure DynamicHeightSchedule (x₀ heightThreshold : ℝ) where
  height : ℝ → ℝ
  admissible : ∀ x, x₀ ≤ x → AdmissibleHeight heightThreshold x (height x)

def explicitFormulaCost
    (layerCost truncationCost compactCost : ℝ → ℝ → ℝ)
    (x T : ℝ) : ℝ :=
  layerCost x T + truncationCost x T + compactCost x T

def IsOptimalHeight
    (cost : ℝ → ℝ → ℝ)
    (admissible : ℝ → ℝ → Prop)
    (T : ℝ → ℝ) : Prop :=
  ∀ x, admissible x (T x) ∧
    ∀ U, admissible x U → cost x (T x) ≤ cost x U

theorem dynamic_explicit_formula_upper
    {pntError : ℝ → ℂ}
    {layerCost truncationCost compactCost : ℝ → ℝ → ℝ}
    {x₀ heightThreshold : ℝ}
    (schedule : DynamicHeightSchedule x₀ heightThreshold)
    (hformula : ∀ x T, AdmissibleHeight heightThreshold x T →
      ‖pntError x‖ ≤ explicitFormulaCost layerCost truncationCost compactCost x T) :
    ∀ x, x₀ ≤ x →
      ‖pntError x‖ ≤
        explicitFormulaCost layerCost truncationCost compactCost x
          (schedule.height x)

theorem optimal_height_upper
    {pntError : ℝ → ℂ}
    {cost : ℝ → ℝ → ℝ}
    {admissible : ℝ → ℝ → Prop}
    {T : ℝ → ℝ}
    (hopt : IsOptimalHeight cost admissible T)
    (hbound : ∀ x U, admissible x U → ‖pntError x‖ ≤ cost x U) :
    ∀ x U, admissible x U →
      ‖pntError x‖ ≤ cost x (T x) ∧ cost x (T x) ≤ cost x U
```

- [ ] **Step 1: Write the failing dynamic-height contract**

Use `cost x T = T + 1 / T`, admissibility `1 ≤ T`, and constant schedule
`T x = 1`. The contract checks generic specialization and comparison with
every admissible `U` under an explicitly supplied optimality proof.

- [ ] **Step 2: Run the contract to verify RED**

Run:

```bash
lake env lean PrimeNumberTheorem/DynamicExplicitFormulaUpperContract.lean
```

Expected: failure because the dynamic upper module does not exist.

- [ ] **Step 3: Implement schedule, cost, and optimality certificate**

Implement the declarations above without importing zeta-specific files.
Prove the two transfer lemmas by direct specialization and transitivity.

- [ ] **Step 4: Connect the truncated explicit formula**

Import `ExplicitFormulaTruncated.lean` and `CarlsonLayerBudget.lean`. Add a
zeta-specific theorem whose assumptions are exactly:

1. the imported explicit-formula identity;
2. a Carlson layered-tail bound;
3. the compact-height complementary contribution;
4. the truncation remainder;
5. an admissible dynamic schedule.

The conclusion must display all three costs at `T x`; it must not hide them in
an existential constant.

- [ ] **Step 5: Run the focused contract**

Run:

```bash
lake env lean PrimeNumberTheorem/DynamicExplicitFormulaUpperContract.lean
```

Expected: exit code `0`.

- [ ] **Step 6: Commit**

```bash
git add PrimeNumberTheorem/DynamicExplicitFormulaUpper.lean \
  PrimeNumberTheorem/DynamicExplicitFormulaUpperContract.lean
git commit -m "feat: add dynamic explicit-formula upper transfer"
```

### Task 4: Finite Rightmost-Cluster Anti-Cancellation

**Files:**

- Create: `PrimeNumberTheorem/RightmostClusterAntiCancellation.lean`
- Create: `PrimeNumberTheorem/RightmostClusterAntiCancellationContract.lean`

**Interfaces:**

- Consumes: a finite trigonometric zero package and the existing mean-square lower bound in `ZeroForcedOscillation.lean`.
- Produces:

```lean
structure ClusterMeanSquareCertificate where
  package : ℝ → ℂ
  start : ℝ
  length : ℝ
  energy : ℝ
  hlength : 0 < length
  henergy : 0 < energy
  integrable :
    IntegrableOn (fun t => ‖package t‖ ^ 2)
      (Set.Icc start (start + length))
  meanSquareLower :
    energy * length ≤
      ∫ t in Set.Icc start (start + length), ‖package t‖ ^ 2

theorem exists_cluster_witness
    (C : ClusterMeanSquareCertificate) :
    ∃ t ∈ Set.Icc C.start (C.start + C.length),
      Real.sqrt C.energy ≤ ‖C.package t‖

theorem unsigned_omega_of_cluster_witnesses
    (C : ℝ → ClusterMeanSquareCertificate)
    (hstart : Tendsto (fun X => (C X).start) atTop atTop) :
    ∀ X, ∃ t, X ≤ t ∧
      Real.sqrt (C X).energy ≤ ‖(C X).package t‖
```

- [ ] **Step 1: Write the failing one-frequency contract**

Instantiate the public witness interface with package
`fun t => Complex.exp (Complex.I * t)` and energy `1`. The contract checks
that the theorem returns a point where the norm is at least `1`.

- [ ] **Step 2: Run the contract to verify RED**

Run:

```bash
lake env lean PrimeNumberTheorem/RightmostClusterAntiCancellationContract.lean
```

Expected: failure because the anti-cancellation module does not exist.

- [ ] **Step 3: Prove mean-square to pointwise witness**

Prove by contradiction: if every point in the interval has squared norm
strictly below the energy, interval monotonicity gives an integral strictly
below `energy * length`, contradicting `meanSquareLower`. Use the exact
interval-integral representation already present in
`ZeroForcedOscillation.lean`; if it uses a normalized average, adapt the
certificate declaration to that normalization rather than reproving measure
theory.

- [ ] **Step 4: Connect the existing zero-package theorem**

Add a constructor from the maximal-real-part zero package and the theorem at
`ZeroForcedOscillation.lean:336`. The constructor records coefficient energy
and produces `ClusterMeanSquareCertificate`. Prove the unbounded witness
statement by choosing a certificate with start beyond the requested scale.

- [ ] **Step 5: Add lower transfer with complementary error**

Using `ZeroForcedOscillationComplementaryBound.lean`, prove:

```lean
theorem pnt_error_lower_of_cluster_gap
    (hmain : A ≤ ‖mainPackage t‖)
    (hcomplement : ‖complement t‖ ≤ B)
    (hremainder : ‖remainder t‖ ≤ R)
    (hgap : B + R < A) :
    A - B - R ≤ ‖pntError t‖
```

The proof is a reverse triangle inequality. Its zero-package specialization
must retain the explicit positive gap `A - B - R`.

- [ ] **Step 6: Run the focused contract**

Run:

```bash
lake env lean PrimeNumberTheorem/RightmostClusterAntiCancellationContract.lean
```

Expected: exit code `0`.

- [ ] **Step 7: Commit**

```bash
git add PrimeNumberTheorem/RightmostClusterAntiCancellation.lean \
  PrimeNumberTheorem/RightmostClusterAntiCancellationContract.lean \
  PrimeNumberTheorem/ZeroForcedOscillationComplementaryBound.lean
git commit -m "feat: prove rightmost-cluster anti-cancellation"
```

### Task 5: Unified Bidirectional Facade

**Files:**

- Replace: `PrimeNumberTheorem/ZeroForcingUnifiedTransfer.lean`
- Create: `PrimeNumberTheorem/ZeroForcingUnifiedTransferContract.lean`

**Interfaces:**

- Consumes: the dynamic upper theorem and the rightmost-cluster lower theorem.
- Produces:

```lean
structure DynamicUpperConclusion
    (pntError : ℝ → ℂ) (cost : ℝ → ℝ) (x₀ : ℝ) where
  bound : ∀ x, x₀ ≤ x → ‖pntError x‖ ≤ cost x

structure OscillationLowerConclusion
    (pntError : ℝ → ℂ) (amplitude : ℝ → ℝ) where
  witnesses :
    ∀ X, ∃ x, X ≤ x ∧ amplitude x ≤ ‖pntError x‖

theorem unified_dynamic_zero_transfer
    {pntError : ℝ → ℂ}
    {upperCost amplitude : ℝ → ℝ}
    {x₀ : ℝ}
    (upperInput : DynamicUpperConclusion pntError upperCost x₀)
    (lowerInput : OscillationLowerConclusion pntError amplitude) :
    DynamicUpperConclusion pntError
      (fun x => explicitFormulaCost ... x (T x)) ×
    OscillationLowerConclusion pntError amplitude
```

- [ ] **Step 1: Write a failing facade contract**

The contract supplies independent synthetic upper and lower hypotheses and
checks that both projections of `unified_dynamic_zero_transfer` recover the
expected bound and witness statements.

- [ ] **Step 2: Run the contract to verify RED**

Run:

```bash
lake env lean PrimeNumberTheorem/ZeroForcingUnifiedTransferContract.lean
```

Expected: failure because the experimental facade lacks the specified
structures and paired theorem.

- [ ] **Step 3: Replace the experimental skeleton**

Import:

```lean
import PrimeNumberTheorem.DynamicExplicitFormulaUpper
import PrimeNumberTheorem.RightmostClusterAntiCancellation
```

Retain `dynamic_zero_free_upper_bound` and
`dynamic_zero_forcing_lower_bound` only as compatibility lemmas. Add the
conclusion structures and paired theorem above. The proof constructs each
component separately; no upper hypothesis may be used in the lower proof and
no zero-existence hypothesis may be used in the upper proof.

- [ ] **Step 4: Run all focused contracts**

Run:

```bash
lake env lean PrimeNumberTheorem/ZeroDensityLayerBudgetContract.lean
lake env lean PrimeNumberTheorem/CarlsonLayerBudgetContract.lean
lake env lean PrimeNumberTheorem/DynamicExplicitFormulaUpperContract.lean
lake env lean PrimeNumberTheorem/RightmostClusterAntiCancellationContract.lean
lake env lean PrimeNumberTheorem/ZeroForcingUnifiedTransferContract.lean
```

Expected: all exit with code `0`.

- [ ] **Step 5: Commit**

```bash
git add PrimeNumberTheorem/ZeroForcingUnifiedTransfer.lean \
  PrimeNumberTheorem/ZeroForcingUnifiedTransferContract.lean
git commit -m "feat: unify dynamic upper and oscillation transfers"
```

### Task 6: Axiom and Aggregate Verification

**Files:**

- Create: `PrimeNumberTheorem/ZeroForcingUnifiedTransferAxiomAudit.lean`
- Modify only if required by project convention: the aggregate import file that lists `PrimeNumberTheorem` modules.

**Interfaces:**

- Consumes: all public facade theorems.
- Produces: build evidence and an explicit list of inherited versus newly introduced axioms.

- [ ] **Step 1: Create the axiom-audit file**

```lean
import PrimeNumberTheorem.ZeroForcingUnifiedTransfer

#print axioms PrimeNumberTheorem.norm_tail_sum_le_layeredTailBudget
#print axioms PrimeNumberTheorem.carlson_layered_tail_bound
#print axioms PrimeNumberTheorem.dynamic_explicit_formula_upper
#print axioms PrimeNumberTheorem.exists_cluster_witness
#print axioms PrimeNumberTheorem.unified_dynamic_zero_transfer
```

- [ ] **Step 2: Run the audit**

Run:

```bash
lake env lean PrimeNumberTheorem/ZeroForcingUnifiedTransferAxiomAudit.lean
```

Expected: exit code `0`; record every reported axiom and its originating
import.

- [ ] **Step 3: Scan changed theorem files for placeholders**

Run:

```bash
rg -n '\bsorry\b|admit|axiom ' \
  PrimeNumberTheorem/ZeroDensityLayerBudget.lean \
  PrimeNumberTheorem/CarlsonLayerBudget.lean \
  PrimeNumberTheorem/DynamicExplicitFormulaUpper.lean \
  PrimeNumberTheorem/RightmostClusterAntiCancellation.lean \
  PrimeNumberTheorem/ZeroForcingUnifiedTransfer.lean
```

Expected: no matches.

- [ ] **Step 4: Run the aggregate build**

Run:

```bash
lake build
```

Expected: exit code `0`.

- [ ] **Step 5: Commit the audit**

```bash
git add PrimeNumberTheorem/ZeroForcingUnifiedTransferAxiomAudit.lean
git commit -m "test: audit unified zero transfer axioms"
```

- [ ] **Step 6: Record completion evidence**

Report:

- branch and worktree;
- public theorem names;
- focused contract results;
- aggregate build result;
- new-file `sorry` scan;
- `#print axioms` output, separated into inherited and newly introduced
  assumptions;
- the remaining mathematical gap to an unconditional numerical
  `Omega_plus_minus` theorem.
