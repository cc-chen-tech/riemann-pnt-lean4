# Completed L-Function Contour Core Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Extract the verified completed/base-function compatibility and logarithmic-derivative rectangle count into reusable Lean 4 interfaces, then make the existing completed-zeta count theorem consume those interfaces without changing its public signature.

**Architecture:** A lightweight `CompletedLFunctionContourData` record carries only strip-level zero and analytic-order compatibility. A separate function-level theorem regularizes a logarithmic derivative by subtracting finite principal parts and evaluates its rectangle boundary integral. The zeta module constructs the first record value and retains all zeta-specific finite-zero and good-height work.

**Tech Stack:** Lean 4, Mathlib complex analysis, `analyticOrderAt` / `analyticOrderNatAt`, repository `toMeromorphicNFOn` regularization, repository axis-parallel boundary integrals, Lake focused builds.

## Global Constraints

- Preserve the signatures of `boundaryRectIntegral_logDeriv_completedZeta_eq_between_sum` and `boundaryRectIntegral_logDeriv_completedZeta_eq_zeroCount_sub`.
- Do not add Gamma factors, conductors, root numbers, functional equations, Euler products, or Dirichlet-series fields to the completed-function record.
- Do not introduce a second multiplicity definition; use `analyticOrderNatAt`.
- Do not add a new residue theorem, contour definition, or unproved `Prop` target.
- Changed proof sources must contain no `sorry`, `admit`, or `axiom`.
- Focused builds run serially with `lake -Kjobs=1 build ...`.
- Audited declarations may depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- This plan does not claim or prove the final Riemann-von Mangoldt asymptotic or the zeta boundary estimate `O(log T)`.

---

### Task 1: Completed-Function Strip Interface

**Files:**
- Create: `PrimeNumberTheorem/LFunction/CompletedContourData.lean`
- Create: `Test/CompletedLFunctionContourContract.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes: Mathlib `AnalyticOnNhd`, `analyticOrderAt`, and `analyticOrderNatAt`.
- Produces: `PrimeNumberTheorem.LFunction.CompletedLFunctionContourData` and `CompletedLFunctionContourData.analyticOrderNatAt_completed_eq_base`.

- [ ] **Step 1: Write the failing contract and register its Lake root**

Create `Test/CompletedLFunctionContourContract.lean`:

```lean
import PrimeNumberTheorem.LFunction.CompletedContourData

open Complex

namespace PrimeNumberTheorem.LFunction

example (data : CompletedLFunctionContourData) {s : ℂ}
    (hleft : data.leftBoundary < s.re)
    (hright : s.re < data.rightBoundary) :
    data.completed s = 0 ↔ data.base s = 0 :=
  data.completed_eq_zero_iff_base_eq_zero (s := s) hleft hright

example (data : CompletedLFunctionContourData) {s : ℂ}
    (hleft : data.leftBoundary < s.re)
    (hright : s.re < data.rightBoundary) :
    analyticOrderNatAt data.completed s = analyticOrderNatAt data.base s :=
  data.analyticOrderNatAt_completed_eq_base (s := s) hleft hright

end PrimeNumberTheorem.LFunction
```

Add `` `PrimeNumberTheorem.LFunction.CompletedContourData `` and
`` `Test.CompletedLFunctionContourContract `` immediately before the existing
Riemann-von Mangoldt roots in `lakefile.lean`.

- [ ] **Step 2: Run the contract and verify the RED state**

Run:

```bash
lake -Kjobs=1 build Test.CompletedLFunctionContourContract
```

Expected: failure because `PrimeNumberTheorem/LFunction/CompletedContourData.lean` does not exist.

- [ ] **Step 3: Implement the minimal record and derived natural-order lemma**

Create `PrimeNumberTheorem/LFunction/CompletedContourData.lean`:

```lean
import Mathlib.Analysis.Analytic.Order

open Complex Set

namespace PrimeNumberTheorem.LFunction

structure CompletedLFunctionContourData where
  base : ℂ → ℂ
  completed : ℂ → ℂ
  leftBoundary : ℝ
  rightBoundary : ℝ
  left_lt_right : leftBoundary < rightBoundary
  analytic_completed : AnalyticOnNhd ℂ completed Set.univ
  completed_eq_zero_iff_base_eq_zero :
    ∀ {s : ℂ}, leftBoundary < s.re → s.re < rightBoundary →
      (completed s = 0 ↔ base s = 0)
  analyticOrderAt_completed_eq_base :
    ∀ {s : ℂ}, leftBoundary < s.re → s.re < rightBoundary →
      (analyticOrderAt completed s = analyticOrderAt base s)

namespace CompletedLFunctionContourData

theorem analyticOrderNatAt_completed_eq_base
    (data : CompletedLFunctionContourData) {s : ℂ}
    (hleft : data.leftBoundary < s.re)
    (hright : s.re < data.rightBoundary) :
    analyticOrderNatAt data.completed s = analyticOrderNatAt data.base s :=
  congrArg ENat.toNat
    (data.analyticOrderAt_completed_eq_base hleft hright)

end CompletedLFunctionContourData
end PrimeNumberTheorem.LFunction
```

- [ ] **Step 4: Run focused GREEN checks**

Run:

```bash
lake -Kjobs=1 build PrimeNumberTheorem.LFunction.CompletedContourData
lake -Kjobs=1 build Test.CompletedLFunctionContourContract
```

Expected: both targets build successfully.

- [ ] **Step 5: Commit the completed-function interface**

```bash
git add lakefile.lean PrimeNumberTheorem/LFunction/CompletedContourData.lean Test/CompletedLFunctionContourContract.lean
git commit -m "feat(lfunction): add completed contour data interface"
```

### Task 2: Generic Logarithmic-Derivative Rectangle Count

**Files:**
- Create: `MathlibAux/LogDerivArgumentPrinciple.lean`
- Create: `Test/LogDerivArgumentPrincipleContract.lean`
- Create: `Test/LogDerivArgumentPrincipleAxiomAudit.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes: `ZeroFreeRegion.analyticOnNhd_toMeromorphicNFOn_logDeriv_sub_finset_principalParts`, `ZeroFreeRegion.meromorphicOn_logDeriv_sub_finset_principalParts`, and `MathlibAux.boundaryRectIntegral_eq_finite_simple_pole_residue_sum_of_differentiableOn`.
- Produces: `MathlibAux.boundaryRectIntegral_logDeriv_eq_finite_zero_multiplicity_sum`.

- [ ] **Step 1: Write the failing theorem contract and register all roots**

Create `Test/LogDerivArgumentPrincipleContract.lean`:

```lean
import MathlibAux.LogDerivArgumentPrinciple

open Complex Set
open scoped BigOperators Interval

example {f : ℂ → ℂ} {x0 x1 y0 y1 : ℝ}
    (zeros : Finset ℂ) (multiplicity : ℂ → ℕ)
    (hf : AnalyticOnNhd ℂ f ([[x0, x1]] ×ℂ [[y0, y1]]))
    (hzero : ∀ z ∈ ([[x0, x1]] ×ℂ [[y0, y1]]),
      f z = 0 ↔ z ∈ zeros)
    (hinside : ∀ rho ∈ zeros,
      x0 < rho.re ∧ rho.re < x1 ∧ y0 < rho.im ∧ rho.im < y1)
    (horder : ∀ rho ∈ zeros,
      analyticOrderAt f rho = multiplicity rho) :
    MathlibAux.boundaryRectIntegral (logDeriv f) x0 x1 y0 y1 =
      (2 * Real.pi * I) *
        ∑ rho ∈ zeros, (multiplicity rho : ℂ) :=
  MathlibAux.boundaryRectIntegral_logDeriv_eq_finite_zero_multiplicity_sum
    zeros multiplicity hf hzero hinside horder
```

Create `Test/LogDerivArgumentPrincipleAxiomAudit.lean`:

```lean
import MathlibAux.LogDerivArgumentPrinciple

#print axioms MathlibAux.boundaryRectIntegral_logDeriv_eq_finite_zero_multiplicity_sum
```

Register the implementation, contract, and audit modules in `lakefile.lean`.

- [ ] **Step 2: Run the contract and verify the RED state**

Run:

```bash
lake -Kjobs=1 build Test.LogDerivArgumentPrincipleContract
```

Expected: failure because `MathlibAux/LogDerivArgumentPrinciple.lean` does not exist.

- [ ] **Step 3: Implement the generic regularization theorem**

Create `MathlibAux/LogDerivArgumentPrinciple.lean`. Define
`boundaryRectIntegral_logDeriv_eq_finite_zero_multiplicity_sum` with exactly the
contract signature. In its proof:

```lean
  classical
  let K : Set ℂ := [[x0, x1]] ×ℂ [[y0, y1]]
  let raw : ℂ → ℂ := fun z =>
    logDeriv f z -
      ∑ rho ∈ zeros, (multiplicity rho : ℂ) * (z - rho)⁻¹
  let g := toMeromorphicNFOn raw K
```

Establish the analytic remainder with:

```lean
  have hregular : AnalyticOnNhd ℂ g K :=
    ZeroFreeRegion.analyticOnNhd_toMeromorphicNFOn_logDeriv_sub_finset_principalParts
      hf zeros multiplicity hzero horder
  have hrawMeromorphic : MeromorphicOn raw K :=
    ZeroFreeRegion.meromorphicOn_logDeriv_sub_finset_principalParts
      hf.meromorphicOn zeros multiplicity
```

For every boundary point, use `hinside` to prove it is not in `zeros`, use
`hzero` to prove `f z ≠ 0`, show `logDeriv f` and every non-pole principal term
are analytic at `z`, and identify `g z = raw z` through
`toMeromorphicNFOn_eq_toMeromorphicNFAt` and `toMeromorphicNFAt_eq_self`.
Then apply:

```lean
  MathlibAux.boundaryRectIntegral_eq_finite_simple_pole_residue_sum_of_differentiableOn
    zeros (fun rho => (multiplicity rho : ℂ))
    hregular.differentiableOn hinside
```

The boundary congruence and factor-order normalization are the same finite-sum
algebra already verified in `RectangleCount.lean`; move that proof into this
module without weakening any hypotheses.

- [ ] **Step 4: Run focused GREEN checks and inspect axioms**

Run:

```bash
lake -Kjobs=1 build MathlibAux.LogDerivArgumentPrinciple
lake -Kjobs=1 build Test.LogDerivArgumentPrincipleContract
lake -Kjobs=1 build Test.LogDerivArgumentPrincipleAxiomAudit
```

Expected: all targets build; audit output lists only `propext`, `Classical.choice`, and `Quot.sound`.

- [ ] **Step 5: Commit the generic theorem**

```bash
git add lakefile.lean MathlibAux/LogDerivArgumentPrinciple.lean Test/LogDerivArgumentPrincipleContract.lean Test/LogDerivArgumentPrincipleAxiomAudit.lean
git commit -m "feat(contour): extract logarithmic derivative zero count"
```

### Task 3: Completed-Zeta Instance and Backconnection

**Files:**
- Modify: `PrimeNumberTheorem/RiemannVonMangoldt/CompletedZeta.lean`
- Modify: `PrimeNumberTheorem/RiemannVonMangoldt/RectangleCount.lean`
- Modify: `Test/RiemannVonMangoldtContract.lean`

**Interfaces:**
- Consumes: `CompletedLFunctionContourData` and `MathlibAux.boundaryRectIntegral_logDeriv_eq_finite_zero_multiplicity_sum`.
- Produces: `PrimeNumberTheorem.RiemannVonMangoldt.completedZetaContourData`; preserves both existing public rectangle-count theorems.

- [ ] **Step 1: Extend the existing contract before production edits**

Add to `Test/RiemannVonMangoldtContract.lean` after the completed-zeta differentiability check:

```lean
example :
    completedZetaContourData.base = riemannZeta ∧
      completedZetaContourData.completed = RiemannHypothesis.completedZeta ∧
      completedZetaContourData.leftBoundary = 0 ∧
      completedZetaContourData.rightBoundary = 1 := by
  rfl
```

- [ ] **Step 2: Run the contract and verify the RED state**

Run:

```bash
lake -Kjobs=1 build Test.RiemannVonMangoldtContract
```

Expected: failure with unknown identifier `completedZetaContourData`.

- [ ] **Step 3: Construct the zeta record value**

Import `PrimeNumberTheorem.LFunction.CompletedContourData` in
`CompletedZeta.lean` and define:

```lean
noncomputable def completedZetaContourData :
    LFunction.CompletedLFunctionContourData where
  base := riemannZeta
  completed := RiemannHypothesis.completedZeta
  leftBoundary := 0
  rightBoundary := 1
  left_lt_right := zero_lt_one
  analytic_completed := by
    intro s _hs
    exact differentiable_completedZeta.analyticAt s
  completed_eq_zero_iff_base_eq_zero := by
    intro s hs0 hs1
    exact completedZeta_eq_zero_iff_riemannZeta_eq_zero_of_mem_criticalStrip hs0 hs1
  analyticOrderAt_completed_eq_base := by
    intro s hs0 hs1
    exact analyticOrderAt_completedZeta_eq_riemannZeta_of_mem_criticalStrip hs0 hs1
```

- [ ] **Step 4: Refactor the zeta rectangle theorem to call the generic theorem**

Import `MathlibAux.LogDerivArgumentPrinciple` in `RectangleCount.lean`. Keep the
zeta-specific proofs `completedZeta_zero_iff_mem_between_on_rectangle`,
`zeroCountRectanglePoles_mem_interior`, and the conversion from zeta natural
multiplicity to completed-zeta analytic order. Replace the local definitions of
`raw` and `g`, the removable-singularity proof, the boundary equality proof,
and the final residue calculation by one invocation:

```lean
  exact MathlibAux.boundaryRectIntegral_logDeriv_eq_finite_zero_multiplicity_sum
    poles multiplicity hxiAnalytic hzero hpoles horder
```

Use `completedZetaContourData.completed_eq_zero_iff_base_eq_zero` in the finite
zero classification and
`completedZetaContourData.analyticOrderAt_completed_eq_base` in `horder`, so
the zeta result genuinely consumes both new abstractions.

- [ ] **Step 5: Run regression checks**

Run:

```bash
lake -Kjobs=1 build PrimeNumberTheorem.RiemannVonMangoldt
lake -Kjobs=1 build Test.RiemannVonMangoldtContract
lake -Kjobs=1 build Test.RiemannVonMangoldtAxiomAudit
```

Expected: public theorem contracts remain unchanged and all targets build.

- [ ] **Step 6: Commit the zeta backconnection**

```bash
git add PrimeNumberTheorem/RiemannVonMangoldt/CompletedZeta.lean PrimeNumberTheorem/RiemannVonMangoldt/RectangleCount.lean Test/RiemannVonMangoldtContract.lean
git commit -m "refactor(zeta): use generic completed contour core"
```

### Task 4: Abstraction-Stage Verification and Claim Audit

**Files:**
- Modify only if required by verification: `Test/LogDerivArgumentPrincipleAxiomAudit.lean`, `Test/RiemannVonMangoldtAxiomAudit.lean`

**Interfaces:**
- Consumes: all Task 1-3 modules.
- Produces: command-level evidence that the abstraction is independent of zeta, backconnected, and free of unapproved axioms.

- [ ] **Step 1: Run every required focused build serially**

```bash
lake -Kjobs=1 build PrimeNumberTheorem.LFunction.CompletedContourData
lake -Kjobs=1 build MathlibAux.LogDerivArgumentPrinciple
lake -Kjobs=1 build Test.CompletedLFunctionContourContract
lake -Kjobs=1 build Test.LogDerivArgumentPrincipleContract
lake -Kjobs=1 build Test.LogDerivArgumentPrincipleAxiomAudit
lake -Kjobs=1 build PrimeNumberTheorem.RiemannVonMangoldt
lake -Kjobs=1 build Test.RiemannVonMangoldtContract
lake -Kjobs=1 build Test.RiemannVonMangoldtAxiomAudit
```

Expected: all eight commands exit successfully.

- [ ] **Step 2: Audit changed sources and the backconnection**

Run:

```bash
rg -n '\b(sorry|admit|axiom)\b' \
  PrimeNumberTheorem/LFunction/CompletedContourData.lean \
  MathlibAux/LogDerivArgumentPrinciple.lean \
  PrimeNumberTheorem/RiemannVonMangoldt/CompletedZeta.lean \
  PrimeNumberTheorem/RiemannVonMangoldt/RectangleCount.lean \
  Test/CompletedLFunctionContourContract.lean \
  Test/LogDerivArgumentPrincipleContract.lean \
  Test/LogDerivArgumentPrincipleAxiomAudit.lean
rg -n 'boundaryRectIntegral_logDeriv_eq_finite_zero_multiplicity_sum' \
  PrimeNumberTheorem/RiemannVonMangoldt/RectangleCount.lean
```

Expected: the first command returns no matches; the second finds the generic theorem invocation in `RectangleCount.lean`.

- [ ] **Step 3: Verify the final diff and repository state**

```bash
git diff --check
git status --short --branch
git log --oneline --decorate -6
```

Expected: no whitespace errors; the branch contains three implementation commits after the design and plan commits; no unintended files are modified.

- [ ] **Step 4: Record any audit-only correction**

If an audit file required correction, commit only that correction:

```bash
git add Test/LogDerivArgumentPrincipleAxiomAudit.lean Test/RiemannVonMangoldtAxiomAudit.lean
git commit -m "test(contour): tighten abstraction axiom audit"
```

If no correction was required, do not create an empty commit.
