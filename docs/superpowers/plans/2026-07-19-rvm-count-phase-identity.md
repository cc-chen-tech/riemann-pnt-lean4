# Riemann-von Mangoldt Count/Phase Identity Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove the exact identity expressing the completed-zeta zero count between two good heights as a Gamma phase difference plus a logarithmically bounded zeta half-path argument.

**Architecture:** Fold the existing `[0,1]` completed-zeta rectangle with functional and conjugation symmetry, then deform its right half through the zero-free rectangle `[1,2]`. Split the resulting half-path using the existing logarithmic-derivative decomposition and control the remaining `Re(s)=2` zeta argument through the principal logarithm.

**Tech Stack:** Lean 4.29.1, Mathlib complex analysis and interval integrals, the repository's completed-zeta argument-principle API, Gamma phase API, shifted-Jensen zeta argument bound, and contract/axiom-audit tests.

## Global Constraints

- Do not add `sorry`, `admit`, or project axioms.
- Preserve the existing boundary orientation `bottom - top + I * right - I * left`.
- Reuse `boundaryRectIntegral_logDeriv_completedZeta_eq_zeroCount_sub`; do not reprove zero classification in a larger rectangle.
- The public result is an exact two-height identity, not the final Riemann-von Mangoldt asymptotic.
- Axiom audits may expose only `propext`, `Classical.choice`, and `Quot.sound`.

---

### Task 1: Completed-Zeta Conjugation and Log-Derivative Symmetry

**Files:**
- Create: `PrimeNumberTheorem/RiemannVonMangoldt/CompletedZetaSymmetry.lean`
- Create: `Test/RiemannVonMangoldtCompletedZetaSymmetryContract.lean`
- Create: `Test/RiemannVonMangoldtCompletedZetaSymmetryAxiomAudit.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes: `RiemannHypothesis.functional_equation`, `differentiable_completedZeta`, `Complex.deriv_conj_conj`, and the convergent zeta Dirichlet series.
- Produces: `completedZeta_conj`, `logDeriv_completedZeta_conj`, and `logDeriv_completedZeta_one_sub_conj`.

- [ ] **Step 1: Add a failing contract**

```lean
import PrimeNumberTheorem.RiemannVonMangoldt.CompletedZetaSymmetry

open Complex

#check PrimeNumberTheorem.RiemannVonMangoldt.completedZeta_conj
#check PrimeNumberTheorem.RiemannVonMangoldt.logDeriv_completedZeta_one_sub_conj
```

- [ ] **Step 2: Verify RED**

Run:

```bash
lake -Kjobs=1 build Test.RiemannVonMangoldtCompletedZetaSymmetryContract
```

Expected: failure because the module or declarations do not exist.

- [ ] **Step 3: Implement value symmetry by analytic continuation**

Expose the signatures:

```lean
theorem completedZeta_conj (s : ℂ) :
    RiemannHypothesis.completedZeta (conj s) =
      conj (RiemannHypothesis.completedZeta s)

theorem logDeriv_completedZeta_conj {s : ℂ}
    (hs : RiemannHypothesis.completedZeta s ≠ 0) :
    logDeriv RiemannHypothesis.completedZeta (conj s) =
      conj (logDeriv RiemannHypothesis.completedZeta s)

theorem logDeriv_completedZeta_one_sub_conj {s : ℂ}
    (hs : RiemannHypothesis.completedZeta s ≠ 0) :
    logDeriv RiemannHypothesis.completedZeta (1 - conj s) =
      -conj (logDeriv RiemannHypothesis.completedZeta s)
```

Prove the first identity on a neighborhood inside `Re(s)>1` from the Dirichlet-series representation and Gamma conjugation, then use `AnalyticOnNhd.eq_of_eventuallyEq`. Differentiate the resulting function identities for the other two theorems.

- [ ] **Step 4: Verify GREEN and audit axioms**

Run:

```bash
lake -Kjobs=1 build \
  PrimeNumberTheorem.RiemannVonMangoldt.CompletedZetaSymmetry \
  Test.RiemannVonMangoldtCompletedZetaSymmetryContract \
  Test.RiemannVonMangoldtCompletedZetaSymmetryAxiomAudit
```

Expected: success; axiom output contains only the permitted foundational axioms.

- [ ] **Step 5: Commit**

```bash
git add PrimeNumberTheorem/RiemannVonMangoldt/CompletedZetaSymmetry.lean \
  Test/RiemannVonMangoldtCompletedZetaSymmetryContract.lean \
  Test/RiemannVonMangoldtCompletedZetaSymmetryAxiomAudit.lean lakefile.lean
git commit -m "feat(zeta): prove completed zeta reflection symmetry"
```

### Task 2: Fold and Deform the Completed-Zeta Boundary

**Files:**
- Create: `PrimeNumberTheorem/RiemannVonMangoldt/HalfBoundary.lean`
- Create: `Test/RiemannVonMangoldtHalfBoundaryContract.lean`
- Create: `Test/RiemannVonMangoldtHalfBoundaryAxiomAudit.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes: Task 1 symmetry and `boundaryRectIntegral_logDeriv_completedZeta_eq_zeroCount_sub`.
- Produces: `completedZetaHalfBoundaryPhase` and `pi_mul_zeroCount_sub_eq_completedZetaHalfBoundaryPhase` with right edge at `Re(s)=2`.

- [ ] **Step 1: Add the failing public contract**

```lean
#check PrimeNumberTheorem.RiemannVonMangoldt.completedZetaHalfBoundaryPhase
#check PrimeNumberTheorem.RiemannVonMangoldt.pi_mul_zeroCount_sub_eq_completedZetaHalfBoundaryPhase
```

- [ ] **Step 2: Verify RED**

Run `lake -Kjobs=1 build Test.RiemannVonMangoldtHalfBoundaryContract` and confirm the missing declarations are the cause.

- [ ] **Step 3: Implement the phase functional and fold `[0,1]`**

Define:

```lean
noncomputable def completedZetaHalfBoundaryPhase (U T : ℝ) : ℝ :=
  (∫ sigma in (1 / 2 : ℝ)..2,
      (logDeriv RiemannHypothesis.completedZeta
        ((sigma : ℂ) + I * U)).im) -
  (∫ sigma in (1 / 2 : ℝ)..2,
      (logDeriv RiemannHypothesis.completedZeta
        ((sigma : ℂ) + I * T)).im) +
  ∫ t in U..T,
      (logDeriv RiemannHypothesis.completedZeta
        ((2 : ℂ) + I * t)).re
```

Use `intervalIntegral.integral_comp_sub_left` to pair the two horizontal halves and `Complex.integral_conj` to move conjugation through integrals. Extract the imaginary part of the existing rectangle-count identity and divide by `2`.

- [ ] **Step 4: Deform through `[1,2]`**

Prove completed zeta is nonzero on the closed positive-height strip `1 <= Re(s) <= 2`, derive analyticity of its logarithmic derivative there, and use `boundaryRectIntegral_eq_zero_of_differentiableOn`. Taking imaginary parts moves the right edge from `1` to `2` with no error.

- [ ] **Step 5: Verify GREEN, audit, and commit**

Run the focused three-target build for the module, contract, and axiom audit. Then commit with:

```bash
git commit -m "feat(contour): fold completed zeta count to a half boundary"
```

### Task 3: Uniform Right-Vertical Zeta Argument Bound

**Files:**
- Create: `PrimeNumberTheorem/RiemannVonMangoldt/RightVerticalZetaArgument.lean`
- Create: `Test/RiemannVonMangoldtRightVerticalZetaArgumentContract.lean`
- Create: `Test/RiemannVonMangoldtRightVerticalZetaArgumentAxiomAudit.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes: the zeta Dirichlet series for `Re(s)>1`, `riemannZeta_two`, and the interval fundamental theorem of calculus.
- Produces: `zetaRightVerticalArgumentVariation` and `abs_zetaRightVerticalArgumentVariation_le_pi`.

- [ ] **Step 1: Add a failing contract**

```lean
example (U T : ℝ) :
    |PrimeNumberTheorem.RiemannVonMangoldt.zetaRightVerticalArgumentVariation U T| ≤
      Real.pi :=
  PrimeNumberTheorem.RiemannVonMangoldt.abs_zetaRightVerticalArgumentVariation_le_pi U T
```

- [ ] **Step 2: Verify RED**

Run the contract build and confirm failure on the missing theorem.

- [ ] **Step 3: Prove the right-half-plane image**

Show

```lean
0 < (riemannZeta ((2 : ℂ) + I * t)).re
```

by bounding `|zeta(2+it)-1|` with `sum_{n>=2} n^-2 = zeta(2)-1 < 1`. This supplies zeta nonvanishing and excludes the principal-log branch cut.

- [ ] **Step 4: Integrate the principal logarithm derivative**

Define:

```lean
noncomputable def zetaRightVerticalArgumentVariation (U T : ℝ) : ℝ :=
  ∫ t in U..T,
    (logDeriv riemannZeta ((2 : ℂ) + I * t)).re
```

Apply the interval fundamental theorem to `Complex.log (riemannZeta (2+I*t))`. Identify the real part of `zeta'/zeta` with the derivative of its imaginary part and bound the endpoint difference by `pi`.

- [ ] **Step 5: Verify GREEN, audit, and commit**

Run the focused build and commit with:

```bash
git commit -m "feat(zeta): bound right vertical argument variation"
```

### Task 4: Exact Gamma/Zeta Count Identity and Logarithmic Remainder

**Files:**
- Create: `PrimeNumberTheorem/RiemannVonMangoldt/CountPhaseIdentity.lean`
- Create: `Test/RiemannVonMangoldtCountPhaseIdentityContract.lean`
- Create: `Test/RiemannVonMangoldtCountPhaseIdentityAxiomAudit.lean`
- Modify: `PrimeNumberTheorem/RiemannVonMangoldt.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes: Tasks 2-3, `logDeriv_completedZeta_eq_zeta_add_gamma`, `verticalGammaUnwrappedPhase`, and `exists_abs_zetaHorizontalArgumentVariation_le_log`.
- Produces: `zetaHalfPathArgument`, the exact count/phase theorem, and `exists_abs_zetaHalfPathArgument_le_log`.

- [ ] **Step 1: Add the failing exact-identity contract**

```lean
example {U T : ℝ} (hU : 4 ≤ U) (hUT : U < T)
    (hUgood : ExplicitFormulaAux.goodHeight U)
    (hTgood : ExplicitFormulaAux.goodHeight T) :
    Real.pi * ((riemannZeroCount T - riemannZeroCount U : ℕ) : ℝ) =
      HardyTheorem.verticalGammaUnwrappedPhase T -
        HardyTheorem.verticalGammaUnwrappedPhase U +
      zetaHalfPathArgument U T :=
  riemannZeroCount_sub_eq_gammaPhase_add_zetaHalfPathArgument
    hU hUT hUgood hTgood
```

- [ ] **Step 2: Verify RED**

Run the contract build and confirm the target theorem is absent.

- [ ] **Step 3: Decompose the half boundary**

Define:

```lean
noncomputable def zetaHalfPathArgument (U T : ℝ) : ℝ :=
  zetaHorizontalArgumentVariation U -
    zetaHorizontalArgumentVariation T +
    zetaRightVerticalArgumentVariation U T
```

Use the zero-boundary integral of the elementary and Gamma summands on
`[1/2,2] x [U,T]`. Prove the elementary critical-line real part is zero and
identify the Gamma critical-line integral with the exact difference of
`verticalGammaUnwrappedPhase`.

- [ ] **Step 4: Prove the logarithmic remainder bound**

Expose:

```lean
theorem exists_abs_zetaHalfPathArgument_le_log :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U T : ℝ, 4 ≤ U → 4 ≤ T →
      ExplicitFormulaAux.goodHeight U →
      ExplicitFormulaAux.goodHeight T →
      |zetaHalfPathArgument U T| ≤
        C * (1 + Real.log (U + 5) + Real.log (T + 5))
```

Combine the two horizontal logarithmic estimates and the vertical `pi` bound by the triangle inequality; enlarge the nonnegative constant once.

- [ ] **Step 5: Verify aggregate module and audits**

Run:

```bash
lake -Kjobs=1 build \
  PrimeNumberTheorem.RiemannVonMangoldt.CountPhaseIdentity \
  Test.RiemannVonMangoldtCountPhaseIdentityContract \
  Test.RiemannVonMangoldtCountPhaseIdentityAxiomAudit \
  PrimeNumberTheorem.RiemannVonMangoldt
rg -n "\bsorry\b|\badmit\b|^\s*axiom\b" \
  PrimeNumberTheorem/RiemannVonMangoldt Test
git diff --check
```

Expected: focused build succeeds, scans return no new proof holes, and diff check is clean.

- [ ] **Step 6: Commit**

```bash
git commit -m "feat(zeta): connect zero count to Gamma and zeta phases"
```
