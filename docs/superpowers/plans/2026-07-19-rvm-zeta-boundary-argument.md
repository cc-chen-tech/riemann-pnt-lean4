# Riemann-von Mangoldt Zeta Boundary Argument Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove that the branch-free horizontal zeta argument variation is `O(log T)` at every good height `T >= 4`.

**Architecture:** First prove an exact arctangent formula and a uniform `pi` bound for the imaginary integral of one inverse factor. Then convert the shifted Jensen divisor finsum into a finite sum and bound its integrated imaginary part by `pi` times divisor mass. Finally combine that estimate with the existing regularized logarithmic-derivative bound on the fixed horizontal segment.

**Tech Stack:** Lean 4.29.1, Mathlib interval integrals and real arctangent calculus, existing `ZeroFreeRegion.ShiftedJensen`, existing `PrimeNumberTheorem.ExplicitFormulaResidues` good-height API.

## Global Constraints

- Work only on branch `feat/rvm-zeta-boundary-argument` in the existing `riemann-von-mangoldt-spike` worktree.
- Use `lake -Kjobs=1 build ...`; this Lake version does not accept `lake -j 1`.
- Export proved theorems only; do not add `def ... : Prop`, `sorry`, `admit`, or `axiom`.
- Do not assume logarithmic zero separation. The final estimate must hold for every good height `T >= 4`.
- Do not construct a continuous branch of `Complex.log`.
- Do not claim the good-height or all-height Riemann-von Mangoldt formula in this plan.

---

### Task 1: One Simple-Pole Angle Integral

**Files:**
- Create: `Test/HorizontalArgumentContract.lean`
- Create: `MathlibAux/HorizontalArgument.lean`
- Create: `Test/HorizontalArgumentAxiomAudit.lean`

**Interfaces:**
- Consumes: `Real.hasDerivAt_arctan`, `intervalIntegral.integral_deriv_eq_sub'`, `Real.neg_pi_div_two_lt_arctan`, and `Real.arctan_lt_pi_div_two`.
- Produces: `MathlibAux.intervalIntegral_im_inv_horizontal_sub_eq` and `MathlibAux.abs_intervalIntegral_im_inv_horizontal_sub_le_pi`.

- [ ] **Step 1: Write the failing contract**

Create `Test/HorizontalArgumentContract.lean`:

```lean
import MathlibAux.HorizontalArgument

open Complex MeasureTheory
open scoped Interval

#check MathlibAux.intervalIntegral_im_inv_horizontal_sub_eq
#check MathlibAux.abs_intervalIntegral_im_inv_horizontal_sub_le_pi

example {a b t : ℝ} {u : ℂ} (ht : t ≠ u.im) :
    |∫ sigma in a..b,
      (((((sigma : ℂ) + I * t) - u)⁻¹).im)| ≤ Real.pi :=
  MathlibAux.abs_intervalIntegral_im_inv_horizontal_sub_le_pi ht
```

- [ ] **Step 2: Run the contract and verify RED**

Run:

```bash
lake -Kjobs=1 build Test.HorizontalArgumentContract
```

Expected: FAIL because `MathlibAux.HorizontalArgument` does not exist.

- [ ] **Step 3: Prove the exact endpoint formula**

Create `MathlibAux/HorizontalArgument.lean` with namespace/import boilerplate and this public theorem shape:

```lean
theorem intervalIntegral_im_inv_horizontal_sub_eq
    {a b t : ℝ} {u : ℂ} (ht : t ≠ u.im) :
    (∫ sigma in a..b,
      (((((sigma : ℂ) + I * t) - u)⁻¹).im)) =
      -Real.arctan ((b - u.re) / (t - u.im)) +
        Real.arctan ((a - u.re) / (t - u.im)) := by
  let d : ℝ := t - u.im
  have hd : d ≠ 0 := sub_ne_zero.mpr ht
  let F : ℝ → ℝ := fun sigma =>
    -Real.arctan ((sigma - u.re) / d)
  have hpoint : ∀ sigma : ℝ,
      (((((sigma : ℂ) + I * t) - u)⁻¹).im) =
        -d / ((sigma - u.re) ^ 2 + d ^ 2) := by
    intro sigma
    simp only [Complex.inv_im, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_re, mul_im, I_re, I_im]
    field_simp
    ring
  have hderiv : deriv F = fun sigma : ℝ =>
      -d / ((sigma - u.re) ^ 2 + d ^ 2) := by
    funext sigma
    have h := Real.hasDerivAt_arctan
      ((sigma - u.re) / d)
    convert (h.comp sigma
      (((hasDerivAt_id sigma).sub_const u.re).div_const d)).neg.deriv using 1
    field_simp [hd]
    ring
  have hdiff : ∀ sigma ∈ Set.uIcc a b,
      DifferentiableAt ℝ F sigma := by
    intro sigma _
    fun_prop
  have hcont : ContinuousOn
      (fun sigma : ℝ => -d / ((sigma - u.re) ^ 2 + d ^ 2))
      (Set.uIcc a b) := by
    fun_prop
  rw [show (fun sigma : ℝ =>
      (((((sigma : ℂ) + I * t) - u)⁻¹).im)) =
      fun sigma => -d / ((sigma - u.re) ^ 2 + d ^ 2) by
        funext sigma; exact hpoint sigma]
  simpa [F, d] using
    intervalIntegral.integral_deriv_eq_sub' F hderiv hdiff hcont
```

The public theorem signature is fixed.  Proof-local algebra may use either the
displayed `simp` normal form or an equivalent `Complex.ext` followed by
`field_simp [hd]` and `ring`; hypotheses and conclusions must not change.

- [ ] **Step 4: Derive the uniform `pi` bound**

Add:

```lean
theorem abs_intervalIntegral_im_inv_horizontal_sub_le_pi
    {a b t : ℝ} {u : ℂ} (ht : t ≠ u.im) :
    |∫ sigma in a..b,
      (((((sigma : ℂ) + I * t) - u)⁻¹).im)| ≤ Real.pi := by
  rw [intervalIntegral_im_inv_horizontal_sub_eq ht]
  have ha_lo := Real.neg_pi_div_two_lt_arctan
    ((a - u.re) / (t - u.im))
  have ha_hi := Real.arctan_lt_pi_div_two
    ((a - u.re) / (t - u.im))
  have hb_lo := Real.neg_pi_div_two_lt_arctan
    ((b - u.re) / (t - u.im))
  have hb_hi := Real.arctan_lt_pi_div_two
    ((b - u.re) / (t - u.im))
  rw [abs_le]
  constructor <;> linarith
```

- [ ] **Step 5: Verify GREEN and audit axioms**

Create `Test/HorizontalArgumentAxiomAudit.lean`:

```lean
import MathlibAux.HorizontalArgument

#print axioms MathlibAux.intervalIntegral_im_inv_horizontal_sub_eq
#print axioms MathlibAux.abs_intervalIntegral_im_inv_horizontal_sub_le_pi
```

Run:

```bash
lake -Kjobs=1 build MathlibAux.HorizontalArgument Test.HorizontalArgumentContract Test.HorizontalArgumentAxiomAudit
```

Expected: PASS; axiom output is contained in `propext`, `Classical.choice`, and `Quot.sound`.

- [ ] **Step 6: Commit Task 1**

```bash
git add MathlibAux/HorizontalArgument.lean Test/HorizontalArgumentContract.lean Test/HorizontalArgumentAxiomAudit.lean
git commit -m "feat(contour): bound one horizontal pole angle"
```

### Task 2: Integrated Shifted-Divisor Principal Part

**Files:**
- Create: `PrimeNumberTheorem/RiemannVonMangoldt/ZetaArgumentBound.lean`
- Create: `Test/RiemannVonMangoldtZetaArgumentContract.lean`

**Interfaces:**
- Consumes: Task 1, `ZeroFreeRegion.exists_finsum_divisor_riemannZeta_shifted_disk_log_bound`, `ZeroFreeRegion.divisor_riemannZeta_closedBall_nonneg`, and `ExplicitFormulaResidues.isNontrivialZero_of_mem_shifted_divisor_support`.
- Produces: `abs_integral_im_shiftedDivisorPrincipalPart_le_pi_mul_mass`.

- [ ] **Step 1: Add the failing principal-part contract**

Create the contract importing the new module and checking:

```lean
#check PrimeNumberTheorem.RiemannVonMangoldt.
  abs_integral_im_shiftedDivisorPrincipalPart_le_pi_mul_mass
```

Run the contract and confirm failure due to the missing module/declaration.

- [ ] **Step 2: Define the local divisor and principal-part functions**

In `ZetaArgumentBound.lean`, define:

```lean
noncomputable def shiftedZetaDivisor (T : ℝ) : ℂ → ℤ :=
  MeromorphicOn.divisor riemannZeta
    (Metric.closedBall ((3 / 2 : ℂ) + I * T) (7 / 5 : ℝ))

noncomputable def shiftedDivisorPrincipalPart (T sigma : ℝ) : ℂ :=
  ∑ᶠ u, (shiftedZetaDivisor T u : ℂ) *
    ((((sigma : ℂ) + I * T) - u)⁻¹)
```

- [ ] **Step 3: Prove the finite integrated principal-part bound**

Export:

```lean
theorem abs_integral_im_shiftedDivisorPrincipalPart_le_pi_mul_mass
    {T : ℝ} (hT : 4 ≤ T)
    (hgood : ExplicitFormulaAux.goodHeight T) :
    |∫ sigma in (1 / 2 : ℝ)..2,
      (shiftedDivisorPrincipalPart T sigma).im| ≤
      Real.pi * ∑ᶠ u, (shiftedZetaDivisor T u : ℝ) := by
  classical
  let D := shiftedZetaDivisor T
  have hfinite : D.support.Finite :=
    D.finiteSupport
      (isCompact_closedBall ((3 / 2 : ℂ) + I * T) (7 / 5 : ℝ))
  let S := hfinite.toFinset
  have hsupport : D.support ⊆ S := hfinite.mem_toFinset.mpr
  have hD : ∀ u, 0 ≤ D u := by
    apply ZeroFreeRegion.divisor_riemannZeta_closedBall_nonneg
    intro u hu
    exact ZeroFreeRegion.closedBall_sigma_it_ne_one_of_height_add_le
      (z := u) (σ := (3 / 2 : ℝ)) (t := T) (R := (7 / 5 : ℝ))
      (H := T - 7 / 5) hu (by linarith) (by linarith)
  have hheight : ∀ u ∈ S, T ≠ u.im := by
    intro u huS hEq
    have huSupport : u ∈ D.support := hfinite.mem_toFinset.mp huS
    have huZero := ExplicitFormulaResidues.
      isNontrivialZero_of_mem_shifted_divisor_support
        (t := T) (by simpa [abs_of_nonneg (by linarith)] using hT)
        (by simpa [D, shiftedZetaDivisor] using huSupport)
    exact hgood u huZero (by simp [hEq, abs_of_nonneg (by linarith : 0 ≤ T)])
  rw [show shiftedDivisorPrincipalPart T = fun sigma =>
      ∑ u ∈ S, (D u : ℂ) *
        ((((sigma : ℂ) + I * T) - u)⁻¹) by
    funext sigma
    simp only [shiftedDivisorPrincipalPart, D]
    exact finsum_eq_sum_of_support_subset _ hsupport]
  simp_rw [map_sum, map_mul, Complex.ofReal_mul, Complex.ofReal_im,
    zero_mul, add_zero]
  rw [intervalIntegral.integral_finset_sum]
  · calc
      |∑ u ∈ S, (D u : ℝ) *
          ∫ sigma in (1 / 2 : ℝ)..2,
            (((((sigma : ℂ) + I * T) - u)⁻¹).im)| ≤
          ∑ u ∈ S, (D u : ℝ) * Real.pi := by
            apply (abs_sum_le_sum_abs _ _).trans
            apply Finset.sum_le_sum
            intro u hu
            rw [abs_mul, abs_of_nonneg (Int.cast_nonneg.mpr (hD u))]
            exact mul_le_mul_of_nonneg_left
              (MathlibAux.abs_intervalIntegral_im_inv_horizontal_sub_le_pi
                (hheight u hu))
              (Int.cast_nonneg.mpr (hD u))
      _ = Real.pi * ∑ᶠ u, (D u : ℝ) := by
        rw [Finset.sum_mul, mul_comm]
        congr 1
        exact (finsum_eq_sum_of_support_subset _ hsupport).symm
  · intro u hu
    exact (continuousOn_of_forall_continuousAt fun sigma => by
      have hne : ((sigma : ℂ) + I * T) - u ≠ 0 := by
        intro hz
        have him := congrArg Complex.im hz
        simp [hheight u hu] at him
      fun_prop).intervalIntegrable
```

The proof must derive `T ≠ u.im` from good height for each support point using `isNontrivialZero_of_mem_shifted_divisor_support`; it must not import the logarithmic-separation height selector.

- [ ] **Step 4: Verify Task 2 GREEN**

Run:

```bash
lake -Kjobs=1 build PrimeNumberTheorem.RiemannVonMangoldt.ZetaArgumentBound Test.RiemannVonMangoldtZetaArgumentContract
```

Expected: PASS for the principal-part declaration.

- [ ] **Step 5: Commit Task 2**

```bash
git add PrimeNumberTheorem/RiemannVonMangoldt/ZetaArgumentBound.lean Test/RiemannVonMangoldtZetaArgumentContract.lean
git commit -m "feat(zeta): bound integrated shifted divisor angles"
```

### Task 3: Assemble the Zeta Horizontal `O(log T)` Bound

**Files:**
- Modify: `PrimeNumberTheorem/RiemannVonMangoldt/ZetaArgumentBound.lean`
- Modify: `Test/RiemannVonMangoldtZetaArgumentContract.lean`
- Create: `Test/RiemannVonMangoldtZetaArgumentAxiomAudit.lean`
- Modify: `PrimeNumberTheorem/RiemannVonMangoldt.lean`

**Interfaces:**
- Consumes: Task 2 and both shifted Jensen logarithmic bounds.
- Produces: `zetaHorizontalArgumentVariation` and `exists_abs_zetaHorizontalArgumentVariation_le_log`.

- [ ] **Step 1: Extend the contract and verify RED**

Add exact `#check`/`example` declarations:

```lean
#check PrimeNumberTheorem.RiemannVonMangoldt.zetaHorizontalArgumentVariation
#check PrimeNumberTheorem.RiemannVonMangoldt.
  exists_abs_zetaHorizontalArgumentVariation_le_log

example : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 4 ≤ T →
    ExplicitFormulaAux.goodHeight T →
    |PrimeNumberTheorem.RiemannVonMangoldt.
      zetaHorizontalArgumentVariation T| ≤
      C * (1 + Real.log (T + 5)) :=
  PrimeNumberTheorem.RiemannVonMangoldt.
    exists_abs_zetaHorizontalArgumentVariation_le_log
```

Run the contract and confirm failure because the two declarations are missing.

- [ ] **Step 2: Define the branch-free variation**

```lean
noncomputable def zetaHorizontalArgumentVariation (T : ℝ) : ℝ :=
  ∫ sigma in (1 / 2 : ℝ)..2,
    (logDeriv riemannZeta ((sigma : ℂ) + I * T)).im
```

- [ ] **Step 3: Prove the regularized-part integral bound**

Inside the final theorem, obtain constants `Breg` and `Bmass`.  For each good `T >= 4`, let `L = 1 + log (T + 5)`, `D = shiftedZetaDivisor T`, and `P = shiftedDivisorPrincipalPart T`.  Prove pointwise on `[1/2,2]`:

```lean
‖logDeriv riemannZeta z - P T sigma‖ ≤ Breg * L
```

using the radius-`1` geometry and good-height nonvanishing.  Then use
`intervalIntegral.norm_integral_le_of_norm_le` (or the scalar absolute analogue) to prove:

```lean
|∫ sigma in (1 / 2 : ℝ)..2,
  (logDeriv riemannZeta (((sigma : ℂ) + I * T)) -
    P T sigma).im| ≤ (3 / 2) * Breg * L.
```

- [ ] **Step 4: Assemble the logarithmic bound**

Use interval-integral additivity after establishing interval integrability of the regularized and finite principal pieces.  Apply Task 2 and the mass estimate.  Choose

```lean
C = (3 / 2) * Breg + Real.pi * Bmass
```

and prove the exact public theorem from the design.  Confirm `0 <= C` using nonnegativity of both Jensen constants and `Real.pi_pos.le`.

- [ ] **Step 5: Import, audit, and run focused verification**

Import `ZetaArgumentBound` from `PrimeNumberTheorem/RiemannVonMangoldt.lean` and create:

```lean
import PrimeNumberTheorem.RiemannVonMangoldt.ZetaArgumentBound

#print axioms PrimeNumberTheorem.RiemannVonMangoldt.
  abs_integral_im_shiftedDivisorPrincipalPart_le_pi_mul_mass
#print axioms PrimeNumberTheorem.RiemannVonMangoldt.
  exists_abs_zetaHorizontalArgumentVariation_le_log
```

Run:

```bash
lake -Kjobs=1 build \
  MathlibAux.HorizontalArgument \
  Test.HorizontalArgumentContract \
  Test.HorizontalArgumentAxiomAudit \
  PrimeNumberTheorem.RiemannVonMangoldt.ZetaArgumentBound \
  Test.RiemannVonMangoldtZetaArgumentContract \
  Test.RiemannVonMangoldtZetaArgumentAxiomAudit \
  PrimeNumberTheorem.RiemannVonMangoldt
rg -n "\bsorry\b|\badmit\b|^\s*axiom\b" \
  MathlibAux/HorizontalArgument.lean \
  PrimeNumberTheorem/RiemannVonMangoldt/ZetaArgumentBound.lean \
  Test/HorizontalArgumentContract.lean \
  Test/HorizontalArgumentAxiomAudit.lean \
  Test/RiemannVonMangoldtZetaArgumentContract.lean \
  Test/RiemannVonMangoldtZetaArgumentAxiomAudit.lean
git diff --check
```

Expected: all builds pass; source scan has no matches; axiom output is contained in the approved foundational allowlist.

- [ ] **Step 6: Commit Task 3**

```bash
git add PrimeNumberTheorem/RiemannVonMangoldt.lean \
  PrimeNumberTheorem/RiemannVonMangoldt/ZetaArgumentBound.lean \
  Test/RiemannVonMangoldtZetaArgumentContract.lean \
  Test/RiemannVonMangoldtZetaArgumentAxiomAudit.lean
git commit -m "feat(zeta): prove horizontal argument logarithmic bound"
```
