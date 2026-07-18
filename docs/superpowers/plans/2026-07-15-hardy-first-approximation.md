# Hardy First-Approximation Implementation Plan

> **Status:** Completed on `feat/hardy-first-approximation`. This is an
> archived implementation plan; unchecked boxes below are historical work
> items and are not current blockers.

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove `HardyTheorem.hardy_zeros_unbounded_target` unconditionally by comparing lower and upper bounds for the dyadic Hardy-Z integral.

**Architecture:** Specialize the first zeta approximation to the critical line and dyadic intervals, compare the exact Gamma phase with an explicit smooth phase, and prove first- and second-derivative oscillatory-integral estimates.  Assemble a linear lower bound and a `T^(3/4)` upper bound; bounded critical-line zeros then force an impossible constant-sign equality.

**Tech Stack:** Lean 4.29.1, Mathlib complex Gamma and zeta APIs, Bochner/interval integration, complex differentiation, asymptotic filters, finite sums.

## Global Constraints

- Do not add `sorry`, `admit`, custom axioms, or a new `def ... : Prop` route interface.
- The final theorem must prove the existing `hardy_zeros_unbounded_target` without hypotheses.
- Do not substitute the existing signed-moment or AFE targets for the final theorem.
- Intermediate estimates must concern actual functions and integrals, not conditional predicates.
- Do not claim RH or exclusion of the line `Re(s) = 1/3`.
- Keep this branch independent of `feat/pnt-dynamic-perron`.

---

### Task 1: Lock the unconditional final contract

**Files:**
- Create: `Test/HardyFirstApproximationContract.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes: `HardyTheorem.hardy_zeros_unbounded_target`, `HardyTheorem.hardy_theorem_target`
- Produces: compile-time contracts for `hardy_zeros_unbounded_target_proved` and `hardy_theorem_target_proved`

- [ ] **Step 1: Add the failing contract**

```lean
import RiemannPNT

example : HardyTheorem.hardy_zeros_unbounded_target :=
  HardyTheorem.hardy_zeros_unbounded_target_proved

example : HardyTheorem.hardy_theorem_target :=
  HardyTheorem.hardy_theorem_target_proved

example : HardyTheorem.hardy_zeros_unbounded_target :=
  RiemannPNT.API.hardy_zeros_unbounded_target_proved
```

Add `Test.HardyFirstApproximationContract` to the `roots` array immediately
after `HardyTheorem.AFE`.

- [ ] **Step 2: Verify RED**

Run:

```bash
lake build Test.HardyFirstApproximationContract
```

Expected: failure only because the three `..._proved` declarations are
unknown.  Fix imports or syntax until there are no other errors.

- [ ] **Step 3: Commit the contract**

```bash
git add Test/HardyFirstApproximationContract.lean lakefile.lean
git commit -m "test the unconditional Hardy theorem contract"
```

### Task 2: Prove the exact Hardy-Z norm and constant-sign integral identity

**Files:**
- Create: `HardyTheorem/HardyIntegralBasics.lean`

**Interfaces:**
- Consumes: `hardyZ`, `Gammaℝ_re_im_arg`,
  `completedRiemannZeta_critical_line_real`, `hardyZ_continuous`
- Produces: `abs_hardyZ_eq_norm_riemannZeta`,
  `abs_integral_hardyZ_eq_integral_abs_of_const_sign`

- [ ] **Step 1: State the exact norm identity**

```lean
import HardyTheorem

open Complex Filter Set Topology

namespace HardyTheorem

theorem abs_hardyZ_eq_norm_riemannZeta (t : ℝ) :
    |hardyZ t| = ‖riemannZeta ((1 / 2 : ℂ) + I * t)‖ := by
```

Use the existing proof of `hardyZ_zero_implies_zeta_zero` to extract the exact
identity

```text
hardyZ t = re(completedRiemannZeta s) / norm(GammaR s).
```

Use `completedRiemannZeta_critical_line_real` to replace the completed zeta by
a real number, `riemannZeta_def_of_ne_zero` to write it as `GammaR s * zeta s`,
and `norm_mul` plus positivity of `norm (GammaR s)` to cancel the Gamma norm.

- [ ] **Step 2: State the constant-sign dyadic integral identity**

```lean
theorem abs_integral_hardyZ_eq_integral_abs_of_const_sign
    {T : ℝ}
    (hpos : (∀ t ∈ Set.Icc T (2 * T), 0 ≤ hardyZ t) ∨
      (∀ t ∈ Set.Icc T (2 * T), hardyZ t ≤ 0)) :
    |∫ t in T..(2 * T), hardyZ t| =
      ∫ t in T..(2 * T), |hardyZ t| := by
```

In the positive case rewrite `abs_of_nonneg`; in the negative case rewrite
`abs_of_nonpos` and use `intervalIntegral.integral_neg`.  Obtain
integrability from `hardyZ_continuous`.

- [ ] **Step 3: Derive constant sign from bounded zeros**

```lean
theorem eventually_abs_integral_hardyZ_eq_integral_norm_zeta_of_bounded_zeros
    (hbounded : Bornology.IsBounded {t : ℝ | hardyZ t = 0}) :
    ∀ᶠ T : ℝ in atTop,
      |∫ t in T..(2 * T), hardyZ t| =
        ∫ t in T..(2 * T),
          ‖riemannZeta ((1 / 2 : ℂ) + I * t)‖ := by
```

Apply `hardyZ_eventually_const_sign_of_bounded_zeros`, raise the eventual sign
from points to the complete dyadic interval, apply Step 2, and rewrite the
integrand with Step 1.

- [ ] **Step 4: Verify and commit**

```bash
lake env lean HardyTheorem/HardyIntegralBasics.lean
git add HardyTheorem/HardyIntegralBasics.lean
git commit -m "prove the exact Hardy-Z integral identity"
```

### Task 3: Prove the first-derivative oscillatory-integral estimate

**Files:**
- Create: `HardyTheorem/OscillatoryIntegral.lean`

**Interfaces:**
- Consumes: Mathlib interval integration and derivatives
- Produces: `norm_integral_cexp_phase_le_of_monotone_deriv`

- [ ] **Step 1: Add the theorem statement**

```lean
import Mathlib

open Complex Set

namespace HardyTheorem.OscillatoryIntegral

theorem norm_integral_cexp_phase_le_of_monotone_deriv
    {F : ℝ → ℝ} {a b m : ℝ}
    (hab : a ≤ b) (hm : 0 < m)
    (hF : ContDiff ℝ 2 F)
    (hmono : MonotoneOn (deriv F) (Icc a b) ∨
      AntitoneOn (deriv F) (Icc a b))
    (haway : ∀ x ∈ Icc a b, m ≤ |deriv F x|) :
    ‖∫ x in a..b, Complex.exp (I * F x)‖ ≤ 4 / m := by
```

- [ ] **Step 2: Prove the positive-derivative case**

Split `haway` using the intermediate-value property of the continuous
derivative: on a connected interval the derivative cannot change sign while
its absolute value is at least `m`.  For `m ≤ F'`, integrate

```text
exp(iF) = (1 / (iF')) * deriv(exp(iF))
```

by parts.  Monotonicity of `F'` bounds the total variation of `1/F'`; both
boundary terms have norm at most `1/m`.  Record the resulting bound `4/m`.

- [ ] **Step 3: Reduce the negative-derivative case**

Apply Step 2 to `-F`, using

```lean
Complex.exp (I * (-F x)) = conj (Complex.exp (I * F x))
```

and invariance of the integral norm under conjugation.

- [ ] **Step 4: Add phase-specialization derivative identities**

```lean
noncomputable def hardyPhase (n : ℕ) (t : ℝ) : ℝ :=
  t / 2 * Real.log
    (t / (2 * Real.pi * Real.exp 1 * (n : ℝ) ^ 2)) - Real.pi / 8

theorem deriv_hardyPhase {n : ℕ} (hn : n ≠ 0) {t : ℝ} (ht : 0 < t) :
    deriv (hardyPhase n) t =
      (1 / 2) * Real.log (t / (2 * Real.pi * n ^ 2)) := by

theorem deriv_two_hardyPhase {n : ℕ} (hn : n ≠ 0) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv 2 (hardyPhase n) t = 1 / (2 * t) := by
```

Normalize casts explicitly as `((n : ℝ) ^ 2)` if elaboration requires it.

- [ ] **Step 5: Verify and commit**

```bash
lake env lean HardyTheorem/OscillatoryIntegral.lean
git add HardyTheorem/OscillatoryIntegral.lean
git commit -m "prove the first derivative oscillatory bound"
```

### Task 4: Prove the second-derivative oscillatory estimate

**Files:**
- Modify: `HardyTheorem/OscillatoryIntegral.lean`

**Interfaces:**
- Consumes: Task 3 first-derivative estimate
- Produces: `norm_integral_cexp_phase_le_of_second_deriv`

- [ ] **Step 1: Add the theorem statement**

```lean
theorem norm_integral_cexp_phase_le_of_second_deriv
    {F : ℝ → ℝ} {a b r : ℝ}
    (hab : a ≤ b) (hr : 0 < r)
    (hF : ContDiff ℝ 2 F)
    (hsecond : (∀ x ∈ Icc a b, r ≤ iteratedDeriv 2 F x) ∨
      (∀ x ∈ Icc a b, iteratedDeriv 2 F x ≤ -r)) :
    ‖∫ x in a..b, Complex.exp (I * F x)‖ ≤ 12 / Real.sqrt r := by
```

- [ ] **Step 2: Bound the near-stationary interval**

For the set where `|F'| ≤ sqrt r`, monotonicity and slope at least `r` imply
diameter at most `2 / sqrt r`.  Bound the integral there by interval length,
using `norm_exp_ofReal_mul_I = 1`.

- [ ] **Step 3: Bound both outer intervals**

On either side, `|F'| ≥ sqrt r`; apply Task 3.  Add the two outer bounds and
the near-stationary length bound to obtain `12 / sqrt r`.

- [ ] **Step 4: Specialize to the Hardy phase**

```lean
theorem norm_integral_cexp_hardyPhase_le
    {n : ℕ} (hn : n ≠ 0) {T : ℝ} (hT : 1 ≤ T) :
    ‖∫ t in T..(2 * T), Complex.exp (I * hardyPhase n t)‖ ≤
      12 * Real.sqrt (4 * T) := by
```

Use `F''(t) = 1/(2t) ≥ 1/(4T)` on `[T,2T]` and simplify
`12 / sqrt (1/(4T))`.

- [ ] **Step 5: Verify and commit**

```bash
lake env lean HardyTheorem/OscillatoryIntegral.lean
git add HardyTheorem/OscillatoryIntegral.lean
git commit -m "prove the second derivative oscillatory bound"
```

### Task 5: Prove the vertical Gamma unit-phase estimate

**Files:**
- Create: `HardyTheorem/VerticalGammaAsymptotic.lean`

**Interfaces:**
- Consumes: complex Gamma integral and recurrence, `Gammaℝ_re_im_arg`
- Produces: `thetaModel`, `norm_gammaR_unit_sub_exp_thetaModel_le_inv`

- [ ] **Step 1: Define the smooth phase model**

```lean
import HardyTheorem

open Complex Filter Asymptotics

namespace HardyTheorem

noncomputable def thetaModel (t : ℝ) : ℝ :=
  t / 2 * Real.log (t / (2 * Real.pi)) - t / 2 - Real.pi / 8
```

- [ ] **Step 2: Prove vertical complex Stirling with a relative error**

```lean
noncomputable def gammaQuarterVerticalModel (t : ℝ) : ℂ :=
  (Real.sqrt (2 * Real.pi) *
      (t / 2) ^ (-1 / 4 : ℝ) * Real.exp (-Real.pi * t / 4) : ℝ) *
    Complex.exp
      (I * (t / 2 * Real.log (t / 2) - t / 2 - Real.pi / 8))

theorem exists_norm_Gamma_quarter_vertical_div_model_sub_one_le_inv :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧ ∀ t : ℝ, T0 ≤ t →
      ‖Complex.Gamma ((1 / 4 : ℂ) + I * t / 2) /
          gammaQuarterVerticalModel t - 1‖ ≤ C / t := by
```

First prove the logarithmic Stirling expansion with remainder on the sector
containing `1/4 + i*t/2`.  Derive it from Euler summation applied to the
GammaSeq product: after two summations by parts the remainder is an integral
of the bounded periodic Bernoulli polynomial divided by `(z+u)^2`, hence has
norm `O(1/|z|)`.  Exponentiate with `Complex.exp_bound_sq` after raising the
threshold so the logarithmic remainder has norm at most `1`.  Expand the
principal logarithm of `1/4 + i*t/2` and absorb the difference between
`arg(1/4+i*t/2)` and `pi/2` into the relative `O(1/t)` remainder.  The displayed
model is nonzero for `t > 0` and has the required magnitude
`sqrt(2*pi)*(t/2)^(-1/4)*exp(-pi*t/4)`.

- [ ] **Step 3: Normalize to the GammaR unit phase**

```lean
theorem exists_norm_gammaR_unit_sub_exp_thetaModel_le_inv :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧ ∀ t : ℝ, T0 ≤ t →
      ‖Gammaℝ ((1 / 2 : ℂ) + I * t) /
          ‖Gammaℝ ((1 / 2 : ℂ) + I * t)‖ -
        Complex.exp (I * thetaModel t)‖ ≤ C / t := by
```

Expand `Gammaℝ_def`, use Step 2, and apply the elementary normalization bound
`norm (z / norm z - w / norm w) ≤ 2 * norm (z-w) / norm w` when the relative
error is at most `1/2`.

- [ ] **Step 4: Connect to the exact Hardy phase**

```lean
theorem exists_norm_exp_thetaPhase_sub_exp_thetaModel_le_inv :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧ ∀ t : ℝ, T0 ≤ t →
      ‖Complex.exp (I * thetaPhase t) -
        Complex.exp (I * thetaModel t)‖ ≤ C / t := by
```

Use the exact unit-phase identity proved inside `Gammaℝ_re_im_arg`; expose it
as a local equality rather than asserting an asymptotic for the principal
argument itself.

- [ ] **Step 5: Verify and commit**

```bash
lake env lean HardyTheorem/VerticalGammaAsymptotic.lean
git add HardyTheorem/VerticalGammaAsymptotic.lean
git commit -m "prove the vertical Gamma phase estimate"
```

### Task 6: Prove the specialized first zeta approximation and lower bound

**Files:**
- Create: `HardyTheorem/FirstZetaApproximation.lean`

**Interfaces:**
- Consumes: Mathlib zeta continuation, finite sums, interval integrals
- Produces: `criticalLineZetaFirstApprox`,
  `exists_integral_norm_riemannZeta_critical_line_ge_mul`

- [ ] **Step 1: Define the dyadic cutoff and polynomial**

```lean
import HardyTheorem.HardyIntegralBasics

open Complex BigOperators Filter Set

namespace HardyTheorem

noncomputable def firstApproxCutoff (T : ℝ) : ℕ := Nat.floor (4 * T)

noncomputable def criticalLineDirichletPolynomial (T t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (firstApproxCutoff T),
    1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)
```

- [ ] **Step 2: Prove the uniform first approximation formula**

Prove the classical first approximation uniformly when the imaginary part is
at most a fixed fraction of the truncation length:

```lean
theorem exists_riemannZeta_first_approximation :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℂ) (x : ℝ),
      (1 / 4 : ℝ) ≤ s.re → s.re ≤ 2 → s ≠ 1 → 1 ≤ x →
      |s.im| ≤ x / 2 →
      ∃ R : ℂ,
        riemannZeta s =
          (∑ n ∈ Finset.Icc 1 (Nat.floor x), 1 / (n : ℂ) ^ s) +
            (x : ℂ) ^ (1 - s) / (s - 1) + R ∧
        ‖R‖ ≤ C * x ^ (-s.re) := by
```

Apply Euler summation to the zeta tail and retain its oscillation instead of
taking the absolute value of the factor `s`.  Split the periodic sawtooth
integral into unit intervals.  On each interval integrate once more against
`exp (-i*s.im*log u)`; the condition `|s.im| ≤ x/2` keeps the resulting
denominators uniform.  Summing the interval bounds gives `C*x^(-re s)` with a
constant uniform on `1/4 ≤ re s ≤ 2`.  Start in `1 < re s`, identify the
Dirichlet series with zeta, and extend the resulting analytic equality to
`0 < re s`, `s != 1`; carry the quantitative bound through the explicit
remainder integral rather than through the identity theorem.

- [ ] **Step 3: Specialize to the critical dyadic interval**

```lean
theorem criticalLineZetaFirstApprox :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧ ∀ T t : ℝ,
      T0 ≤ T → t ∈ Set.Icc T (2 * T) →
      ∃ R : ℂ,
        riemannZeta ((1 / 2 : ℂ) + I * t) =
          criticalLineDirichletPolynomial T t + R ∧
        ‖R‖ ≤ C / Real.sqrt T := by
```

Absorb the pole term into `R`; with `x = 4T`, its norm and the Euler remainder
are both `O(T^(-1/2))` uniformly for `t ∈ [T,2T]`.

- [ ] **Step 4: Integrate the polynomial and isolate `n = 1`**

Prove the exact integral of `n^(-it)` for `n >= 2` and the bound

```text
norm (integral T (2T) n^(-1/2-it)) <= 2 / (sqrt n * log n).
```

Bound the finite sum by `O(sqrt T)` using dyadic grouping; the `n = 1` term is
exactly `T`.

- [ ] **Step 5: Derive the lower norm integral bound**

```lean
theorem exists_integral_norm_riemannZeta_critical_line_ge_mul :
    ∃ c T0 : ℝ, 0 < c ∧ 1 ≤ T0 ∧ ∀ T : ℝ, T0 ≤ T →
      c * T ≤ ∫ t in T..(2 * T),
        ‖riemannZeta ((1 / 2 : ℂ) + I * t)‖ := by
```

Use `norm_integral_le_integral_norm`, Step 3, and Step 4 to prove
`norm (integral zeta) >= T - C*sqrt T`, then choose a threshold where the
error is at most `T/2`.

- [ ] **Step 6: Verify and commit**

```bash
lake env lean HardyTheorem/FirstZetaApproximation.lean
git add HardyTheorem/FirstZetaApproximation.lean
git commit -m "prove the critical-line first zeta approximation"
```

### Task 7: Prove the dyadic Hardy-Z upper bound

**Files:**
- Create: `HardyTheorem/HardyIntegralUpperBound.lean`

**Interfaces:**
- Consumes: Tasks 3-6
- Produces: `exists_abs_integral_hardyZ_le_rpow_three_quarters`

- [ ] **Step 1: Prove the smooth-phase finite-sum identity**

For each `n >= 1`, rewrite

```text
Re(exp(i*thetaModel t) * n^(-1/2-it))
  = n^(-1/2) * cos(hardyPhase n t).
```

The equality follows from `cpow_def_of_ne_zero`, the real logarithm of a
positive natural, and the definition of `hardyPhase`.

- [ ] **Step 2: Bound the near-stationary index range**

For `n ≤ 3*sqrt(T/pi)`, apply Task 4 termwise and prove

```text
sum n^(-1/2) * norm(integral exp(i*phase n)) <= C*T^(3/4).
```

Use the integral comparison
`sum_{n≤N} n^(-1/2) ≤ 2*sqrt N`.

- [ ] **Step 3: Bound the nonstationary range**

For `3*sqrt(T/pi) < n ≤ 4T`, prove

```text
deriv (hardyPhase n) t ≤ -4/9
```

on `[T,2T]`, then apply Task 3.  Sum `n^(-1/2)` over this range to obtain an
`O(sqrt T)` contribution.

- [ ] **Step 4: Absorb zeta and Gamma approximation errors**

Use Task 5's phase error and Task 6's zeta remainder.  The zeta polynomial has
pointwise norm `O(sqrt T)` by the triangle inequality, so the phase error
contributes `O(sqrt T)` after integrating `1/t` over `[T,2T]`; the zeta
remainder also contributes `O(sqrt T)`.

- [ ] **Step 5: State and prove the upper bound**

```lean
theorem exists_abs_integral_hardyZ_le_rpow_three_quarters :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧ ∀ T : ℝ, T0 ≤ T →
      |∫ t in T..(2 * T), hardyZ t| ≤ C * T ^ (3 / 4 : ℝ) := by
```

Combine Steps 1-4 and absorb every `O(sqrt T)` term into `T^(3/4)` above
`T >= 1`.

- [ ] **Step 6: Verify and commit**

```bash
lake env lean HardyTheorem/HardyIntegralUpperBound.lean
git add HardyTheorem/HardyIntegralUpperBound.lean
git commit -m "bound the dyadic Hardy-Z integral"
```

### Task 8: Close Hardy's theorem and export it

**Files:**
- Create: `HardyTheorem/HardyIntegralContradiction.lean`
- Modify: `RiemannPNT.lean`

**Interfaces:**
- Consumes: Tasks 2, 6, and 7
- Produces: final unconditional theorem and public API

- [ ] **Step 1: Prove unbounded zeros by contradiction**

```lean
import HardyTheorem.HardyIntegralBasics
import HardyTheorem.FirstZetaApproximation
import HardyTheorem.HardyIntegralUpperBound

open Filter Topology

namespace HardyTheorem

theorem hardy_zeros_unbounded_target_proved : hardy_zeros_unbounded_target := by
```

Negate `hardy_zeros_unbounded_target` to obtain a height above which no
critical-line zero exists.  This makes the Hardy-Z zero set bounded.  Task 2
then equates the absolute Hardy-Z integral to the zeta norm integral.  Task 6
gives `c*T` below it and Task 7 gives `C*T^(3/4)` above it.  Use

```text
T^(3/4) / T = T^(-1/4) -> 0
```

to choose `T` with `C*T^(3/4) < c*T`, a contradiction.

- [ ] **Step 2: Derive the existing infinite-zero target**

```lean
theorem hardy_theorem_target_proved : hardy_theorem_target :=
  hardy_theorem_target_of_unbounded hardy_zeros_unbounded_target_proved
```

- [ ] **Step 3: Export the public API**

Import `HardyTheorem.HardyIntegralContradiction` from `RiemannPNT.lean` and add

```lean
theorem hardy_zeros_unbounded_target_proved :
    HardyTheorem.hardy_zeros_unbounded_target :=
  HardyTheorem.hardy_zeros_unbounded_target_proved
```

inside `RiemannPNT.API`.

- [ ] **Step 4: Verify the original contract is GREEN**

```bash
lake build Test.HardyFirstApproximationContract
```

- [ ] **Step 5: Commit the theorem**

```bash
git add HardyTheorem/HardyIntegralContradiction.lean RiemannPNT.lean
git commit -m "prove Hardy's theorem"
```

### Task 9: Audit, inventory, documentation, and full verification

**Files:**
- Modify: `Test/MultiplicityAxiomAudit.lean`
- Modify: `scripts/check_axiom_allowlist.py`
- Modify: `scripts/update-target-status.py`
- Regenerate: `docs/current-target-status.json`
- Modify: `README.md`
- Modify: `PUBLISHING.md`
- Modify: `docs/formal-theorem-inventory.md`
- Modify: `docs/mathematical-contributions.md`
- Modify: `docs/hardy-theorem-chain.md`
- Modify: `docs/missing-chains-index.md`
- Modify: `docs/target-statements-and-chains.md`

**Interfaces:**
- Consumes: Task 8 final theorem
- Produces: audited and accurately scoped public status

- [ ] **Step 1: Extend the axiom audit**

Add:

```lean
#print axioms HardyTheorem.hardy_zeros_unbounded_target_proved
#print axioms HardyTheorem.hardy_theorem_target_proved
#print axioms RiemannPNT.API.hardy_zeros_unbounded_target_proved
```

and the same names to `EXPECTED_DECLARATIONS`.

- [ ] **Step 2: Update target classification**

Teach `scripts/update-target-status.py` that `hardy_zeros_unbounded_target` and
`hardy_theorem_target` are proved by the Task 8 declarations.  Regenerate the
JSON only with:

```bash
python3 scripts/update-target-status.py
```

- [ ] **Step 3: Update the claim boundary**

State that Hardy's theorem is proved by the first-approximation and
oscillatory-integral route.  Preserve explicit statements that RH,
`Re(s)=1/3` exclusion, the Vinogradov-Korobov region, Hardy-Littlewood zero
counts, Selberg proportions, and Conrey's percentage remain unproved.

- [ ] **Step 4: Run focused checks**

```bash
lake build Test.HardyFirstApproximationContract
python3 scripts/check-targets-consistent.py
python3 scripts/check-chain-gaps.py
python3 -m pytest -q
python3 scripts/check_axiom_allowlist.py
git diff --check
```

- [ ] **Step 5: Run full checks sequentially**

```bash
lake build
./scripts/verify-baseline.sh
```

- [ ] **Step 6: Obtain independent proof review**

The reviewer must inspect the complex Gamma relative-error direction, phase
normalization, both oscillatory-integral constants, the finite index split,
the lower integral bound, and the final contradiction.  Any high-severity
finding blocks publication and requires rerunning Steps 4-5.

- [ ] **Step 7: Commit the audit and documentation**

```bash
git add Test/MultiplicityAxiomAudit.lean scripts/check_axiom_allowlist.py \
  scripts/update-target-status.py docs/current-target-status.json README.md \
  PUBLISHING.md docs/formal-theorem-inventory.md \
  docs/mathematical-contributions.md docs/hardy-theorem-chain.md \
  docs/missing-chains-index.md docs/target-statements-and-chains.md \
  docs/superpowers/plans/2026-07-15-hardy-first-approximation.md
git commit -m "document the formal proof of Hardy's theorem"
```
