# Classical Prime-Counting Error Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove the unconditional de la Vallee Poussin-form estimate
`|primeCounting x - logIntegral x| <= C*x*exp(-c*sqrt(log x))` for all
sufficiently large real `x`.

**Architecture:** Transfer the proved `psi` remainder to `theta`, then bound the
exact Abel error integral by splitting at `sqrt x`.  Assemble the endpoint,
integral, and fixed lower-limit terms through the existing partial-summation
identity.  Keep every result concrete; do not introduce a new conditional
target predicate.

**Tech Stack:** Lean 4.29.1, Mathlib interval integrals and asymptotics,
Chebyshev functions, real logarithm/exponential/rpow estimates.

## Global Constraints

- Do not add `sorry`, `admit`, custom axioms, or `def ... : Prop` placeholders.
- The final theorem must quantify all sufficiently large real inputs.
- The final theorem must concern the actual `primeCounting` and `logIntegral`
  functions, not a surrogate sequence or conditional interface.
- Constants may be existential but must satisfy `0 < c` and `0 <= C`.
- Do not claim numerically explicit constants, a power saving below `2/3`,
  zero exclusion on `Re(s)=1/3`, or RH.

---

### Task 1: Failing final theorem contract

**Files:**
- Create: `Test/ClassicalPrimeCountingErrorContract.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes: `PrimeNumberTheorem.primeCounting`,
  `PrimeNumberTheorem.logIntegral`
- Produces: compile-time contracts for the namespace theorem and public API

- [x] **Step 1: Add the contract before production code**

```lean
import RiemannPNT

open PrimeNumberTheorem

example :
    ∃ c C X : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ x : ℝ, X ≤ x →
      |(primeCounting x : ℝ) - logIntegral x| ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x)) :=
  exists_abs_primeCounting_sub_logIntegral_le_exp_neg_sqrt_log

example :
    ∃ c C X : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ x : ℝ, X ≤ x →
      |(primeCounting x : ℝ) - logIntegral x| ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x)) :=
  RiemannPNT.API.exists_abs_primeCounting_sub_logIntegral_le_exp_neg_sqrt_log
```

Register `Test.ClassicalPrimeCountingErrorContract` immediately after
`Test.ClassicalPNTErrorContract` in the `roots` array.

- [x] **Step 2: Verify RED**

Run:

```bash
lake build Test.ClassicalPrimeCountingErrorContract
```

Expected: failure reporting that
`exists_abs_primeCounting_sub_logIntegral_le_exp_neg_sqrt_log` and its API
export are unknown.  Fix import or syntax errors until these missing
declarations are the only cause.

- [x] **Step 3: Commit the contract**

```bash
git add Test/ClassicalPrimeCountingErrorContract.lean lakefile.lean
git commit -m "test the classical prime-counting error contract"
```

### Task 2: Transfer the `psi` remainder to `theta`

**Files:**
- Create: `PrimeNumberTheorem/ClassicalPrimeCountingError.lean`

**Interfaces:**
- Consumes:
  `exists_abs_chebyshevPsi_sub_id_le_exp_neg_sqrt_log`,
  `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log`
- Produces:
  `exists_eventually_abs_chebyshevTheta_sub_id_le_exp_neg_sqrt_log`

- [x] **Step 1: Add the exact intermediate theorem statement**

```lean
import PrimeNumberTheorem.ClassicalPNTError

open Filter Topology

namespace PrimeNumberTheorem

theorem exists_eventually_abs_chebyshevTheta_sub_id_le_exp_neg_sqrt_log :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
      |Chebyshev.theta x - x| ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x))

end PrimeNumberTheorem
```

Attach a `by` proof using the following exact inequalities in one theorem body.

- [x] **Step 2: Extract the proved `psi` constants and weaken the decay**

Use

```lean
rcases exists_abs_chebyshevPsi_sub_id_le_exp_neg_sqrt_log with
  ⟨c, C, X, hc, hC, hpsi⟩
let a : ℝ := c / 2
```

Prove `0 < a`.  Work eventually above `max X (Real.exp 1)` and above a
threshold satisfying `4*a <= sqrt(log x)`.

- [x] **Step 3: Absorb the prime-power correction**

For each sufficiently large `x`, obtain

```lean
have hdiff := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx1
```

and normalize it with `chebyshevPsi_eq_mathlib`.  Use
`Real.log_le_rpow_div` at exponent `1/4` to prove

```text
2*sqrt(x)*log(x) <= 8*x^(3/4).
```

Use `Real.rpow_def_of_pos`, `Real.exp_le_exp`, and
`4*a <= sqrt(log x)` to prove

```text
x^(3/4) <= x*exp(-a*sqrt(log x)).
```

The final pointwise calculation must be

```text
|theta(x)-x|
 <= |psi(x)-x| + |psi(x)-theta(x)|
 <= (C+8)*x*exp(-a*sqrt(log x)).
```

Return constants `a` and `C+8` with a nonnegativity proof.

- [x] **Step 4: Verify GREEN for the module**

Run:

```bash
lake env lean PrimeNumberTheorem/ClassicalPrimeCountingError.lean
```

Expected: exit code `0` with no placeholder declarations.

- [x] **Step 5: Commit the theta transfer**

```bash
git add PrimeNumberTheorem/ClassicalPrimeCountingError.lean
git commit -m "prove the classical theta error term"
```

### Task 3: Bound the Abel error integral

**Files:**
- Modify: `PrimeNumberTheorem/ClassicalPrimeCountingError.lean`

**Interfaces:**
- Consumes:
  `exists_eventually_abs_chebyshevTheta_sub_id_le_exp_neg_sqrt_log`,
  `intervalIntegrable_theta_error_div_id_log_sq_of_le`
- Produces:
  `exists_eventually_abs_theta_error_integral_le_exp_neg_sqrt_log`

- [x] **Step 1: Add the integral theorem statement**

```lean
theorem exists_eventually_abs_theta_error_integral_le_exp_neg_sqrt_log :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
      |∫ t in (2)..x,
          (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
```

- [x] **Step 2: Fix the threshold and split the interval**

Extract `a`, `D`, and an eventual threshold `A0` from Task 2.  Define

```lean
let A : ℝ := max (max A0 (Real.exp 1)) 2
let K : ℝ → ℝ := fun t =>
  (Chebyshev.theta t - t) / (t * Real.log t ^ 2)
let I0 : ℝ := ∫ t in (2)..A, K t
let b : ℝ := a / 4
```

Work eventually above `max (A^2) 4` and all logarithmic thresholds needed to
show the final scale is at least `sqrt x` and `1`.  Prove `A <= sqrt x` using
`Real.le_sqrt`.

Use `intervalIntegrable_theta_error_div_id_log_sq_of_le` and
`intervalIntegral.integral_add_adjacent_intervals` twice to establish exactly

```text
integral 2 x K = I0 + integral A (sqrt x) K + integral (sqrt x) x K.
```

- [x] **Step 3: Bound `[A, sqrt x]`**

Apply `intervalIntegral.abs_integral_le_integral_abs` and
`intervalIntegral.integral_mono_on`.  For `A <= t <= sqrt x`, use the Task 2
bound, `1 <= log t`, `exp(...) <= 1`, and positivity of the denominator to
prove `|K t| <= D`.

Pull out the constant with `intervalIntegral.integral_const` and derive

```text
|integral A (sqrt x) K| <= D*sqrt x.
```

- [x] **Step 4: Bound `[sqrt x, x]`**

For `sqrt x <= t <= x`, prove

```text
log x / 2 <= log t
sqrt (log x) / 2 <= sqrt (log t).
```

Use `Real.log_sqrt`, `Real.log_le_log`, `Real.sq_sqrt`, and nonnegativity.
The theta bound then yields

```text
|K t| <= D*exp(-(a/2)*sqrt(log x)).
```

Integrate this constant majorant over an interval of length at most `x` to
obtain

```text
|integral (sqrt x) x K|
  <= D*x*exp(-(a/2)*sqrt(log x)).
```

- [x] **Step 5: Absorb the initial and short-interval terms**

With `b=a/4`, prove eventually

```text
1 <= x*exp(-b*sqrt(log x))
sqrt x <= x*exp(-b*sqrt(log x))
exp(-(a/2)*sqrt(log x)) <= exp(-b*sqrt(log x)).
```

The first two follow from `2*b <= sqrt(log x)` after rewriting `x` as
`exp(log x)`.  Combine the three interval estimates with `abs_add_le` and use
a nonnegative constant such as `|I0| + 2*D`.

- [x] **Step 6: Verify GREEN and commit**

Run:

```bash
lake env lean PrimeNumberTheorem/ClassicalPrimeCountingError.lean
```

Then:

```bash
git add PrimeNumberTheorem/ClassicalPrimeCountingError.lean
git commit -m "bound the classical Abel error integral"
```

### Task 4: Assemble and export the final theorem

**Files:**
- Modify: `PrimeNumberTheorem/ClassicalPrimeCountingError.lean`
- Modify: `RiemannPNT.lean`

**Interfaces:**
- Consumes:
  `primeCounting_sub_logIntegral_eq_theta_error_integral`, Tasks 2 and 3
- Produces:
  `exists_abs_primeCounting_sub_logIntegral_le_exp_neg_sqrt_log` in both
  `PrimeNumberTheorem` and `RiemannPNT.API`

- [ ] **Step 1: Prove the eventual final estimate**

Add:

```lean
theorem exists_eventually_abs_primeCounting_sub_logIntegral_le_exp_neg_sqrt_log :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
      |(primeCounting x : ℝ) - logIntegral x| ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
```

Take the minimum of the positive decay constants from Tasks 2 and 3.  Above
`exp 1`, compare both existing scales with the common weaker scale.  Use
`primeCounting_sub_logIntegral_eq_theta_error_integral` and `abs_add_le` twice.
Bound the endpoint by the theta estimate divided by `log x >= 1`, use Task 3
for the integral, and absorb `2/log 2` after proving the common scale is at
least `1`.

- [ ] **Step 2: Package explicit existential constants**

Add:

```lean
theorem exists_abs_primeCounting_sub_logIntegral_le_exp_neg_sqrt_log :
    ∃ c C X : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ x : ℝ, X ≤ x →
      |(primeCounting x : ℝ) - logIntegral x| ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  rcases exists_eventually_abs_primeCounting_sub_logIntegral_le_exp_neg_sqrt_log with
    ⟨c, C, hc, hC, hbound⟩
  rcases eventually_atTop.1 hbound with ⟨X, hX⟩
  exact ⟨c, C, X, hc, hC, hX⟩
```

- [ ] **Step 3: Export through the public API**

Import `PrimeNumberTheorem.ClassicalPrimeCountingError` in `RiemannPNT.lean`
and add:

```lean
theorem exists_abs_primeCounting_sub_logIntegral_le_exp_neg_sqrt_log :
    ∃ c C X : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ x : ℝ, X ≤ x →
      |(PrimeNumberTheorem.primeCounting x : ℝ) -
          PrimeNumberTheorem.logIntegral x| ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x)) :=
  PrimeNumberTheorem.exists_abs_primeCounting_sub_logIntegral_le_exp_neg_sqrt_log
```

- [ ] **Step 4: Verify the original RED contract is GREEN**

Run:

```bash
lake build Test.ClassicalPrimeCountingErrorContract
```

Expected: successful build of the final theorem and both contract examples.

- [ ] **Step 5: Commit the endpoint**

```bash
git add PrimeNumberTheorem/ClassicalPrimeCountingError.lean RiemannPNT.lean
git commit -m "prove the classical prime-counting error term"
```

### Task 5: Audit, documentation, and repository verification

**Files:**
- Modify: `Test/MultiplicityAxiomAudit.lean`
- Modify: `scripts/check_axiom_allowlist.py`
- Modify: `README.md`
- Modify: `PUBLISHING.md`
- Modify: `docs/formal-theorem-inventory.md`
- Modify: `docs/mathematical-contributions.md`
- Modify: `docs/missing-chains-index.md`
- Modify: `docs/target-statements-and-chains.md`
- Modify: `docs/assets/riemann-proof-atlas.html`
- Modify: `scripts/update-target-status.py` only if generated status wording
  still calls the Abel endpoint open
- Regenerate: `docs/current-target-status.json` only through the repository
  status script

**Interfaces:**
- Consumes: final Task 4 theorem
- Produces: an audited and accurately scoped repository claim

- [ ] **Step 1: Extend the axiom audit**

Append:

```lean
#print axioms PrimeNumberTheorem.exists_abs_primeCounting_sub_logIntegral_le_exp_neg_sqrt_log
#print axioms RiemannPNT.API.exists_abs_primeCounting_sub_logIntegral_le_exp_neg_sqrt_log
```

Add the same fully-qualified names to `EXPECTED_DECLARATIONS` in
`scripts/check_axiom_allowlist.py`.

- [ ] **Step 2: Update the publication boundary**

State the exact `pi-Li` remainder shape and that constants are existential.
Remove only claims that the quantitative Abel endpoint is open.  Preserve
explicit statements that `O(x^(2/3-delta))`, `Re(s)=1/3` exclusion, RH,
Hardy, Vinogradov-Korobov, and numerically explicit constants remain open.

- [ ] **Step 3: Run focused and inventory checks**

```bash
lake build Test.ClassicalPrimeCountingErrorContract
python3 scripts/check-targets-consistent.py
python3 scripts/check-chain-gaps.py
python3 -m pytest -q
python3 scripts/check_axiom_allowlist.py
git diff --check
```

Expected: all commands exit `0`; inventory remains fully classified.

- [ ] **Step 4: Run full verification**

```bash
lake build
./scripts/verify-baseline.sh
```

Run these sequentially.  Expected: both exit `0`, no placeholder scan
failures, and only the standard allowed axioms.

- [ ] **Step 5: Obtain independent proof review**

Review must inspect the `psi`-to-`theta` absorption, both Abel subinterval
bounds, the common decay-constant comparison, and every public claim.  Treat
any high-severity finding as blocking and rerun the focused and baseline
checks after fixes.

- [ ] **Step 6: Commit the audit and documentation**

```bash
git add Test/MultiplicityAxiomAudit.lean scripts/check_axiom_allowlist.py \
  README.md PUBLISHING.md docs/formal-theorem-inventory.md \
  docs/mathematical-contributions.md docs/missing-chains-index.md \
  docs/target-statements-and-chains.md docs/assets/riemann-proof-atlas.html \
  scripts/update-target-status.py docs/current-target-status.json
git commit -m "document the classical prime-counting remainder"
```

Do not stage generated files whose content did not change.
