# Conrey Mollifier Moving-Right Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove the explicit uniform estimate
`‖B(2 * log L + i t, conreyExplicitP) - 1‖ ≤ 3 / L` for `L ≥ exp 1`, uniformly in the mollifier cutoff and height.

**Architecture:** Put the reusable finite-Dirichlet-tail estimate and its specialization to Conrey's explicit polynomial in one focused module.  Keep the result independent of the unproved `V₁` approximation and of the long mollified mean square; the module supplies only the rigorously closed `B` factor of equation (37)'s moving right edge.

**Tech Stack:** Lean 4, Mathlib complex powers and real `rpow`, finite sums, integral comparison, Lake contract roots.

**Spec:** `docs/research/2026-08-25-conrey-two-fifths-mathematical-audit.md`, Section 21.

## Global Constraints

- Establish the mathematical inequality before adding a Lean endpoint.
- Use the actual equation-(33) `conreyMollifier`; do not introduce an abstract surrogate.
- The final theorem must be uniform in `t : ℝ` and `Y : ℕ`.
- Do not assume a mean-square theorem, a spectral estimate, or a quantitative theorem for `V₁`.
- The proof must use `sigma0 ≤ 1 / 2`, matching `sigma0 = 1 / 2 - R / L` for positive `R,L`.
- The public contract must print only standard logical axioms.

---

### Task 1: Contract for the explicit polynomial and generic right-tail bound

**Files:**
- Create: `Test/ConreyMollifierRightEdgeContract.lean`
- Create: `HardyTheorem/ConreyMollifierRightEdge.lean`

**Interfaces:**
- Consumes: `conreyExplicitP`, `conreyMollifier`, `conreyMollifierCoefficient_one`, and `PrimeNumberTheorem.sum_Icc_rpow_le_add_div_of_lt_neg_one`.
- Produces:
  - `abs_conreyExplicitP_le_one {x : ℝ} (hx : x ∈ Set.Icc 0 1) : |conreyExplicitP x| ≤ 1`
  - `norm_conreyMollifier_sub_one_le_rightTail ... : ‖conreyMollifier Y sigma0 P s - 1‖ ≤ 2 ^ (-s.re) * (1 + 2 / (s.re - 1))`

- [ ] **Step 1: Write the failing public contract**

```lean
import HardyTheorem.ConreyMollifierRightEdge

open Complex Set

namespace HardyTheorem

example {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    |conreyExplicitP x| ≤ 1 :=
  abs_conreyExplicitP_le_one hx

example {Y : ℕ} {sigma0 : ℝ} {P : ℝ → ℝ} {s : ℂ}
    (hY : 2 ≤ Y) (hsigma0 : sigma0 ≤ 1 / 2)
    (hP1 : P 1 = 1)
    (hP : ∀ x ∈ Set.Icc (0 : ℝ) 1, |P x| ≤ 1)
    (hs : 1 < s.re) :
    ‖conreyMollifier Y sigma0 P s - 1‖ ≤
      (2 : ℝ) ^ (-s.re) * (1 + 2 / (s.re - 1)) :=
  norm_conreyMollifier_sub_one_le_rightTail hY hsigma0 hP1 hP hs

#print axioms abs_conreyExplicitP_le_one
#print axioms norm_conreyMollifier_sub_one_le_rightTail

end HardyTheorem
```

- [ ] **Step 2: Run the contract and verify it fails because the module is absent**

Run: `lake env lean Test/ConreyMollifierRightEdgeContract.lean`

Expected: failure resolving `HardyTheorem.ConreyMollifierRightEdge`.

- [ ] **Step 3: Prove the explicit polynomial bound**

Create `HardyTheorem/ConreyMollifierRightEdge.lean` importing
`HardyTheorem.ConreyExplicitIntegralBridge`,
`HardyTheorem.ConreyMollifierProduct`, and
`PrimeNumberTheorem.CarlsonDivisorSquare`.  Prove `0 ≤ conreyExplicitP x`
and `conreyExplicitP x ≤ 1` from `0 ≤ x ≤ 1`, `x^3 ≤ x`, and `x^5 ≤ x`,
then rewrite the absolute value using nonnegativity.

- [ ] **Step 4: Prove that the logarithmic mollifier argument lies in `[0,1]`**

For `2 ≤ Y` and `n ∈ Finset.Icc 1 Y`, prove

```lean
Real.log ((Y : ℝ) / n) / Real.log Y ∈ Set.Icc (0 : ℝ) 1
```

using `1 ≤ Y / n ≤ Y`, positivity of `log Y`, and monotonicity of `Real.log`.

- [ ] **Step 5: Bound each actual Conrey coefficient by one**

Use `ArithmeticFunction.abs_moebius_le_one`, the polynomial hypothesis,
`sigma0 - 1 / 2 ≤ 0`, and the complex-cpow norm formula to prove

```lean
‖conreyMollifierCoefficient Y sigma0 P n‖ ≤ 1
```

for every `n ∈ Finset.Icc 1 Y`.

- [ ] **Step 6: Split off the exact constant term and prove the p-series tail**

Rewrite `conreyMollifier Y sigma0 P s - 1` as the sum over
`Finset.Icc 2 Y`, apply the triangle inequality and the coefficient bound,
then apply
`PrimeNumberTheorem.sum_Icc_rpow_le_add_div_of_lt_neg_one` with
`L=2`, `U=Y`, and `q=-s.re`.  Algebraically simplify its right side and
drop the nonnegative `Y^(1-s.re)` term to obtain

```lean
(2 : ℝ) ^ (-s.re) * (1 + 2 / (s.re - 1)).
```

- [ ] **Step 7: Run the contract**

Run: `lake env lean Test/ConreyMollifierRightEdgeContract.lean`

Expected: exit code 0 and axiom output containing only
`[propext, Classical.choice, Quot.sound]` (a subset is acceptable).

### Task 2: Corrected `2 log L` moving edge

**Files:**
- Modify: `HardyTheorem/ConreyMollifierRightEdge.lean`
- Modify: `Test/ConreyMollifierRightEdgeContract.lean`

**Interfaces:**
- Consumes: `norm_conreyMollifier_sub_one_le_rightTail`.
- Produces: `norm_conreyExplicitMollifier_movingRight_sub_one_le ... : ‖conreyMollifier Y sigma0 conreyExplicitP ((2 * Real.log L : ℂ) + I * t) - 1‖ ≤ 3 / L`.

- [ ] **Step 1: Add the failing endpoint contract**

```lean
example {Y : ℕ} {sigma0 L t : ℝ}
    (hY : 2 ≤ Y) (hsigma0 : sigma0 ≤ 1 / 2)
    (hL : Real.exp 1 ≤ L) :
    ‖conreyMollifier Y sigma0 conreyExplicitP
        ((2 * Real.log L : ℂ) + I * t) - 1‖ ≤ 3 / L :=
  norm_conreyExplicitMollifier_movingRight_sub_one_le hY hsigma0 hL t
```

- [ ] **Step 2: Run the contract and verify the new name is missing**

Run: `lake env lean Test/ConreyMollifierRightEdgeContract.lean`

Expected: failure with unknown identifier
`norm_conreyExplicitMollifier_movingRight_sub_one_le`.

- [ ] **Step 3: Prove the corrected moving-edge exponent bounds**

From `exp 1 ≤ L`, prove `1 ≤ log L`, hence
`2 ≤ 2 * log L`.  Use `Real.log_two_gt_d9` to obtain
`1 / 2 ≤ log 2`, rewrite real powers through `Real.rpow_def_of_pos`, and
prove

```lean
(2 : ℝ) ^ (-(2 * Real.log L)) ≤ 1 / L
```

by monotonicity of `Real.exp` and `Real.exp_neg_log`.

- [ ] **Step 4: Specialize the generic tail**

Apply `norm_conreyMollifier_sub_one_le_rightTail` with
`P=conreyExplicitP` and `s=(2 * log L : ℂ) + I*t`.  Bound
`1 + 2 / (2 * log L - 1) ≤ 3`, combine with the preceding real-power
bound, and conclude `≤ 3/L`.

- [ ] **Step 5: Run the contract and targeted module build**

Run:

```bash
lake env lean Test/ConreyMollifierRightEdgeContract.lean
lake build HardyTheorem.ConreyMollifierRightEdge Test.ConreyMollifierRightEdgeContract
```

Expected: both commands exit 0.

### Task 3: Build roots, audit synchronization, and review gate

**Files:**
- Modify: `lakefile.lean`
- Modify: `docs/research/2026-08-25-conrey-two-fifths-mathematical-audit.md`

**Interfaces:**
- Consumes: all Task 1 and Task 2 theorems.
- Produces: default-build coverage and an honest equation-(37) status boundary.

- [ ] **Step 1: Add both new Lake roots**

Add `HardyTheorem.ConreyMollifierRightEdge` beside
`HardyTheorem.ConreyFarRight` and add
`Test.ConreyMollifierRightEdgeContract` beside `Test.ConreyFarRightContract`.

- [ ] **Step 2: Synchronize the mathematical audit**

Ensure Section 21 records exactly the proved `(B-right)` and `(B-moving)`
bounds, identifies Conrey 1983 pages 59--60 as the source of the printed
`sigma_1=log L` inconsistency, and explicitly leaves the normalized `V₁`
estimate and long mollified mean square open.

- [ ] **Step 3: Run formatting and targeted verification**

Run:

```bash
git diff --check
lake env lean Test/ConreyMollifierRightEdgeContract.lean
lake build HardyTheorem.ConreyMollifierRightEdge Test.ConreyMollifierRightEdgeContract
```

Expected: all commands exit 0.

- [ ] **Step 4: Inspect the exact diff and axiom output**

Run:

```bash
git diff --stat
git diff -- HardyTheorem/ConreyMollifierRightEdge.lean Test/ConreyMollifierRightEdgeContract.lean lakefile.lean docs/research/2026-08-25-conrey-two-fifths-mathematical-audit.md
```

Reject any statement that claims the `V₁` product bound, equation (37), or
the Conrey two-fifths target is complete.

- [ ] **Step 5: Commit and update the existing PR**

Run:

```bash
git add HardyTheorem/ConreyMollifierRightEdge.lean Test/ConreyMollifierRightEdgeContract.lean lakefile.lean docs/research/2026-08-25-conrey-two-fifths-mathematical-audit.md docs/superpowers/plans/2026-08-28-conrey-mollifier-moving-right.md
git commit -m "feat(conrey): quantify explicit mollifier right edge"
git push origin codex/conrey-two-fifths-mainline-20260826
```

Then confirm PR #489 is open, non-draft, mergeable, and still ready for
review.  Do not merge it.
