# Selberg Residue Fourier Mass Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove the low- and high-frequency mass bounds for the elementary residue in Selberg's explicit S1 kernel, at the exact scales needed by the existing nonconstant Fourier-mass theorems.

**Architecture:** Extend the focused residue module in three layers.  First bound the squared residue coefficient by `X^4` and absorb `X^4` into `delta^(-1/2)` from `c<1/8`.  Next dominate the residue pointwise by `delta^(-1/2) * exp (-y)` and integrate it on the low and high ranges.  Finally rewrite `log (X^a) = a * log X` to expose the same public existential-constant interfaces as `SelbergNonconstantFourierMass`.

**Tech Stack:** Lean 4.33, Mathlib Bochner/set integrals, real `rpow`, repository contract tests.

**Spec:** `docs/research/2026-08-24-selberg-mainline-mathematical-audit.md`, equations `(S2-res-low)` and `(S2-res-high)`.

## Global Constraints

- Do not use the Zeta23 bridge or any zero-density hypothesis.
- Do not add `sorry`, `admit`, `axiom`, or `opaque`.
- Keep constants uniform in `X` and `delta`; dependence on fixed `a` and `c` is permitted.
- Retain the exact assumptions used by the neighboring nonconstant low/high mass interfaces.
- Write each public contract before its implementation and observe the expected missing-declaration failure.

---

### Task 1: Residue coefficient and pointwise absorption

**Files:**
- Modify: `HardyTheorem/SelbergResidueFourierMass.lean`
- Modify: `Test/SelbergResidueFourierMassContract.lean`

**Interfaces:**
- Consumes: `norm_selbergSqrtZetaPsi_one_mul_zero_le`, `normSq_selbergResidueInverseFourierKernel`.
- Produces: `normSq_selbergSqrtZetaPsi_one_mul_zero_le_fourth`, `selberg_fourth_power_le_delta_neg_half`, and `normSq_selbergResidueInverseFourierKernel_le_exp_mul_delta_neg_half`.

- [x] **Step 1: Write the failing contract**

```lean
#check normSq_selbergSqrtZetaPsi_one_mul_zero_le_fourth
#check selberg_fourth_power_le_delta_neg_half
#check normSq_selbergResidueInverseFourierKernel_le_exp_mul_delta_neg_half
```

- [x] **Step 2: Verify RED**

Run: `lake env lean Test/SelbergResidueFourierMassContract.lean`

Expected: unknown-identifier errors for the three declarations above.

- [x] **Step 3: Implement the coefficient and pointwise bounds**

Use `Real.log_le_sub_one_of_pos` to prove `1 + log X <= X`, square the existing norm bound, then use `Real.rpow_le_rpow` and `Real.rpow_le_rpow_of_exponent_ge` to prove

```lean
(X : ℝ) ^ 4 ≤ delta ^ (-(1 / 2 : ℝ)).
```

Rewrite the exact residue norm-square identity and multiply the nonnegative inequalities.

- [x] **Step 4: Verify GREEN**

Run both:

```bash
lake env lean HardyTheorem/SelbergResidueFourierMass.lean
lake env lean Test/SelbergResidueFourierMassContract.lean
```

Expected: both exit zero.

### Task 2: Low- and high-range integral envelopes

**Files:**
- Modify: `HardyTheorem/SelbergResidueFourierMass.lean`
- Modify: `Test/SelbergResidueFourierMassContract.lean`

**Interfaces:**
- Consumes: `normSq_selbergResidueInverseFourierKernel_le_exp_mul_delta_neg_half`, `integrableOn_exp_neg_Ioi`, `integral_exp_neg_Ioi`.
- Produces: `integral_normSq_selbergResidueInverseFourierKernel_low_le_delta_neg_half` and `integral_normSq_selbergResidueInverseFourierKernel_div_sq_high_le`.

- [x] **Step 1: Write the failing contract**

```lean
#check integral_normSq_selbergResidueInverseFourierKernel_low_le_delta_neg_half
#check integral_normSq_selbergResidueInverseFourierKernel_div_sq_high_le
```

- [x] **Step 2: Verify RED**

Run: `lake env lean Test/SelbergResidueFourierMassContract.lean`

Expected: unknown-identifier errors for the two integral declarations.

- [x] **Step 3: Implement the integral bounds**

For the low range, dominate by `delta^(-1/2) * exp (-y)` and enlarge `Ioc 0 L` to `Ioi 0`.  For the high range, use `L^2 <= y^2` on `Ioi L`, dominate by

```lean
delta ^ (-(1 / 2 : ℝ)) / L ^ 2 * Real.exp (-y),
```

and evaluate the exponential tail.  Use `integral_mono_of_nonneg`, so no circular integrability hypothesis on the residue is introduced.

- [x] **Step 4: Verify GREEN**

Run the source and contract commands from Task 1.  Expected: both exit zero.

### Task 3: Public parameter-scale interfaces

**Files:**
- Modify: `HardyTheorem/SelbergResidueFourierMass.lean`
- Modify: `Test/SelbergResidueFourierMassContract.lean`
- Modify: `lakefile.lean` only if a new module is split out during implementation.

**Interfaces:**
- Consumes: the two integral envelopes and `Real.log_rpow`.
- Produces: `exists_integral_normSq_selbergResidueInverseFourierKernel_low_le` and `exists_integral_normSq_selbergResidueInverseFourierKernel_high_le` with signatures parallel to the existing nonconstant-mass theorems.

- [x] **Step 1: Write the failing contract**

```lean
#check exists_integral_normSq_selbergResidueInverseFourierKernel_low_le
#check exists_integral_normSq_selbergResidueInverseFourierKernel_high_le
```

- [x] **Step 2: Verify RED**

Run: `lake env lean Test/SelbergResidueFourierMassContract.lean`

Expected: unknown-identifier errors for the two existential declarations.

- [x] **Step 3: Implement the final scale conversion**

Derive `0 < a` and `0 < log X` from `2 <= log (X^a)` and `2 <= X`.  Rewrite

```lean
Real.log ((X : ℝ) ^ a) = a * Real.log (X : ℝ)
```

and choose the uniform witness `C = 1 / a` for both the low and high estimates.

- [x] **Step 4: Verify GREEN and the target build**

Run:

```bash
lake env lean HardyTheorem/SelbergResidueFourierMass.lean
lake env lean Test/SelbergResidueFourierMassContract.lean
lake build HardyTheorem.SelbergResidueFourierMass
git diff --check
```

Expected: every command exits zero and no new placeholder is present.

- [x] **Step 5: Commit and update PR #484**

```bash
git add HardyTheorem/SelbergResidueFourierMass.lean \
  Test/SelbergResidueFourierMassContract.lean \
  docs/research/2026-08-24-selberg-mainline-mathematical-audit.md \
  docs/superpowers/plans/2026-08-25-selberg-residue-mass.md
git commit -m "feat(selberg): bound residue Fourier mass"
git push
```
