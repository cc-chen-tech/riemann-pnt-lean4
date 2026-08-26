# Conrey Littlewood Mean-Square Bridge Implementation Plan

> **For Codex:** Follow `superpowers:executing-plans` task by task. Keep the
> mathematical theorem below separate from the still-unproved long mollified
> mean-square estimate.

**Goal:** Formalize the exact, constant-preserving analytic inequality that
turns a positive continuous function's interval mean square into the logarithmic
boundary integral used by Conrey's Littlewood argument.

**Architecture:** First prove a generic logarithmic arithmetic-geometric mean
inequality in `MathlibAux`. Then specialize it to `f(t) = ‖F(t)‖ ^ 2` for
complex-valued functions in `HardyTheorem`. This closes only the Jensen/AGM
bridge; it neither states nor assumes Conrey's long mollified mean-square
theorem.

**Tech Stack:** Lean 4, Mathlib interval integrals, real logarithm, continuity,
complex norm.

**Research specification:**
`docs/research/2026-08-25-conrey-two-fifths-mathematical-audit.md`

## Mathematical statement

Let `a < b` and let `F : R -> C` be continuous and nonzero on `[a,b]`. Put

```text
L = b - a,
M2 = integral_a^b |F(t)|^2 dt.
```

Then `L > 0`, `M2 > 0`, and

```text
2 * integral_a^b log |F(t)| dt
  <= L * log (M2 / L).
```

Consequently, if `M2 <= C * L` and `C > 0`, then

```text
2 * integral_a^b log |F(t)| dt <= L * log C.
```

The proof is constant-exact. For a positive continuous real function `f`, set
`m = (integral f) / L`. Pointwise,

```text
log (f(t) / m) <= f(t) / m - 1.
```

After integration the affine error has integral zero, because
`(integral f) / m = L`. Applying this to `f = |F|^2` and using
`log (|F|^2) = 2 log |F|` gives the displayed inequality.

### Task 1: Lock the public contract in RED

**Files:**

- Create: `Test/ConreyLittlewoodMeanSquareContract.lean`

1. Import `HardyTheorem.ConreyLittlewoodMeanSquare`.
2. State examples for the exact logarithmic mean-square inequality and its
   upper-bound corollary.
3. Run `lake env lean Test/ConreyLittlewoodMeanSquareContract.lean` and verify
   failure is the missing production module, not an unrelated syntax error.

The regression caught is loss of the factor `2`, loss of the normalization
`b-a`, or a reversed inequality. The expectations are the hand-derived formulas
above and do not reuse implementation helpers.

### Task 2: Prove the generic real logarithmic AGM inequality

**Files:**

- Create: `MathlibAux/LogMeanSquare.lean`

1. Prove positivity of the interval integral from strict positivity and
   continuity.
2. Integrate `Real.log_le_sub_one_of_pos` after normalizing by the interval
   average.
3. Simplify the integrated affine error exactly.
4. Expose an upper-bound corollary using monotonicity of `Real.log`.

### Task 3: Specialize to a complex-valued boundary function

**Files:**

- Create: `HardyTheorem/ConreyLittlewoodMeanSquare.lean`
- Modify: `lakefile.lean`

1. Apply the generic theorem to `fun t => ‖F t‖ ^ 2`.
2. Use nonvanishing to prove strict positivity.
3. Rewrite `Real.log (‖F t‖ ^ 2)` as `2 * Real.log ‖F t‖`.
4. Prove the exact mean-square statement and the `C`-bounded corollary.
5. Register the production and contract roots.

### Task 4: Verify and document the proof boundary

**Files:**

- Modify: `docs/research/2026-08-25-conrey-two-fifths-mathematical-audit.md`

1. Run the targeted production build.
2. Run the contract directly.
3. Inspect `#print axioms` output and the repository allowlist where practical.
4. Record that the Jensen/AGM bridge is proved, while the long mollified
   mean-square and DI/Kloosterman inputs remain open.
5. Review the diff, commit, push, and confirm PR #486 remains open and
   ready for review.
