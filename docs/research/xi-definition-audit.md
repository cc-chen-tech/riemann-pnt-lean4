# Xi Definition Audit

## Purpose

This note audits the local completed-zeta and xi-related definitions before any
new Lean proof work. It is meant to keep the RH route grounded in existing
Mathlib names and local files.

## Standard Mathematical Target

The classical xi function is usually written as

```text
xi(s) = 1/2 * s * (s - 1) * pi^(-s/2) * Gamma(s/2) * zeta(s).
```

Using Mathlib's real Gamma factor

```text
GammaR(s) = pi^(-s/2) * Gamma(s/2),
```

this becomes

```text
xi(s) = 1/2 * s * (s - 1) * GammaR(s) * zeta(s).
```

Mathlib calls this Gamma factor `Gammaℝ`.

## Mathlib Anchors

Relevant Mathlib file:

- `vendor/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean`

Important names found locally in Mathlib:

- `completedRiemannZeta₀`
  - Entire completed zeta variant.
  - Defined as `completedHurwitzZetaEven₀ 0`.
- `completedRiemannZeta`
  - Meromorphic completed zeta variant.
  - Defined as `completedHurwitzZetaEven 0`.
- `completedRiemannZeta_eq`
  - Relates `completedRiemannZeta` and `completedRiemannZeta₀` by subtracting
    pole terms.
- `differentiable_completedZeta₀`
  - Differentiability of the entire completed-zeta variant.
- `completedRiemannZeta₀_one_sub`
  - Functional equation for `completedRiemannZeta₀`.
- `completedRiemannZeta_one_sub`
  - Functional equation for `completedRiemannZeta`.
- `riemannZeta_eq_completed_div_Gamma`
  - Connects `riemannZeta`, `completedRiemannZeta`, and `Gammaℝ`.
- `_root_.RiemannHypothesis`
  - Mathlib's RH proposition.

Relevant Gamma file:

- `vendor/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Deligne.lean`

Important names:

- `Gammaℝ`
- `Gammaℝ_def`
- `Gammaℝ_ne_zero_of_re_pos`
- `Gammaℝ_eq_zero_iff`

## Local Anchors

### `RiemannExplorer.lean`

Local definition:

```lean
noncomputable def completedZeta (s : ℂ) : ℂ :=
  (1 / 2) * s * (s - 1) * completedRiemannZeta₀ s
    - (1 / 2) * (s - 1) + (1 / 2) * s
```

The file comments describe this as the completed zeta function `xi(s)`, and the
local theorem

```lean
theorem functional_equation (s : ℂ) :
    completedZeta s = completedZeta (1 - s)
```

is proved from `completedRiemannZeta₀_one_sub`.

Audit note:

- This local `completedZeta` is not simply
  `1/2 * s * (s - 1) * completedRiemannZeta₀ s`.
- The extra affine correction
  `- (1 / 2) * (s - 1) + (1 / 2) * s` should be justified or replaced by a
  clearly named definition.
- Before building Li coefficients, the project should introduce a canonical
  `xiFunction` name whose relation to Mathlib's `completedRiemannZeta` and
  `completedRiemannZeta₀` is explicit.

### `HardyTheorem.lean`

This file proves and uses facts around:

- `completedRiemannZeta_conj_eq_of_one_lt_re`
- `completedRiemannZeta₀_conj_eq`
- `completedRiemannZeta_critical_line_real`

Audit note:

- These are useful for the critical-line route and for showing real-valued
  behavior on `1/2 + it`.
- They are not yet a canonical xi-function API.
- They should remain separate from a future `XiFunction.lean` unless reused
  through small exported lemmas.

### `PrimeNumberTheorem.lean`

This file bridges local RH statements to Mathlib:

```lean
theorem rh_statement_iff_mathlib :
    _root_.RiemannHypothesis ↔ RiemannHypothesis.Statement
```

It also contains:

- `RH_ErrorBound`
- `rh_iff_optimal_error`
- `explicit_formula_von_mangoldt`

Audit note:

- This file is the right consumer of xi and explicit formula infrastructure,
  but it should not own the xi API.

## Recommended Lean Boundary

Create a future file only after the active `sorry` work settles:

```text
XiFunction.lean
```

Proposed responsibilities:

- Define `xiFunction : ℂ -> ℂ`.
- State and prove its relation to `completedRiemannZeta` away from poles.
- State and prove its relation to `completedRiemannZeta₀` globally.
- Prove `xiFunction_one_sub`.
- Prove zero correspondence with `RiemannHypothesis.IsNontrivialZero`.
- Export only small API lemmas consumed by Li and Weil routes.

Do not place Li coefficients, explicit formula, or Hardy Z-function work in
this file. Those should be separate consumers.

## Proposed First Lean Statements

These are candidate statements, not yet implementation instructions.

```lean
noncomputable def xiFunction (s : ℂ) : ℂ :=
  (1 / 2) * s * (s - 1) * completedRiemannZeta s
```

This definition is mathematically natural away from `0` and `1`, but it uses
the meromorphic completed zeta. It may need a global version built from
`completedRiemannZeta₀`.

Alternative:

```lean
noncomputable def xiFunction (s : ℂ) : ℂ :=
  (1 / 2) * s * (s - 1) *
    (completedRiemannZeta₀ s - 1 / s - 1 / (1 - s))
```

This expression is not directly safe at `0` and `1`, so the better global
definition should use the already entire `completedRiemannZeta₀` with the pole
cancellation algebra made explicit.

## Open Questions Before Editing Lean

1. Is the local affine correction in `RiemannExplorer.completedZeta` already
   mathematically intended to cancel the pole terms from
   `completedRiemannZeta₀`?
2. Should the canonical xi definition reuse `completedZeta`, or should
   `completedZeta` be renamed after audit?
3. Does Mathlib already contain enough results to prove `xiFunction` is entire,
   or only differentiable as a function?
4. Which zero correspondence is easiest:
   via `completedRiemannZeta` away from poles, or via the globally entire
   `completedRiemannZeta₀` expression?

## Recommendation

The next RH formalization step should be a small `XiFunction.lean` design, not
an immediate proof attempt. The first implementation should prove only:

- the functional equation for the canonical xi definition;
- agreement with the classical expression for `s.re > 1`;
- a clean statement of zero correspondence for nontrivial zeros.

Once those are stable, the Li criterion route has a credible Lean foundation.

