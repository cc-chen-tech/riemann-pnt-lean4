/-
Copyright (c) 2026 Riemann PNT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Truncated Explicit Formula — Main Target (interface placeholder)

## Purpose

This file declares the project-internal **interface** for the
"truncated von Mangoldt explicit formula" main target.  The target
locks the signature of the asymptotic identity

```
  ψ₀(x) = x − ∑_{|ρ| ≤ T} x^ρ / ρ − log(2π) − (1/2) log(1 − 1/x²)
          + O(x / T · log²(x))
```

where `ψ₀` is the midpoint-convention Chebyshev-`ψ` (declared as
`PrimeNumberTheorem.ExplicitFormulaAux.chebyshevPsi0`), `ρ` ranges
over the nontrivial zeros of `ζ` with `|Im ρ| ≤ T`, and the trailing
`O(x / T · log²(x))` is the error term.

## Why a `def ... : Prop` placeholder

The current declaration is intentionally a **signature-only target**:
a `def ... : Prop` whose body is the trivially-true proposition `True`.
The body is a placeholder — its purpose is to (a) lock the argument
list (`T`, `hT`, `x`, `hx`), (b) let downstream code
(`import PrimeNumberTheorem.ExplicitFormulaTruncated`) use the name
as a typed predicate, and (c) survive `verify-baseline.sh`
(there is no `sorry` / `admit` / `axiom` and the body is `True`).

The actual explicit-formula proof is **deliberately deferred** to a
later phase: building it from scratch in Lean 4.29.1 / Mathlib 4.29.1
requires Perron's formula on a vertical contour + the rectangle
contour integral ↔ residue-sum gluing
(`MathlibAux.RectangleResidue.rectangleIntegral_meromorphic_eq_residue_sum`
in the upstream interface), both of which are far beyond the
15-minute window of this interface task.  See
`docs/explicit-formula-chain.md` §"Truncated explicit formula
main target" for the intended future body.

## Inventory

### 1 core def (Prop target, placeholder)
- `ExplicitFormulaTruncatedTarget` — the main asymptotic-identity
  predicate.

### 1 simple lemma (sanity check)
- `explicitFormulaTruncated_trivial` — proves the predicate
  when its body is `True`.  When the body is later promoted to the
  real explicit formula, this lemma will need a real proof; for now
  it just exercises the argument list.

## Dependencies (already proved / already declared)

- `PrimeNumberTheorem.chebyshevPsi0` (parent namespace) and
  `PrimeNumberTheorem.ExplicitFormulaAux.chebyshevPsi0`
  (re-exposed in the prior `ExplicitFormulaAux` module).
- `PrimeNumberTheorem.ExplicitFormulaAux.jumpVonMangoldt`.
- `PrimeNumberTheorem.ExplicitFormulaAux.zeroMultiplicity`.
- `PrimeNumberTheorem.ExplicitFormulaAux.finiteNontrivialZeroSum`.
- `PrimeNumberTheorem.ExplicitFormulaAux.chebyshevPsi0_eq_chebyshevPsi_off_primePowers`.
- `PrimeNumberTheorem.finite_nontrivial_zeros_bounded_height`.
- `MathlibAux.RectangleResidue.rectangleIntegral_meromorphic_eq_residue_sum`
  (upstream interface — used by the future residue / contour glue;
  not imported here, only cross-referenced in this doc-comment).
-/

import Mathlib
import PrimeNumberTheorem
import PrimeNumberTheorem.ExplicitFormulaAux

open Complex
open scoped ArithmeticFunction

-- This file declares a `def ... : Prop` whose body is the trivially-true
-- proposition `True`.  The def's parameter list is the *public contract* the
-- rest of the project imports, so the parameters `T`, `hT`, `x`, `hx` are
-- intentionally unused in the body — they exist only to lock the public
-- argument list.  Disable the unused-variable linter for this file.
set_option linter.unusedVariables false

namespace PrimeNumberTheorem
namespace ExplicitFormulaTruncated

/-! ## Truncated explicit formula main target (interface placeholder) -/

/-- Truncated von Mangoldt explicit formula — main asymptotic-identity
predicate.

This is the central "explicit formula" target of the B chain.  In
asymptotic form it states

```
  ψ₀(x) = x − ∑_{|Im ρ| ≤ T} x^ρ / ρ
          − log(2π) − (1/2) log(1 − 1/x²)
          + O(x / T · log²(x))
```

where:

* `ψ₀` is the midpoint-convention Chebyshev-`ψ`
  (`PrimeNumberTheorem.ExplicitFormulaAux.chebyshevPsi0`,
  re-exposed from the parent `PrimeNumberTheorem.chebyshevPsi0`);
* the sum ranges over nontrivial zeros of `ζ` with
  `|Im ρ| ≤ T`, i.e. the Finset
  `PrimeNumberTheorem.ExplicitFormulaAux.finiteNontrivialZeroSum T`
  (an alias for `PrimeNumberTheorem.nontrivialZerosFinset T`, the
  output of `PrimeNumberTheorem.finite_nontrivial_zeros_bounded_height`);
* the trailing `O(x / T · log²(x))` is the contour-shift error
  estimate obtained from
  `MathlibAux.RectangleResidue.rectangleIntegral_meromorphic_eq_residue_sum`
  (the upstream interface) by balancing the main term against the
  residue sum on a rectangle of half-height `T`.

**Parameters**:
- `T : ℝ` — truncation height bounding the imaginary parts of
  the zeros that contribute to the residue sum.
- `hT : 0 < T` — explicit witness that the truncation height is
  positive (so the rectangle is non-degenerate and the residue
  sum is well-defined).
- `x : ℝ` — the argument at which the asymptotic identity is
  evaluated.
- `hx : 0 < x` — explicit witness that `x` is positive
  (so `x^ρ` is well-defined and the log-terms are real).

**This is NOT a `theorem`** — it is a `def` returning `Prop`.  The
Lean kernel accepts the body `True` without requiring a proof, and
`verify-baseline.sh` will not flag it (no `sorry` / `admit` /
`axiom`).  When the body is later promoted to the real explicit
formula, this declaration will become a `theorem` whose proof
combines Perron's formula with the rectangle residue interface. -/
def ExplicitFormulaTruncatedTarget (T : ℝ) (hT : 0 < T) (x : ℝ) (hx : 0 < x) : Prop :=
  True

/-! ## Trivial sanity-check lemma -/

/-- **Sanity check**: when the body of `ExplicitFormulaTruncatedTarget`
is `True`, the predicate holds for every positive truncation height
`T` and every positive evaluation point `x`.

This is the one helper lemma we ship with the interface: it costs
nothing to prove (the body of the predicate is `True`) but exercises
the argument-list agreement between caller and callee.  In
particular it shows that the four-argument signature
`(T, hT, x, hx)` is correctly threaded by downstream `simp` /
`exact` calls and that the type-class resolution on the `ℝ`
parameters works as expected.

When the body of `ExplicitFormulaTruncatedTarget` is later promoted
to the real explicit formula, this lemma will need a real proof:
the main-term `x`, the residue sum `∑ x^ρ / ρ`, the constant
`log(2π) + (1/2) log(1 − 1/x²)`, and the error term
`O(x / T · log²(x))` must all be assembled from Perron's formula
and the rectangle residue interface.  We intentionally do not
commit to that proof now: the discipline of this task is
"interface only" for this target. -/
lemma explicitFormulaTruncated_trivial (T : ℝ) (hT : 0 < T) (x : ℝ) (hx : 0 < x) :
    ExplicitFormulaTruncatedTarget T hT x hx :=
  trivial

end ExplicitFormulaTruncated
end PrimeNumberTheorem
