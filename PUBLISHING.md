# Publishing Readiness

This repository is a buildable Lean 4 formalization that proves the ordinary
Prime Number Theorem and classical de la Vallee Poussin-form remainders for
Chebyshev `psi` and prime counting `pi-Li`, Hardy's theorem, the all-height
Riemann--von Mangoldt formula, Carlson's fixed-`sigma` zero-density estimate,
and local-separation Hilbert/mean-square estimates. It does not prove the
Riemann Hypothesis or provide numerically explicit values for the existential
remainder constants.

## Current Verified Baseline

- Lean toolchain: `leanprover/lean4:v4.29.1`
- Build command: `lake build`
- Last verified local result: see the current verification log before release
- Current code-level `sorry` count: 0
- Remaining mathematical `def ... : Prop` targets: 13
- Route-interface `def ... : Prop` declarations: 5
- Reusable Prop predicates: 13
- Unclassified Prop declarations: 0

## Required Gates Before Public Mathematical Claims

Run these checks before tagging a release, submitting a paper, or making a
strong mathematical claim about the repository.

```bash
./scripts/verify-baseline.sh

python3 -m pytest
python3 scripts/list-prop-targets.py
```

The baseline script runs `lake build`, recursively scans project Lean sources
for real placeholder proof forms, checks that every `def ... : Prop` is
classified, checks the 13-item mathematical target inventory, and validates the
four chain-gap buckets. The ordinary PNT, de la Vallee Poussin-form `psi` and
`pi-Li` errors, Hardy's theorem, Riemann--von Mangoldt, Carlson zero density,
and local-separation estimates are theorem-level. RH, Vinogradov--Korobov,
Selberg positive proportion, and any unconditional power-saving error below
exponent `2/3` remain outside the proved boundary.

As of the current baseline, no route interface has a body equal to `True`.
`MathlibAux.rectangleIntegral_meromorphic_eq_residue_sum` is still an explicit
marker for missing rectangle deformation infrastructure.  Its body is an
existential certificate, not a theorem derivable from the radius hypothesis.
The local finite simple-pole circle residue formula is now theorem-level; the
rectangle-to-circles deformation remains open.

## Required SOTA Check Before Public Claims

Before a paper, release note, README headline, talk abstract, or arXiv
submission makes a novelty claim, check the external baseline separately from
the local Lean target inventory.

Minimum external comparison set:

- Isabelle/HOL formalizations of the elementary PNT;
- HOL Light formalization of Newman's analytic PNT proof;
- Lean `PrimeNumberTheoremAnd`;
- Mathlib's `riemannZeta`, Euler product, functional equation, nonvanishing,
  and Dirichlet `L`-function infrastructure;
- newer Lean PNT repositories current at submission time.

Allowed claim shape:

```text
Verified Lean 4 formalization of classical analytic number theory for the
Riemann zeta function, including the de la Vallee Poussin zero-free region and
Strong PNT remainder, Hardy's theorem, the all-height Riemann--von Mangoldt
formula, Carlson's fixed-sigma zero-density estimate, and reusable
local-separation Hilbert/mean-square infrastructure.
```

Do not claim:

- first formalization of PNT;
- numerically explicit values for the existential remainder constants;
- proof of RH or RH-equivalent prime-counting error terms;
- completion of any `def ... : Prop` target unless it has been replaced by a
  checked theorem/lemma.

## Maturity Boundary

For public positioning, treat the current repository as:

```text
classical zero-free region, Strong PNT, Hardy theorem, all-height
Riemann--von Mangoldt, fixed-sigma Carlson zero density, and local-separation
Hilbert/mean-square infrastructure proved in Lean 4
```

not as:

```text
proof of RH or a power-saving prime error below exponent `2/3`
```

The next stronger zero-free-region blocker is exponential-sum input for the
Vinogradov-Korobov width. It is not needed for the now-proved ordinary PNT.

## Unproved Target Statements

| File | Remaining `sorry` count | Main target statements |
|---|---:|---|
| `ZeroFreeRegion.lean` | 0 | Classical `c/log |t|` region proved; Vinogradov-Korobov remains a target |
| `HardyTheorem.lean` | 0 | Hardy's infinite-zero theorem proved; Hardy--Littlewood and Selberg quantitative extensions remain targets on `main` |
| `PrimeNumberTheorem.lean`, `PrimeNumberTheorem/PNTFromDynamicPerron.lean`, `PrimeNumberTheorem/ClassicalPNTError.lean`, and `PrimeNumberTheorem/ClassicalPrimeCountingError.lean` | 0 | Ordinary PNT and the de la Vallee Poussin-form `psi` and `pi-Li` remainders proved; unconditional RH-scale predicates remain open |

## Release Dependency Issue

The current local build uses:

```lean
require mathlib from "./vendor/mathlib"
```

This is a local build-stability workaround. Since `vendor/mathlib` is ignored
by git, a public release should either:

- switch `lakefile.lean` back to a pinned Mathlib git dependency and regenerate
  `lake-manifest.json`, or
- provide explicit instructions for reconstructing `vendor/mathlib` at Mathlib
  4.29.1.

The first option is preferable for review and archiving.
