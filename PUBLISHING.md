# Publishing Readiness

This repository is a buildable Lean 4 formalization that proves the ordinary
Prime Number Theorem and a classical de la Vallee Poussin-form Chebyshev `psi` remainder
through the de la Vallee Poussin route. It does not prove the Riemann
Hypothesis or the corresponding prime-counting `pi-Li` remainder of the same shape.

## Current Verified Baseline

- Lean toolchain: `leanprover/lean4:v4.29.1`
- Build command: `lake build`
- Last verified local result: see the current verification log before release
- Current code-level `sorry` count: 0
- Remaining mathematical `def ... : Prop` targets: 16
- Route-interface `def ... : Prop` declarations: 5
- Reusable Prop predicates: 10
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
classified, checks the 16-item mathematical target inventory, and validates the
four chain-gap buckets. The ordinary PNT and de la Vallee Poussin-form
Chebyshev `psi` error are theorem-level; RH, Hardy, Vinogradov-Korobov, and the `pi-Li`
endpoint remain outside the proved boundary.

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
Verified Lean 4 formalization of the de la Vallee Poussin 3-4-1 machinery, the
classical c/log zero-free region, and the resulting ordinary PNT and
de la Vallee Poussin-form Chebyshev psi remainder through a multiplicity-aware
moving-height explicit formula.
```

Do not claim:

- first formalization of PNT;
- proof of the corresponding prime-counting `pi-Li` remainder;
- proof of RH or RH-equivalent prime-counting error terms;
- completion of any `def ... : Prop` target unless it has been replaced by a
  checked theorem/lemma.

## Maturity Boundary

For public positioning, treat the current repository as:

```text
ordinary PNT proved through the de la Vallee Poussin zero-free-region and
moving-height explicit-formula machinery, with a de la Vallee Poussin-form
Chebyshev `psi` remainder
```

not as:

```text
proof of RH or the corresponding prime-counting `pi-Li` remainder
```

The next stronger zero-free-region blocker is exponential-sum input for the
Vinogradov-Korobov width. It is not needed for the now-proved ordinary PNT.

## Unproved Target Statements

| File | Remaining `sorry` count | Main target statements |
|---|---:|---|
| `ZeroFreeRegion.lean` | 0 | Classical `c/log |t|` region proved; Vinogradov-Korobov remains a target |
| `HardyTheorem.lean` | 0 | Hardy-Z phase facts proved; corrected integral asymptotics and zero-counting consequences remain targets |
| `PrimeNumberTheorem.lean`, `PrimeNumberTheorem/PNTFromDynamicPerron.lean`, and `PrimeNumberTheorem/ClassicalPNTError.lean` | 0 | Ordinary PNT and the de la Vallee Poussin-form Chebyshev `psi` remainder proved; the corresponding `pi-Li` remainder and unconditional RH-scale predicates remain open |

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
