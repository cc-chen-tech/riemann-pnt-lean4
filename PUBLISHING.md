# Publishing Readiness

This repository is currently a buildable Lean 4 formalization framework, not a
completed proof of the Prime Number Theorem or the Riemann Hypothesis.

## Current Verified Baseline

- Lean toolchain: `leanprover/lean4:v4.29.1`
- Build command: `lake build`
- Last verified local result: `Build completed successfully (8262 jobs).`
- Current code-level `sorry` count: 0
- Remaining mathematical `def ... : Prop` targets: 22
- Route-interface `def ... : Prop` declarations: 4
- Reusable Prop predicates: 2
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
classified, checks the 22-item mathematical target inventory, and validates the
four chain-gap buckets. This does not mean the PNT or RH has been proved:
several deep results are recorded only as `def ... : Prop` targets.

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
Verified Lean 4 infrastructure for the de la Vallee Poussin 3-4-1 machinery
and a compact zero-free strip, complementary to existing PNT formalizations by
other routes.
```

Do not claim:

- first formalization of PNT;
- completed formalization of the original analytic PNT proof;
- proof of the classical quantitative zero-free region `1 - c / log |t|`;
- proof of the full PNT, RH, or RH-equivalent prime-counting error terms;
- completion of any `def ... : Prop` target unless it has been replaced by a
  checked theorem/lemma.

## Maturity Boundary

For public positioning, treat the current repository as:

```text
proved front half of the de la Vallee Poussin zero-free-region machinery
```

not as:

```text
near-complete PNT proof
```

The immediate mathematical blocker is the boundary-strip zeta estimate, not the
documentation layer:

```lean
∃ B T0, ∀ z : ℂ,
  1 ≤ z.re → z.re ≤ 2 → T0 ≤ |z.im| →
  ‖logDeriv riemannZeta z‖ ≤ B * Real.log |z.im|
```

Together with a zero-candidate regular-part estimate for `-ζ'/ζ`, this would
feed the existing conditional zero-free-region closures.  Until these estimates
are proved in Lean, the correct publishable claim remains the local
`3-4-1 + compact zero-free strip` module.

## Unproved Target Statements

| File | Remaining `sorry` count | Main target statements |
|---|---:|---|
| `ZeroFreeRegion.lean` | 0 | Compact zero-free region proved; quantitative zero-free regions remain targets |
| `HardyTheorem.lean` | 0 | Hardy-Z phase facts proved; corrected integral asymptotics and zero-counting consequences remain targets |
| `PrimeNumberTheorem.lean` | 0 | Bounded-height zero finiteness proved; RH error equivalence and explicit formula remain targets |

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
