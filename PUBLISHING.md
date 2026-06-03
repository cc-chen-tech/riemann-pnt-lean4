# Publishing Readiness

This repository is currently a buildable Lean 4 formalization framework, not a
completed proof of the Prime Number Theorem or the Riemann Hypothesis.

## Current Verified Baseline

- Lean toolchain: `leanprover/lean4:v4.29.1`
- Build command: `lake build`
- Last verified local result: `Build completed successfully (8255 jobs).`
- Current code-level `sorry` count: 0

## Required Gates Before Public Mathematical Claims

Run these checks before tagging a release, submitting a paper, or making a
strong mathematical claim about the repository.

```bash
./scripts/verify-baseline.sh

lake build
python3 scripts/list-prop-targets.py
rg -n '\\b(sorry|admit|axiom)\\b' *.lean
```

The commands should return a stable 23-item target inventory and no placeholders
(`sorry`/`admit`/`axiom`) in Lean sources. This does not mean the PNT or RH has
been proved: several deep results are recorded only as `def ... : Prop` targets.

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
