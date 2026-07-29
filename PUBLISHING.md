# Publishing Readiness

This repository is a buildable Lean 4 formalization that proves the ordinary
Prime Number Theorem and classical de la Vallee Poussin-form remainders for
Chebyshev `psi` and prime counting `pi-Li`, Hardy's theorem, the all-height
Riemann--von Mangoldt formula, Carlson's fixed-`sigma` zero-density estimate,
local-separation Hilbert/mean-square estimates, Hardy--Littlewood linear lower
bounds, divergence of a Pintz zero envelope, and the implication from a
right-of-critical-line zero to a strict-beyond-`pi/2` PNT-error oscillation in
every sufficiently late `[Y,Y^(1+epsilon)]` window for fixed `epsilon > 0`.
It also proves a linear ordinary local second-moment lower bound in every such
late window and collision-safe, phase-coercive local `L2` estimates for finite
zeta-zero clusters.
It does not prove the Riemann Hypothesis, Selberg's `T log T` result, or
provide numerically explicit values for the existential remainder constants.

## Current Verified Baseline

- Lean toolchain: `leanprover/lean4:v4.29.1`
- Build command: `lake build`
- Last verified local result: see the current verification log before release
- Current code-level `sorry` count: 0
- Remaining mathematical `def ... : Prop` targets: 12
- Route-interface `def ... : Prop` declarations: 5
- Reusable Prop predicates: 48
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
classified, checks the 12-item mathematical target inventory, and validates the
four chain-gap buckets. The ordinary PNT, de la Vallee Poussin-form `psi` and
`pi-Li` errors, Hardy's theorem, Riemann--von Mangoldt, Carlson zero density,
local-separation estimates, Hardy--Littlewood linear lower bounds, the Pintz
envelope, and the implication from a right-of-critical-line zero to
strict-beyond-`pi/2` oscillation in every late fixed-epsilon power window are
theorem-level.  The resulting linear local second-moment lower bound and the
finite-zero-cluster coercivity inequalities are also theorem-level.  The
fixed-proportion large-value theorem explicitly assumes an external fourth
moment bound; the full explicit-formula complement and detector-energy gates
remain open. RH, Vinogradov--Korobov,
Selberg positive proportion, and any
unconditional power-saving error below exponent `2/3` remain outside the
proved boundary.

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
local-separation Hilbert/mean-square infrastructure, together with
Hardy--Littlewood linear critical-line-zero lower bounds, a divergent Pintz
zero envelope, and right-of-critical-line-zero-forced PNT oscillation beyond
pi/2 and a linear local second-moment lower bound in every sufficiently late
fixed-epsilon power window, plus collision-safe finite-zero-cluster local L2
coercivity.
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
Hilbert/mean-square infrastructure, Hardy--Littlewood linear lower bounds,
Pintz envelope divergence, and the implication from a right-of-critical-line
zero to strict-beyond-pi/2 PNT oscillation in every sufficiently late
fixed-epsilon power window, together with linear local second-moment and
finite-zero-cluster coercivity estimates, proved in Lean 4
```

not as:

```text
proof of RH or a power-saving prime error below exponent `2/3`
```

The next stronger zero-free-region blocker is the Ford short-sum layer for the
Vinogradov-Korobov width. The exponential-sum/zeta blocks, prime-power
conditioning, mixed moments, and coupled-tail recurrences are merged, but the
tent-kernel localization, smooth-support estimates, and final parameter
optimization remain open.  The merged residue-mass audit proves that, for
constant coefficients on complete prime-power blocks, normalized moments
recover the usual Holder cardinality loss when converted back to raw moments;
normalization alone therefore supplies no exponent saving. None of these are
needed for the now-proved ordinary PNT.

For the zero-forced oscillation route, distinguish three trust levels:

- unconditional theorem-level: strict-beyond-`pi/2` local oscillation and the
  linear ordinary local second-moment lower bound, conditional only on the
  existence of the stated off-line zeta zero;
- conditional theorem-level: fixed-proportion large values assuming the
  displayed external fourth-moment bound;
- infrastructure: explicit target-pair identification, annihilator transfer,
  and finite-cluster coercivity, without a completed global complement/remainder
  estimate.

## Unproved Target Statements

| File | Remaining `sorry` count | Main target statements |
|---|---:|---|
| `ZeroFreeRegion.lean` | 0 | Classical `c/log |t|` region proved; Vinogradov-Korobov remains a target |
| `HardyTheorem.lean`, `HardyTheorem/CriticalLineMultiplicity.lean` | 0 | Hardy and Hardy--Littlewood linear lower bounds proved; Selberg's `T log T` and Conrey-style percentage estimates remain open |
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
