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
zeta-zero clusters.  The finite-cluster contribution is also connected by an
exact finite-height explicit-formula identity to the actual standard
Chebyshev-`psi` second moment, with the complete concrete remainder retained as
a subtraction term.  A further theorem-level chain removes jump terms almost
everywhere, bounds the closed terms, selects one good height for every real
sample in a fixed logarithmic window, and makes the normalized finite-height
approximation remainder uniformly arbitrarily small on that window and
arbitrarily small in its local second moment.
It does not prove the Riemann Hypothesis, independently reprove Selberg's
`T log T` result through this repository's native mollifier/MWKF route, or
provide numerically explicit values for the existential remainder constants.
The Selberg target and the definitionally equivalent legacy Conrey-named alias
are nevertheless closed inside this repository's kernel through the
independently machine-checked Anthropic Zeta23 Theorem B; that external
analytic input must remain explicit in every publication claim. Conrey's
genuine strict `> 2/5` simple-zero theorem remains open.

## Current Verified Baseline

- Lean toolchain: `leanprover/lean4:v4.33.0-rc2` (`main`)
- Build command: `lake build`
- Last full Lean baseline: record the current commit and fresh `lake build`
  output in the release log
- Current code-level `sorry` count: 0
- Tracked mathematical `def ... : Prop` targets: 15
  (2 of these -- `selberg_odd_zero_proportion_target` and
  `KnownResults.conrey_40_percent_zeros_on_critical_line_target` -- are
  closed by the verified Anthropic `zeta-23-lean` Theorem B through the
  in-repo bridge `HardyTheorem.Zeta23SelbergBridge`, which imports the
  vendored, axiom-clean `Zeta23` library and closes both targets inside
  this repository's kernel; see
  [zeta23-selberg-bridge.md](docs/research/zeta23-selberg-bridge.md)); the
  inventory also includes the two unproved `FiniteSpectrumGap` target forms
- Route-interface `def ... : Prop` declarations: 6
- Reusable Prop predicates: 197
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
classified, checks the 15-item mathematical target inventory, and validates the
four chain-gap buckets. The ordinary PNT, de la Vallee Poussin-form `psi` and
`pi-Li` errors, Hardy's theorem, Riemann--von Mangoldt, Carlson zero density,
local-separation estimates, Hardy--Littlewood linear lower bounds, the Pintz
envelope, and the implication from a right-of-critical-line zero to
strict-beyond-`pi/2` oscillation in every late fixed-epsilon power window are
theorem-level.  The resulting linear local second-moment lower bound and the
finite-zero-cluster coercivity inequalities are also theorem-level.  The
fixed-proportion large-value theorem explicitly assumes an external fourth
moment bound.  The actual finite-height complement is now defined and the
exact `psi` transfer is theorem-level.  The finite-height approximation, jump,
and closed-term pieces now have fixed-window control, but no theorem yet
controls the complementary zero package strongly enough for the strict
positivity endpoint; the detector-energy gate also remains open. RH,
Vinogradov--Korobov, a repository-native Selberg/MWKF reproof independent of
Zeta23, and any unconditional power-saving error below exponent `2/3` remain
outside the proved boundary. The Zeta23-based Selberg and legacy-alias closure
is inside the kernel but must be attributed as an external machine-checked
analytic input. Conrey's genuine strict two-fifths simple-zero target remains
outside the proved boundary.

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
coercivity and an exact actual-psi second-moment transfer with a visible
finite-height remainder, together with a uniform fixed-log-window theorem
making the normalized finite-height approximation remainder arbitrarily small
at one shared good height, both pointwise and in local `L2`.
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
finite-zero-cluster coercivity estimates and an exact finite-height
explicit-formula transfer to the actual psi second moment, plus uniform
fixed-log-window decay of the normalized finite-height approximation remainder,
including its local second moment, proved in Lean 4
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
- infrastructure with theorem-level identities: explicit target-pair
  identification, annihilator transfer, finite-cluster coercivity, and the
  exact actual-`psi` second-moment lower bound after subtracting the concrete
  remainder; the approximation, jump, and closed-term pieces have fixed-window
  control, including local `L2` smallness of the approximation piece, but the
  complementary zero package does not.

For the PR #474 windowed-detector and single-layer-forcing route, keep a
separate boundary:

- theorem-level: Mellin response and cubic-kernel identities, detection-point
  choice, L3 mass/contradiction transfers, sharp-witness transfers, and the
  Carlson contradiction after a forcing lower count is supplied;
- still external to the closure: a concrete proof of
  `CubicLineForcingAssumption.lower` from `DirectL2` plus the two-height
  capacity inputs, and a `GateAssemblyInput` supplier for every feasible
  parameter tuple;
- forbidden publication claim: an unconditional `Re(rho) <= 14/17` or
  `Re(rho) <= 2/3` theorem.

See
[`2026-08-24-pr474-windowed-detector-single-layer-forcing.md`](docs/research/2026-08-24-pr474-windowed-detector-single-layer-forcing.md).

For the merged PR #478--#482 Selberg/MWKF research records, keep a third
boundary:

- audited on `main`: the Selberg--Möbius LCM main term, exact mollified AFE and
  off-diagonal reindexing, the published-coverage map, and finite exact models
  for the centered Möbius Type-I/II and Farey reductions;
- still unproved: the global coupled operator estimate, the centered
  Möbius--Farey trilinear estimate with the required saving, and the independent
  transform-tail obligation;
- forbidden publication claim: an unconditional `N=T^3` long-mollifier
  asymptotic or a new theorem-level Selberg proof derived only from those
  research documents and Python scripts.

See
[`2026-08-24-mobius-weighted-off-diagonal.md`](docs/research/2026-08-24-mobius-weighted-off-diagonal.md),
[`2026-08-24-mwkf-published-coverage.md`](docs/research/2026-08-24-mwkf-published-coverage.md),
and
[`2026-08-24-mwkf-global-coupled-coefficient-first.md`](docs/research/2026-08-24-mwkf-global-coupled-coefficient-first.md).

## Unproved Target Statements

| File | Remaining `sorry` count | Main target statements |
|---|---:|---|
| `ZeroFreeRegion.lean` | 0 | Classical `c/log |t|` region proved; Vinogradov-Korobov remains a target |
| `HardyTheorem.lean`, `HardyTheorem/CriticalLineMultiplicity.lean`, `HardyTheorem/ConreySimpleZeroCount.lean` | 0 | Hardy and Hardy--Littlewood linear lower bounds and the independent Selberg theorem are proved; Zeta23 closes the Selberg target and legacy Conrey-named alias, while the genuine strict `> 2/5` simple-zero target and its long-mollifier analytic gate remain open |
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
  `v4.33.0-rc2` (commit `51e6992efd06126df61a496bebf8f49482a4e129`); the
  instructions in `INSTALL.md` already cover this.

The first option is preferable for review and archiving.
