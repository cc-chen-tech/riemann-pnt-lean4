# Half-Isolated Zero Dichotomy — Prior-Art & Interface Audit

Status date: 2026-07-25  
Worktree: `/Users/luicy/AI/Riemann/riemann-pnt-lean4/.worktrees/half-isolated-zero-dichotomy`  
Branch: `research/half-isolated-zero-dichotomy`  
Baseline commit: `029d3376ae91ab2fb4f2a281bfaf1f6ad9687f07`  

## Scope boundary (phase 0)

This document records what can be reused now and what is still an interface gap.
No RH-level consequence is claimed.

## Existing reusable prior art

- `PrimeNumberTheorem.nontrivialZerosFinset` and `PrimeNumberTheorem.mem_nontrivialZerosFinset`: finite zero list at a fixed height cutoff.
- `RiemannHypothesis.IsNontrivialZero`: base object for nontrivial zeros and their strip bounds.
- `PrimeNumberTheorem.GlobalZeroCount` and `PrimeNumberTheorem.ZeroDensityCount`:
  finite zero-count identities and explicit height-summation bounds over `nontrivialZerosFinset`.
- `PrimeNumberTheorem.NontrivialZeroMultiplicity`:
  local multiplicity identities (`analyticOrderNatAt`) and divisor-type identities usable as finite cluster mass counters.
- `PrimeNumberTheorem.LocalSeparationKernel`:
  separation-from-identity infrastructure and local-separation list machinery.
- `PrimeNumberTheorem.CarlsonDetectorCount` and `PrimeNumberTheorem.CarlsonDetectorGrowth`:
  finite zero support and finite-difference separation estimates that can become
  arithmetic inputs in the cluster branch.
- `PrimeNumberTheorem.ExplicitFormulaAux`, `PrimeNumberTheorem.ExplicitFormulaAllHeights`:
  exact finite-height explicit-formula decomposition on nontrivial-zero support.
- `PrimeNumberTheorem.QuantitativeGoodHeight`:
  good-height existence and height-comparison primitives.
- `PrimeNumberTheorem.LocalSeparationKernel` + Fourier-separation files:
  existing frequency-gap normalization and tail lemmas compatible with cluster
  diameter-to-separation conversion.

## Interface friction and required wrapper modules

1. **Top-layer selector**
   - Need a stable API for "most-right strip layer at height `T`": current files provide
     finite zero supports and membership lemmas, but no dedicated named
     proposition for "is rightmost real part at cut height".

2. **Dichotomy statement packaging**
   - `Maynard–Pratt` must enter as an explicit assumption/API.
   - Current code does not already contain a ready-made `half-isolated ∨ local cluster`
     theorem at this exact interface.

3. **Cluster representation**
   - No generic `Cluster` structure currently carries both:
     finite cardinal data, height window, gap radius, and an explicit
     center zero certificate.

4. **Iterative amplification route**
   - Local pairwise/weight calculations are present, but there is no direct route from
     one bounded local cluster certificate to a structured chain of many distinct top-layer
     zeros with uniform gap control.

## Missing lemmas for "cluster -> many distinct zeros" (phase-1 targets)

Label each target as a required interface bridge:

- **[A] Analytic input**: convert local finite cluster geometric bounds into
  explicit lower bounds for cumulative multiplicity/weighted mass on that layer.
- **[I] Iteration interface**: from one certified local cluster, construct a
  canonical sequence/subset of distinct top-layer zeros with explicit pairwise
  control and increasing index map.
- **[C] Combinatorial identity**: identify and freeze the exact identity that
  rewrites finite sums over one zero-cluster into multiplicity-weighted package
  terms compatible with future lower-bound arguments.
- **[T] Conditional theorem shape**: condition on a concrete detector output and
  derive a one-line theorem of form  
  `rightmost zero at height T` `->` `half-isolated ∨ cluster`.

## Deliverable plan extracted from audit

- Create a strict contract file for:
  `half-isolated` predicate, `local cluster` predicate, and the `Maynard–Pratt`
  detector assumption API.
- Create an explicit audit interface file listing unresolved assumptions as
  typeclass fields to avoid informal placeholders.
- Keep all downstream formal statements under the new path prefix only:
  `docs/research/half-isolated-zero-dichotomy-*`,
  `PrimeNumberTheorem/HalfIsolatedZeroDichotomy*.lean`.
