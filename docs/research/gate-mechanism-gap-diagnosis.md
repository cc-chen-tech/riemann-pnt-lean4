# Gate mechanism gap diagnosis

## Status

Diagnosis of the unclosed inputs of the amplification gate
(`PrimeNumberTheorem/ExceptionalZeroAmplificationGateContract.lean`), based on
a full read of the assembly layer
(`HalfIsolatedZeroDichotomy/{Contract,Audit}.lean`,
`ZeroForcedOscillationComplementaryBound.lean`,
`ZeroDensityAmplificationAudit*.lean`,
`VKEdgeConditionalPackage.lean`) and the budget experiments in
`gate-amplification-budget-numerics.md`.  Diagnosis only; no new theorems.

## The gate inputs and who could supply them

| input | candidate supplier | status |
|-------|--------------------|--------|
| `hroots` | reverse assumption (a seed `rho_0`, `beta > 2/3` exists) | trivial assembly |
| `hbranch` | (a) combinatorial dichotomy doubling, (b) window-energy forcing, (c) multi-window detector | **none gives growth in T** |
| `hdisjoint` | `topLayerWindow_pairwise_disjoint_of_centers` (2δ separation) | structural, fine |
| `C` + `hlower` | `halfIsolatedDichotomy_zeroDensityAdapter`, window accounting | structural, fine |
| `hgap` | needs `q(T)^depth` to beat `C (T+H)^(4σ(1-σ)) log^4` | fails for constant `q` |

## Gap 1: no growth source for q(T)

- The dichotomy endpoint (`halfIsolatedDetectorClusterEndpoint`) gives at most
  doubling: `2 * centers.card <= zset.card`, a **constant** branch factor.
- The Lean no-go
  `one_offline_zero_certificate_does_not_yield_diverging_gap` proves a
  single-window/single-zero certificate can never satisfy `hgap`.
- The window-energy route gives `e_M > 0` only for `beta > 10/13`
  (numerics in `gate-amplification-budget-numerics.md`), and even there it
  forces a *density* of successors that a top-layer set bounded by the global
  count cannot host unless the forcing is real.
- Candidate repair (a): multi-window detector — run the detector in `H/delta`
  separated height windows per layer, giving `q(T) = H/delta = T^(h-kappa)`.
  Requires the detector to force a top-layer zero *inside a prescribed height
  window*, which the current detector does not do.

## Gap 2: no imaginary-part control of forced zeros

- The detector input `HalfIsolatedSimplifiedDetectorInput T` (Audit.lean:107)
  forces existence of a top-layer (real part `beta`) zero somewhere below `T`,
  with no height window.
- The directed step needs strictly higher imaginary parts; the one-step lemma
  `halfIsolatedOneStepAdvanceFromEndpoint` (Audit.lean:583) takes `hdrift`
  (`window zeros other than rho have larger imaginary part`) as a hypothesis.
- The stall theorem
  `halfIsolatedDirectedIteration_stall_under_equal_im_topLayer` shows what
  happens without it: equal-imaginary top layer blocks ascent.
- Candidate repair: derive `hdrift` from a Gram/Schur-type regularity of the
  top-layer imaginary distribution (half-isolated-dyadic-gram-schur line), or
  replace the directed order by a detector-window order that does not need it.

## Gap 3: the (2/3, 10/13] blind strip of the energy route

- `e_M = 2 lam (beta-sigma)/gamma - q(sigma) - theta` is positive exactly for
  `beta > 10/13` (theta = 0, sigma -> 2/3+, gamma -> g); the coherent capacity
  `sum m^2/|rho|^2 <= T^(q-2) log^5` is the bottleneck.
- The separation (orthogonal) model does not help: its capacity is still
  governed by the same zero-density exponent `q(sigma)`.
- Candidate repairs: (i) a capacity bound strictly better than
  `T^(q(sigma)-2)` for the *window-localized* mass (e.g. using the
  half-isolated phase structure); (ii) accept the strip and prove the gate
  only for `beta > 10/13` (partial result); (iii) a different forcing
  mechanism (detector multi-window) that does not pass through density at all.

## Consequences

- The assembly (gaps in `hbranch`/`hgap` aside) is complete and mergeable;
  see `merge-path-amplification-audit.md`.
- The next research loop should attack Gap 1/2 jointly (multi-window detector
  with height control), because that route, if it works, closes the gate for
  **all** `beta > 2/3` and does not need the energy route's density bottleneck.
- Gap 3 remains as a fallback/partial-result option (`beta > 10/13`).

## Boundaries

Diagnosis only; no theorem-level novelty is claimed for the candidate repairs.
