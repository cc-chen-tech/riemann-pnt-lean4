# Weil Interval Assembly Design

Status: design record, 2026-07-21

## Purpose

This document records the design decisions for closing link 1 of the
preregistered Weil certificate chain in
`docs/research/weil-extremal-kernel-preregistration.md`: the intervalized
dual-route assembly of the cutoff-free full matrix `Q_full(c, N)`. It covers
the unified artifact pattern, the two independent assembly routes, the
overlap-as-intersection and symmetrization semantics, the validation baseline,
and the progression plan from small `N` to the registered `(c, N) = (100, 200)`
Gate A calibration.

## Claim Boundary

The existing repository evidence for this line is a high-precision
point-value cross-check only. The frozen artifact
`experiments/rh/reference/groskin_2607_02828_v1_small_n_high_precision_crosscheck.json`
records mpmath point values at 70 or more significant digits for every ordered
entry at `(c, N) = (13, 4)` and `(13, 8)`. Neither route currently emits
outward-rounded interval enclosures. The intervalized artifacts described here
are under construction and no such artifact has been produced yet. Gate A
remains open: there is no entrywise interval overlap, no exact rational LDL
certificate replay against an analytic enclosure, no analytic transfer margin,
and no 512-bit-separated narrowing record for entry enclosures. Nothing in
this document is a proof of the Riemann Hypothesis, a new positivity theorem,
or a result about `N = 250`.

## Unified Artifact Pattern

Every interval assembly run emits one UTF-8 JSON object per route per
`(c, N, prec_bits)` setting. The schema is

```text
schema_version    = "weil-extremal-kernel-interval-assembly/v1"
c                 = integer cutoff parameter, c >= 2
N                 = integer Fourier cutoff, N >= 0
dimension         = 2*N+1
route             = string identifier of the assembly route
prec_bits         = integer working precision in bits
index_convention  = "fourier -N..N row-major"
entries           = list of (2*N+1)^2 items in row-major order over
                    indices -N, ..., N; each item is a pair [lo, hi] of
                    decimal strings giving a rigorous containing interval
                    for that real matrix entry
provenance        = {generator, note, created_utc}
payload_sha256    = SHA-256 of the canonical JSON of every field above
```

Conventions carried over from the preregistered experiment format:

- Canonical JSON uses sorted keys and comma/colon separators without extra
  spaces, with a terminal newline on disk.
- `lo` and `hi` are decimal strings, never JSON floating-point numbers. The
  values are parsed directly from the outward-rounded Arb decimal
  serialization; no binary floating-point value may intervene between the
  interval arithmetic and the artifact, matching the preregistration's
  invalidating conditions.
- `[lo, hi]` must satisfy `lo <= hi` and must provably contain the exact real
  entry under the documented rounding direction: `lo` is rounded toward
  negative infinity and `hi` toward positive infinity at the serialization
  precision.
- `route` distinguishes the two independent implementations; a single
  artifact never mixes routes.
- `payload_sha256` is computed over the payload excluding the
  `payload_sha256` field itself, exactly as in the existing cross-check
  artifact.

## The Two Assembly Routes

Both routes assemble the same real symmetric matrix `Q_full(c, N)` with
indices `-N, ..., N`, in the normalization frozen by the preregistration
against arXiv:2607.02828v1. Both are fresh implementations that do not import
or call the released `anc/arb_ldlt_certify.py`. The point-value versions live
in `experiments/rh/weil_extremal_crosscheck.py`; the intervalized versions
replace mpmath point arithmetic with python-flint Arb ball arithmetic
(python-flint 0.9.0 in the managed runtime) at a declared `prec_bits`.

1. **Auxiliary S/CC/XC closed form.** Entries are built from the pole block,
   the archimedean diagonal/off-diagonal terms through the auxiliary sequences
   `S`, `CC`, and `XC`, and the prime-power block with weights
   `log p / sqrt(q)` over prime powers `q <= c`. The intervalized route must
   enclose the digamma/trigamma evaluations and the four exponentially
   convergent geometric tail sums, including a rigorous bound for the
   truncation of each tail.
2. **CCM hypergeometric/Lerch closed form.** Entries are built from the
   Connes--Consani--Moscovici `alpha`/`beta`/`gamma` sequences through
   `2F1` hypergeometric values and the Lerch transcendent at
   `z = exp(-2 log c)`, plus the pole block and the prime block. The
   intervalized route must enclose the hypergeometric and Lerch evaluations
   through Arb series with certified error bounds.

The routes share no code path for their transcendental blocks. Their only
shared inputs are the registered parameters `(c, N)`, the index convention,
and the prime-power list, which is exact integer data.

## Overlap-as-Intersection and Symmetrization Semantics

Link 1 requires the two routes' intervals to overlap entrywise. The
combination rule is:

- For each ordered index pair `(i, j)`, let `A_ij = [a_lo, a_hi]` from the
  auxiliary route and `C_ij = [c_lo, c_hi]` from the CCM route. The overlap is
  the intersection `[max(a_lo, c_lo), min(a_hi, c_hi)]`. An empty intersection
  at any entry fails the run with status `INCONCLUSIVE` under preregistered
  Gate C; it is never averaged, widened, or repaired by hand.
- Symmetrization uses intersection, not copying. For each unordered pair
  `{i, j}`, the symmetrized enclosure of both `(i, j)` and `(j, i)` is the
  intersection of the two overlap intervals above. Because the exact matrix
  is symmetric, this intersection is mathematically justified; silently
  copying one triangle over the other is forbidden by certificate-chain
  link 2. If the intersection is empty, the run fails.
- The resulting symmetric interval matrix is the input to the existing
  generic rational-reduction and perturbation-transfer mechanism (second
  milestone) and, after an exact rational center is chosen inside each entry
  interval, to the exact rational LDL checker (first milestone).

## Validation Baseline

The hard correctness test for every intervalized artifact is containment
against the frozen point-value artifact:

- For `(c, N) = (13, 4)` and `(c, N) = (13, 8)`, every matrix entry point
  value recorded in
  `experiments/rh/reference/groskin_2607_02828_v1_small_n_high_precision_crosscheck.json`
  (both routes, at the 70-digit serialization) must lie inside the
  corresponding `[lo, hi]` interval of the intervalized artifact for the same
  route and case, up to the documented half-ulp serialization budget of the
  frozen decimal strings.
- The frozen artifact SHA-256
  `62da7e8d50bea317d3cee154a1fa758a0b0d31939016bc158d13eff9418bca2e`
  is part of the test fixture; the containment test verifies the digest
  before comparing values.
- A containment failure at any entry is a hard failure of the interval
  assembly, because a rigorous outward-rounded enclosure must contain every
  correctly rounded point evaluation of the same formula.

Containment against point values does not itself prove interval rigor; it is
a necessary regression gate. Rigor rests on Arb's certified ball arithmetic
plus the documented truncation bounds for each infinite tail.

## Progression Plan: Small N to N = 200

The intervalized assembly advances in bounded steps:

1. `(c, N) = (13, 4)` and `(13, 8)` on both routes, with the frozen
   containment test above. This exercises every block (pole, archimedean
   diagonal and off-diagonal, prime) at trivial cost.
2. A small-`N` ladder at fixed `c = 13` and then at moderate `c`, checking
   that entrywise overlap holds and that interval widths shrink under a
   precision increase separated by at least 512 bits.
3. The registered Gate A calibration `(c, N) = (100, 200)`, full dimension
   `401`, on both routes. Entry enclosures must be retained in the artifacts
   so that the 512-bit-separated rerun can verify that every entry enclosure
   narrows, which the released upstream metadata cannot establish because it
   records no entry balls.
4. Only after Gate A closes does the `(c, N) = (100, 250)` Gate B search
   begin, under the preregistered strict-improvement rule.

Each step freezes its artifacts with `payload_sha256` and records the replay
command, software versions, and working precision, matching the
preregistration's reproducible-experiment format.

## Correspondence with Gate A

Gate A at `(c, N) = (100, 200)` has five preregistered sub-conditions. Their
status and the role of this design are:

1. **Both assembly routes overlap entrywise.** This document's subject. The
   two intervalized routes and the overlap-as-intersection rule above address
   it. Currently open; only a point-value cross-check exists.
2. **The exact checker accepts the emitted rational LDL certificate.** The
   standard-library exact rational `LDL^T` checker from the first milestone
   is in place and accepts rational artifacts. It has not yet received an
   analytic rational reduction of the Weil interval matrix.
3. **The analytic transfer margin is at least zero.** The generic
   interval-to-center perturbation theorem from the second milestone is in
   place. No Weil entry enclosure instantiates it yet, so no margin has been
   computed.
4. **Two precision settings separated by at least 512 bits preserve the
   certified inertia and narrow every entry enclosure.** The 9000/9512-bit
   same-route replays recorded persistent positive inertia but cannot certify
   narrowing, because the released records retain no entry balls. The
   intervalized artifacts in this design retain `[lo, hi]` for every entry,
   which is exactly the missing evidence.
5. **All artifact hashes and the replay command are present.** The unified
   artifact pattern carries `payload_sha256` and provenance; replay commands
   and dependency versions are recorded per run.

## What This Design Does Not Establish

- It does not implement the intervalized routes; it fixes their contract.
- It does not close certificate-chain link 1, and it changes no Gate status.
- It does not weaken the preregistered claim boundary: the current evidence
  for the Weil line remains a point-value-level cross-check, the intervalized
  artifacts are under construction, and Gate A is not closed.
