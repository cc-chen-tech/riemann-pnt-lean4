# Weil Streaming Interval LDL Design

## Scope

Consume the retained sharded symmetric intersection at `(c,N)=(100,200)`
without materializing a monolithic rational matrix. Run an unpivoted rigorous
interval `LDL^T` factorization in Arb. Emit a positive finite-matrix
certificate only when every pivot interval is strictly positive. A negative
claim additionally requires an exact rational vector whose interval quadratic
form has a strictly negative upper endpoint.

The finite-matrix result does not include the analytic tail or basis-change
transfer. Therefore `gate_a_status` remains `not_satisfied` even if the finite
matrix is certified positive.

## Architecture

The input reader authenticates the sharded cross-precision manifest and exposes
one symmetric high-precision tile at a time. A disk-backed lower-triangular
Schur store keeps only bounded blocks. At panel `k`, the factorizer loads the
current diagonal block, computes rigorous scalar interval pivots inside that
block, solves the panel with Arb matrix operations, and updates one trailing
Schur block at a time.

Every persisted Arb block is serialized to exact rational outward bounds with
enough decimal digits for the working precision. Checkpoints bind the input
manifest, algorithm source, block geometry, workspace block digests, precision,
and all certified pivot intervals.

## Outcomes

- `positive`: every interval pivot is strictly positive.
- `strict_negative_witness`: an exact rational vector has a strictly negative
  interval quadratic-form upper bound.
- `unresolved`: the first pivot interval contains zero, or interval division
  cannot proceed. This is not evidence of singularity or negativity.

The standard-library verifier authenticates checkpoint structure, source
bindings, canonical rational endpoints, pivot ordering and the claimed sign
logic. Reproducing Arb arithmetic requires rerunning the factorizer.

## High-Precision Path

If 896 bits is unresolved, regenerate both independent route matrices at 9000
and 9512 bits with an outward grid sized from the precision, intersect them
tile-by-tile, and feed the resulting sharded intersection to the same factorizer.
The earlier provenance records pin the registered parameters and same-route
positive inertia but do not replace the missing high-precision dual-route
entry data.
