# Weil Streaming Interval LDL, 2026-07-25

## Result at 896 bits

The input is the committed two-route, two-precision sharded intersection at
`(c,N)=(100,200)`. The factorizer authenticated all source shards, selected
the symmetric 896-bit intersection, and ran a 64-by-64 disk-backed interval
`LDL^T` factorization with Arb at 896 bits. Mutable Schur and factor blocks were
serialized on a 300-digit outward rational grid.

The result is rigorously **unresolved**:

- pivots 0 through 66 have strictly positive lower endpoints;
- pivot 67 has an interval containing zero;
- no strict negative rational witness was found or claimed;
- no positive finite-matrix certificate was emitted.

The last positive pivot interval is approximately

```text
[1.607947325362e-5, 3.057505286317e-5].
```

The first unresolved pivot interval is approximately

```text
[-4.044282153109e-3, 3.041817943369e-3].
```

The checkpoint stores the exact rational endpoints. Its file SHA-256 is
`1af647074af73dd617cdb3d027e5400efd01b67727982d46acca2f88a1f7ceae`.
Its canonical payload hash is
`5c547dc172fc08250bb345bfad40e9b89b6df7138207b217248af9b3029e5f52`.

## Bounded storage

No individual loaded block exceeded 64 by 64, or 4096 interval entries.
Each update retains only a fixed number of such blocks rather than a full
401-by-401 matrix. The final workspace contained 31 compressed block files
totaling `28058564` bytes. The workspace is a reproducibility cache in `/tmp`,
not a committed mathematical artifact; its manifest SHA-256 is
`4e84f19a469d8c000e860d337bcbcdedeffdefa99dbdb3e1243e1f6c5c8e5e2e`.

The first two runs took `95.31s` and `92.88s`; the second reproduced the
complete pivot sequence, unresolved interval, workspace summary, and every
workspace file byte-for-byte. Final regeneration after adding explicit
low/high layer selection took `143.31s` with the same mathematical transcript.
The final standard-library checkpoint replay took `166.98s`, dominated by
reauthentication of the 121 MB source artifact. These wall-clock timings vary
with filesystem cache state.

```sh
/tmp/weil-overlap-venv-20260724/bin/python \
  -m experiments.rh.weil_extremal_streaming_ldlt run \
  experiments/rh/reference/groskin_2607_02828_v1_c100_N200_arb_cross_precision_sharded/manifest.json \
  experiments/rh/reference/groskin_2607_02828_v1_c100_N200_streaming_ldlt_896_checkpoint.json \
  --workspace-dir /tmp/weil-streaming-ldlt-c100-N200-896 \
  --block-size 64 --arb-prec-bits 896 --serialization-digits 300

python3 -S -m experiments.rh.weil_extremal_streaming_ldlt \
  verify-checkpoint \
  experiments/rh/reference/groskin_2607_02828_v1_c100_N200_streaming_ldlt_896_checkpoint.json
```

The standard-library verifier authenticates exact endpoint syntax, source
bindings, pivot sign logic and transcript metadata. It does not independently
replay Arb arithmetic; that requires rerunning the factorizer.

## Registered c=100 high-precision path

The existing high source is serialized on a 120-digit grid. Raising only the
factorization context to 9000 bits cannot recover information discarded by
that input grid. A meaningful high-precision attempt must regenerate both
independent routes at 9000 and 9512 bits on the same 2900-digit outward grid.

To avoid a monolithic matrix, route generation must be refactored into:

1. precomputation of the one-dimensional auxiliary and CCM sequences;
2. evaluation and immediate serialization of one 64-by-64 tile;
3. tile-local dual-route and transpose intersection;
4. streaming interval LDL on the 9000-bit low intersection and the 9512-bit
   high intersection with 2950-digit Schur serialization.

The exact execution contract and provenance digests are recorded in
`groskin_2607_02828_v1_c100_N200_streaming_ldlt_high_precision_plan.json`.
The 9000/9512 provenance records confirm same-route positive inertia at the
registered point. They do not provide the missing high-precision dual-route
entry intervals and cannot be substituted for them.

The registered `(c,N)=(100,200)` high-precision route has not been executed.
The 896-bit result does not certify positivity or negativity.

## c=13, N=200 candidate execution

A separate candidate run at `(c,N)=(13,200)` completed all four 64-by-64
sharded routes:

- the low auxiliary and CCM routes used 9000-bit Arb intervals;
- the high auxiliary and CCM routes used 9512-bit Arb intervals;
- all routes used a 2900-digit outward grid;
- each route completed 49 tiles and 160801 entries;
- each route passed its independent route verifier.

The transpose-aware cross artifact also completed all 49 tiles and passed
`verify-cross`. Its checkpoint and manifest SHA-256 is
`efec67a8e7a0eca6c028164c12e87ae6cb94312d0b855adceb58ea439f504b04`.
All low and high route intersections overlap, all retained intersections are
contained and strictly narrower, and all symmetric intersections are
nonempty.

The first real high-precision LDL run exposed a verifier coverage bug: the
runner accepted both the legacy sharded cross schema and the resumable
high-precision cross schema, while the checkpoint verifier accepted only the
legacy schema. Commit `9a8cf5f` makes both paths share the same dual-schema
source-validation helper and adds a high-precision-source regression. All 106
Weil Python tests pass. The final LDL checkpoints below were regenerated after
that repair, so their generator SHA binds the committed verifier source.

Both retained intersection levels have a complete positive factorization:

| level | Arb bits | positive pivots | checkpoint SHA-256 |
| --- | ---: | ---: | --- |
| high | 9512 | 401/401 | `be071bd29e22a8d6c6ee947bc4585394a63f030519f920241c790a4e6fcce41b` |
| low | 9000 | 401/401 | `7044877c6f4c1663e91d2b5ae5732784fcbd419dffe466d184f8a8098edb2110` |

Both checkpoints passed independent `verify-checkpoint` runs. The smallest
pivot lower bound occurs at index 203 and is approximately
`3.007626851110137615766217289610976834519e-20`. Its interval width is
approximately `1.13e-2694` on the high intersection and `1.07e-2543` on the
low intersection.

This is a rigorous positive certificate for one finite 401-by-401 candidate
matrix. It is not the preregistered `(c,N)=(100,200)` Gate A baseline.
Analytic tail control and basis-change transfer remain open, so
`gate_a_status` remains `not_satisfied` and no RH conclusion is made.

## Lean finite-to-tail transfer and scalar integral

The generic finite-dimensional transfer step is now verified in
`WeilExtremalKernels/ArchimedeanTailTransfer.lean`. It proves:

- finite positive semidefiniteness or definiteness survives addition of a
  nonnegative tail;
- a finite negative witness below `-B * squaredNorm x` survives any tail
  bounded above by `B * squaredNorm x`;
- interval-matrix and separate transfer-error budgets combine with an
  explicit total margin.

The scalar improper integral used in the paper's explicit tail budget is
verified in `WeilExtremalKernels/ArchimedeanTailBudget.lean`:

```text
integral over (T,+infinity) of log r / (r-b)^2
  = log T / (T-b) + b^(-1) log (T / (T-b))
```

under `0 < b < T` and `1 <= T`. The proof includes the derivative identity
and the antiderivative limit at positive infinity.

The unintegrated rank-two density is now verified in
`WeilExtremalKernels/ArchimedeanRankTwoTail.lean`.  For the paper's centered
coordinates `-N, ..., N`, it constructs the two Cauchy vectors

```text
p_T(n) = (T / rho - n)^(-1)
q_T(n) = (T / rho + n)^(-1)
```

and proves the exact pointwise norm budget

```text
sum p_T(n)^2 + sum q_T(n)^2
  <= 2 * (2*N+1) * (rho / (T-rho*N))^2.
```

Consequently, any nonnegative scalar weight times the associated rank-two
Gram matrix is positive semidefinite and has its quadratic form bounded by
the same explicit scalar times `squaredNorm x`.

`WeilExtremalKernels/ArchimedeanRankTwoIntegral.lean` now adds the finite
matrix-valued integration layer:

- entrywise interval integration commutes with every finite quadratic form;
- a continuous nonnegative weighted rank-two density integrates to a positive
  semidefinite matrix increment;
- the integrated quadratic form is bounded by the integral of the explicit
  pointwise Cauchy-vector budget.

`WeilExtremalKernels/ArchimedeanHPlus.lean` now inserts the paper's actual
archimedean density

```text
h_+(t) = Re digamma(1/4 + i*t/2) - log pi
```

and the scalar weight

```text
pi^(-2) h_+(r) sin^2(Lr/2) / rho.
```

It proves analyticity of `digamma` in the right half-plane, continuity of
`h_+` and of the actual weight, and transfers pointwise nonnegativity and the
logarithmic envelope to that weight once the corresponding facts about
`h_+` are supplied. Using the existing second-order Stirling remainder, it
also proves

```text
h_+(t) - log(t / (2*pi)) -> 0
```

and therefore a non-explicit threshold `T_0` beyond which
`0 <= h_+(t) <= log t`.

These results remove the generic algebraic transfer, scalar-calculus,
rank-two positivity, pointwise vector-norm, and finite-interval matrix
integration subgoals, and they now identify and eventually bound the actual
analytic weight in Lean. They do not yet prove the explicit hard estimates

```text
0 <= h_+(t) <= log t  for t >= 7,
```

construct the improper matrix tail, integrate to the final constant `B_T`,
verify the basis transfer, or connect a finite certificate to the
infinite-dimensional Weil criterion. Gate A therefore remains open.
