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

## 9000/9512-bit path

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

The high-precision route has not been executed. The 896-bit result does not
certify positivity or negativity. Analytic tail control and basis-change
transfer also remain open, so `gate_a_status` remains `not_satisfied` and no
RH conclusion is made.
