# Weil Gate A Local Reproduction, 2026-07-19

## Scope

This record replays the Arb interval `LDL^T` script released with
[Groskin's finite Guinand--Weil dictionary](https://arxiv.org/abs/2607.02828)
at the published calibration point `(c,N)=(100,200)`. It reproduces one
upstream assembly route. It is not an independent assembly and does not by
itself pass preregistered Gate A.

## Frozen inputs

- paper/source version: arXiv:2607.02828v1;
- released script: `anc/arb_ldlt_certify.py`;
- script SHA-256:
  `02462e7f75a601ed8a5cc4d5c22064ece8088140ff45b9a21fd0295162c72039`;
- Python: 3.12.13;
- `mpmath`: 1.3.0;
- `python-flint`: 0.8.0;
- machine: Apple M4, 10 cores, 16 GB RAM, macOS 15.6.1.

The small `(c,N,prec)=(13,8,300)` calibration also completed with full
dimension `17`, `n_pos=17`, `n_neg=0`, and certified positive definiteness.
Its JSON SHA-256 was
`7fd9af800b7bcfa5b09523cbd36e08979129753bc61830e667b19dbb7f5afc82`.
The script's `--selftest` independently recomputed representative entries
with `mpmath` and returned successfully.

## Replay

```sh
PYTHONDONTWRITEBYTECODE=1 \
  /tmp/weil-gate-a-venv-20260719c/bin/python \
  /tmp/arxiv-2607.02828.S3PwAS/anc/arb_ldlt_certify.py \
  --selftest --c 100 --N 200 --prec 9000 \
  --json-out /tmp/weil-c100-N200-prec9000-local.json
```

Observed result:

```text
cutoff-free block built, dimension 401 (964.7s)
RESULT: n_pos=401 n_neg=0 (80.5s)
CERTIFIED positive-definite: all 401 Arb interval pivots strictly signed
```

The local result is preserved as
`experiments/rh/reference/groskin_2607_02828_v1_c100_N200_local_20260719.json`.
The raw generated JSON had SHA-256
`702c55fbef78d81f94c2cdf816ed8ea38d584ecbfe4fa8355f9a3710e2ad4c5e`;
the repository copy adds a terminal newline and has SHA-256
`e6813465db1fef0087e6220a1e76c55d4fdd877db33d27ac51d0ece396033956`.

The repository verifier accepts it with:

```sh
python3 -m experiments.rh.weil_extremal_kernels \
  verify-groskin-provenance \
  experiments/rh/reference/groskin_2607_02828_v1_c100_N200_local_20260719.json \
  --c 100 --N 200
```

The local and published records agree on `script`, `c`, `N`, `dimension`,
`prec_bits`, `n_pos`, `n_neg`, `undetermined_pivot`, and
`certified_positive_definite`. Timings and timestamps are machine-dependent.

## Gate status

This closes only a same-route local replay of the published `N=200`
calibration. Gate A remains open because it additionally requires:

- a second, independent matrix assembly with entrywise-overlapping intervals;
- an exact rational certificate replay, rather than only the upstream Arb
  factorization;
- a second precision at least 512 bits away with narrower entry enclosures;
- the registered analytic transfer-margin check.

No `N=250` computation, strict improvement, new positivity theorem, or result
about the Riemann Hypothesis is claimed.
