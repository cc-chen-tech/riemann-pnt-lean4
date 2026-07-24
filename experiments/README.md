# Computational Experiments

This directory contains small, reproducible experiments that do not edit the
Lean proof files. They are meant to run on a local laptop and produce data or
finite certificates that can later be connected to formal Lean statements.

## PNT Experiments

Generate a CSV of Prime Number Theorem sample values:

```bash
python3 -m experiments.pnt.pnt_experiments --start 10 --stop 100000 --points 40
```

Generate a Markdown summary report:

```bash
python3 -m experiments.pnt.report --start 10 --stop 100000 --points 40
```

The output columns are:

- `x`
- `pi_x`
- `theta_x`
- `psi_x`
- `li_x`, using the offset integral `integral from 2 to x of dt/log(t)`
- `psi_error = psi_x - x`
- `pi_minus_li = pi_x - li_x`

This is intentionally dependency-light: the first version uses only the Python
standard library.

## RH Experiments

Generate a truncated Li coefficient report using a small built-in fixture of
early zeta-zero ordinates:

```bash
python3 -m experiments.rh.li_coefficients --n-max 10 --zero-pairs 10
```

The output is empirical numerical evidence only. It uses a finite zero list and
does not prove the Riemann Hypothesis.

### Weil finite-matrix certificates

Create an exact rational `LDL^T` artifact from a JSON object containing
`matrix` and optional `parameters` fields:

```bash
python3 -m experiments.rh.weil_extremal_kernels \
  certify matrix.json certificate.json
```

Replay the exact checker in a clean process:

```bash
python3 -m experiments.rh.weil_extremal_kernels verify certificate.json
```

Matrix entries must be integers or rational strings such as `"-7/12"`.
Artifacts are explicitly scoped to the stored finite rational matrix; they do
not certify that the matrix equals an analytic Weil-form matrix. The registered
analytic target and transfer gaps are fixed in
`docs/research/weil-extremal-kernel-preregistration.md`.

Generate the independent small-N outward-rounded Arb overlap artifact:

```bash
uv run --with python-flint==0.8.0 \
  python -m experiments.rh.weil_extremal_interval_overlap generate \
  experiments/rh/reference/groskin_2607_02828_v1_c13_N4_arb_interval_overlap.json \
  --c 13 --N 4 --prec-bits 384 --decimal-enclosure-digits 120
```

Replay its standard-library verifier:

```bash
python3 -m experiments.rh.weil_extremal_interval_overlap verify \
  experiments/rh/reference/groskin_2607_02828_v1_c13_N4_arb_interval_overlap.json
```

This artifact records two full `9 x 9` interval matrices and their entrywise
overlap at `(c,N)=(13,4)`. It is small-N Gate preparation, not the registered
full `(100,200)` Gate A certificate, and it makes no exact `LDL^T` claim.

## Discrete Search

Search for a small Ramsey counterexample graph:

```bash
python3 -m experiments.discrete.ramsey_search --vertices 5 --clique-size 3 --independent-size 3
```

Write a JSON certificate for that graph:

```bash
python3 -m experiments.discrete.ramsey_search \
  --vertices 5 \
  --clique-size 3 \
  --independent-size 3 \
  --certificate-output experiments/discrete/output/ramsey_r3_3_n5.json
```

For `R(3, 3)`, a counterexample exists on 5 vertices and none exists on 6
vertices. This gives a compact end-to-end model for AI-assisted construction:
generate a finite object, check the property, and preserve the certificate.
