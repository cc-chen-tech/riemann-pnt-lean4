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
