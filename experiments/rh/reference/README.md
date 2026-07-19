# Groskin finite-dictionary calibration record

`groskin_2607_02828_v1_c100_N200_provenance.json` is the provenance metadata
released with Akiva Groskin, *A finite Guinand--Weil dictionary and
archimedean tail order for the truncated Weil quadratic form*,
arXiv:2607.02828v1.

Source bundle: <https://arxiv.org/src/2607.02828v1>, file
`anc/c100_N200_arb_ldlt_prec9000_provenance.json`.

The upstream file has no terminal newline and SHA-256
`ccb6327eb2f5fc2d81fae923b2db272d4371b7bcbd0ef995562fb99e04538e98`.
The repository copy adds one terminal newline and has SHA-256
`5d14ea5bc0874c4edf15b586075337c1852b8e592bd7c4a7867ea14a995325a7`.

The verifier in `experiments.rh.weil_extremal_kernels` checks only dimensional
and inertia metadata. It does not replay the matrix assembly, Arb interval
arithmetic, or the released `LDL^T` certificate.

The two local normalized replay records freeze certified positive inertia at
`9000` and `9512` bits. Their SHA-256 values are respectively
`e6813465db1fef0087e6220a1e76c55d4fdd877db33d27ac51d0ece396033956`
and
`6130a52197e9cde363f3e722124608e784fd31e81f97146444f79595edfcb178`.
The second run is exactly 512 bits above the first, but these metadata-only
records cannot establish entrywise enclosure narrowing.

## Small-N Independent Numerical Cross-Check

`groskin_2607_02828_v1_small_n_high_precision_crosscheck.json` is a canonical
JSON record of every ordered full-matrix entry at `(c,N)=(13,4)` and `(13,8)`.
It compares two fresh mpmath implementations: the auxiliary `S/CC/XC` closed
form and the distinct CCM hypergeometric/Lerch closed form. It does not import
or call `arb_ldlt_certify.py`; the released script SHA-256 recorded in the
artifact is `02462e7f75a601ed8a5cc4d5c22064ece8088140ff45b9a21fd0295162c72039`.

The artifact was generated in two bounded runs at 80 and 120 decimal digits.
After each assembly returns, cross-route and cross-precision subtraction,
maximum selection, tolerance construction and comparison, and diagnostic
decimal formatting run at 140 decimal digits, including 20 guard digits.
Arithmetic internal to each formula assembly remains at that route's declared
80 or 120 decimal digits. Each entry additionally stores clearly named low-
and high-precision values for both routes at 130 audit digits (`high_dps+10`).
All low/high pairs in these cases coincide at 70 significant digits, so the
extra audit digits are required to recompute and authenticate the 70-digit
cross-precision diagnostics. The verifier includes the half-ulp serialization
budget of both audit values and the diagnostic:

```sh
python -m experiments.rh.weil_extremal_crosscheck \
  --case 13:4 --low-dps 80 --high-dps 120 \
  --output experiments/rh/reference/groskin_2607_02828_v1_small_n_high_precision_crosscheck.json
python -m experiments.rh.weil_extremal_crosscheck --append \
  --case 13:8 --low-dps 80 --high-dps 120 \
  --output experiments/rh/reference/groskin_2607_02828_v1_small_n_high_precision_crosscheck.json
```

The real-assembly regression is optional in a default development environment
and skips when mpmath is unavailable. A strong research-validation run must use
the frozen mpmath 1.3.0 dependency and must report no skipped test:

```sh
python -m pip install 'mpmath==1.3.0'
python -c 'import mpmath; assert mpmath.__version__ == "1.3.0"'
python -m pytest -q tests/test_weil_extremal_kernels.py
```

Its SHA-256 is
`62da7e8d50bea317d3cee154a1fa758a0b0d31939016bc158d13eff9418bca2e`.
The record is a numerical point-value cross-check only: it does not provide
outward-rounded enclosures, their entrywise overlap, an exact rational LDL
certificate, an analytic transfer margin, or the registered `(100,200)` Gate
A computation.
