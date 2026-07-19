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
