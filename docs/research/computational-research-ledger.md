# Computational Research Ledger

## Purpose

This ledger tracks research work that can run in parallel with Lean proof work.
It avoids the active `sorry` files and focuses on reproducible experiments,
finite certificates, and clear bridges back to formal statements.

## Workstreams

### PNT/RH Numerical Experiments

Location: `experiments/pnt/pnt_experiments.py`

Current scope:

- Compute `pi(x)`, Chebyshev `theta(x)`, Chebyshev `psi(x)`.
- Compute the offset logarithmic integral `integral from 2 to x of dt/log(t)`.
- Export rows with `psi(x) - x` and `pi(x) - Li(x)`.
- Generate an empirical Markdown report with extrema and sign-change counts.

Research use:

- Compare numerical behavior with the asymptotic goals in
  `PrimeNumberTheorem.lean`.
- Generate candidate inequalities or monotonicity observations before deciding
  whether they deserve a Lean statement.
- Keep claims empirical unless a Lean theorem or independent proof is added.

Local-machine fit:

- Good for sample ranges up to ordinary laptop scale.
- Not intended for high-precision zeta zero databases or record-scale prime
  computations.

### RH Li Coefficient Experiment

Location: `experiments/rh/li_coefficients.py`

Current scope:

- Use a small built-in fixture of early positive imaginary parts of zeta zeros.
- Pair each zero as `1/2 +/- i*t`.
- Compute finite truncated approximations to Li coefficients using
  `sum_rho (1 - (1 - 1/rho)^n)`.
- Generate an empirical Markdown report under `experiments/rh/output/`.

Research use:

- Give the Li criterion route a concrete computational target.
- Check report and data plumbing before introducing higher-precision or
  externally sourced zero lists.
- Keep all conclusions empirical until a formal proof route exists.

Local-machine fit:

- Good for small fixture and truncation-sensitivity experiments.
- Not a substitute for rigorous convergence control or a formal Li criterion
  proof.

### Finite Construction Search

Location: `experiments/discrete/ramsey_search.py`

Current scope:

- Search small graphs by brute force.
- Check clique and independent-set constraints.
- Use `R(3, 3)` as a sanity-check target: counterexample on 5 vertices, none on
  6 vertices.
- Export and verify JSON certificates for finite graph counterexamples.

Research use:

- Model the OpenAI/Erdos-style workflow at toy scale: generate finite object,
  verify it, then store the certificate.
- Later extensions can add unit-distance graphs, SAT encodings, or canonical
  graph reduction.

### Weil Extremal-Kernel Certificate Line

Locations: `experiments/rh/weil_extremal_crosscheck.py` (point-value dual
routes), `experiments/rh/weil_extremal_kernels.py` (exact rational `LDL^T`
checker), frozen records under `experiments/rh/reference/`.

Governing documents: `docs/research/weil-extremal-kernel-preregistration.md`,
`docs/research/weil-interval-assembly-design.md`,
`docs/research/weil-gate-a-local-reproduction-2026-07-19.md`.

Registered target:

- A rigorous positive-semidefinite certificate for the full cutoff-free
  matrix `Q_full(100, 250)`, preceded by the Gate A calibration at
  `Q_full(100, 200)` with the full `401 x 401` matrix.
- The certificate must traverse a six-link chain: intervalized dual-route
  assembly with entrywise overlap, symmetrization by intersection, exact
  rational reduction, exact rational `LDL^T` with nonnegative diagonal,
  analytic transfer with nonnegative margin, and independent replay.

Current scope:

- The two independent closed-form assembly routes (auxiliary `S/CC/XC` and
  CCM hypergeometric/Lerch) exist at mpmath point-value level; the frozen
  cross-check at `(c, N) = (13, 4)` and `(13, 8)` is content-addressed by
  SHA-256 `62da7e8d50bea317d3cee154a1fa758a0b0d31939016bc158d13eff9418bca2e`.
- Certificate-chain links 4 and 6 (exact rational `LDL^T`, artifact
  plumbing) and the generic mechanism for links 3 and 5 (rational interval
  reduction and perturbation transfer) are closed.
- Link 1 is in progress: the intervalized assembly contract
  `weil-extremal-kernel-interval-assembly/v1` is designed but not yet
  implemented. Gate A remains open; the current evidence is a
  point-value-level cross-check only.

Research use:

- Climb from the small-`N` containment tests (frozen point values must lie
  inside each route's `[lo, hi]` interval) to the `(100, 200)` Gate A
  calibration, including a 512-bit-separated rerun that verifies entrywise
  enclosure narrowing.

Local-machine fit:

- Small-`N` runs are laptop-scale. The `(100, 200)` assembly took about 16
  minutes per run for the upstream Arb route at 9000 bits on an Apple M4;
  dual-route interval assembly at that size is heavier and should be planned
  as a long local run.

## Boundaries

- These experiments do not modify Lean proof files.
- Generated observations are not mathematical proofs.
- Any candidate theorem should be promoted only after it has a clear statement,
  a proof strategy, and a verification path.

## Next Candidate Steps

1. Add optional plotting when `matplotlib` is available.
2. Add truncation-sensitivity reports for Li coefficients as the zero-pair
   cutoff changes.
3. Add externally loaded zero fixtures with provenance notes.
4. Map each useful observation to either a Lean theorem, a Mathlib blocker, or
   an experiment-only note.
