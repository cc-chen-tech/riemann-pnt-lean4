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
