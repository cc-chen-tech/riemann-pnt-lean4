# Riemann Hypothesis Proof Roadmap

## Status

This document is a research roadmap, not a proof of the Riemann Hypothesis.
The goal is to turn the RH work into a sequence of checkable subprojects:
formal statements, numerical experiments, Mathlib infrastructure gaps, and
candidate proof routes that can be tested without disturbing active Lean proof
work elsewhere in the repository.

## Local Project Anchors

The current repository already contains useful RH-adjacent material:

- `RiemannExplorer.lean`
  - Defines `RiemannHypothesis.Statement`.
  - Defines nontrivial zeros and the critical line.
  - Contains a completed-zeta based `completedZeta` expression and notes about
    Hadamard-style approaches.
- `PrimeNumberTheorem.lean`
  - Defines `logIntegral`, `chebyshevPsi`, and PNT equivalent forms.
  - Contains `RH_ErrorBound` and the statement
    `rh_iff_optimal_error`.
  - Contains nontrivial-zero symmetry and critical-strip lemmas.
  - Proves a multiplicity-aware explicit von Mangoldt formula, ordinary PNT,
    the classical PNT remainder, and both directions of the RH/error
    equivalence. The equivalence does not prove RH or either equivalent error
    proposition unconditionally.
- `HardyTheorem.lean`
  - Proves Hardy's theorem in the stronger unbounded-positive-height form.
  - This gives infinitely many critical-line zeros, but is not enough for RH
    and does not exclude zeros away from the critical line.
- `ZeroFreeRegion.lean`
  - Proves the classical `c/log |t|` zero-free region using the local
    Borel/Jensen and zeta-growth infrastructure.
  - The stronger Vinogradov-Korobov target still requires exponential-sum
    estimates.
- `experiments/pnt/pnt_experiments.py`
  - Provides local numerical data for `pi(x)`, `theta(x)`, `psi(x)`, and
    `Li(x)`.

## Main Principle

Do not try to write "the proof of RH" directly. Instead, promote one statement
at a time through this pipeline:

1. Natural-language mathematical statement.
2. Numerical experiment or literature reference, when applicable.
3. Precise Lean statement.
4. Classification as local proof, Mathlib infrastructure, or research blocker.
5. Proof attempt only after dependencies are explicit.

## Candidate Routes

### Route A: Li Criterion

Statement:

RH is equivalent to positivity of the Li coefficients

```text
lambda_n > 0 for every n >= 1.
```

One common form is

```text
lambda_n = sum_rho (1 - (1 - 1/rho)^n),
```

where the sum is over nontrivial zeros of zeta, interpreted with the standard
regularization. Another form uses derivatives of `log xi(s)` at `s = 1`.

Why this route is attractive:

- It turns RH into an infinite family of real inequalities.
- It connects naturally to computation.
- It provides many smaller formalization targets before the full theorem.

Required infrastructure:

- A clean Lean definition of the completed xi function.
- Proof that xi is entire.
- Product or logarithmic derivative formula for xi.
- A formal definition of Li coefficients.
- Equivalence theorem between positivity of all Li coefficients and RH.

Near-term tasks:

- Define a Python experiment for the first Li coefficients using a trusted
  numerical source or a controlled zero list.
- Draft Lean statements for `xiFunction`, `liCoefficient`, and
  `li_criterion_statement`.
- Do not attempt the full equivalence until xi and product infrastructure are
  available.

Risk:

Medium-high. The route is modular, but it still needs serious complex-analysis
infrastructure.

### Route B: Weil Criterion and Explicit Formula

Statement:

RH can be expressed as positivity of a quadratic form or distributional
condition in Weil's explicit formula.

Why this route is attractive:

- It connects RH to explicit formula work already present in
  `PrimeNumberTheorem.lean`.
- It gives test-function based finite approximations that are good for
  computational experiments.
- It is conceptually closer to the prime-number side of this repository.

Required infrastructure:

- The existing rigorous von Mangoldt explicit formula as a starting point.
- Test functions and Fourier/Mellin transform machinery.
- Summation over zeros with convergence control.
- Positivity theorem equivalent to RH.

Near-term tasks:

- Reuse `explicit_formula_von_mangoldt_proved` rather than reintroducing it as
  a target.
- Add an experiment that compares `psi(x) - x` with truncated zero terms.
- Build a dependency map from explicit formula to Perron, residues, and contour
  integrals.

Risk:

High. The local contour and residue route is now sufficient for the PNT
formula, but the Weil positivity equivalence requires substantially different
test-function and distributional infrastructure.

### Route C: Xi Function and Hadamard Product

Statement:

Study the completed xi function as an entire function whose zeros are exactly
the nontrivial zeta zeros, then use product representations and symmetry.

Why this route is attractive:

- It is close to the classical analytic formulation of RH.
- It provides reusable infrastructure for Li and Weil routes.
- The local project already has completed-zeta and zero-symmetry material.

Required infrastructure:

- Correct, canonical definition of `xi(s)`.
- Entirety of xi.
- Functional equation `xi(s) = xi(1 - s)`.
- Zero correspondence between xi and nontrivial zeta zeros.
- Hadamard factorization for entire functions of finite order.

Near-term tasks:

- Audit `RiemannExplorer.lean` against the standard xi definition.
- Create a file plan for a future `XiFunction.lean`, but do not edit proof
  files while another worker is resolving `sorry`s.
- Identify which xi facts already exist in Mathlib and which must be built.

Risk:

High. This is foundational and valuable, but Hadamard factorization is a major
Mathlib-level dependency.

### Route D: Hilbert-Polya and Operator Routes

Statement:

Find a self-adjoint operator whose spectrum corresponds to the imaginary parts
of nontrivial zeta zeros.

Why this route is interesting:

- It is one of the most famous conceptual approaches to RH.
- It connects to spectral theory and mathematical physics.

Why it is not the recommended first route:

- No accepted operator is known.
- It is difficult to convert into near-term Lean milestones.
- It is easy to generate speculative text without verifiable progress.

Near-term tasks:

- Keep this route as background research only.
- Do not build local implementation tasks around it until a concrete theorem or
  operator model is selected.

Risk:

Very high.

## Recommended Path

The strongest near-term path is a combined A plus C strategy:

1. Use Route C to establish clean xi-function definitions and dependency maps.
2. Use Route A to turn RH into Li coefficient positivity targets.
3. Use experiments to compute and inspect early Li coefficients.
4. Promote only stable, dependency-light facts into Lean statements.

Route B should run in parallel as a long-term prime-number-side path, because
it connects to the existing explicit formula target. Route D should remain
background reading unless it produces a concrete formal target.

## Immediate Work Items

### Work Item 1: Xi Definition Audit

Output:

- A short note comparing the local `completedZeta`/completed-zeta expressions
  against the standard xi definition

```text
xi(s) = 1/2 * s * (s - 1) * pi^(-s/2) * Gamma(s/2) * zeta(s).
```

Acceptance criteria:

- The note identifies the local names that already express parts of xi.
- The note identifies whether a new `XiFunction.lean` file is warranted.
- No Lean proof files are edited.

### Work Item 2: Li Criterion Research Note

Output:

- A document section defining the Li criterion in the notation of this project.
- A dependency list for formalizing the criterion in Lean.
- A list of experiment inputs needed to compute early coefficients.

Acceptance criteria:

- The note separates theorem statements from numerical heuristics.
- The note names all local files it would depend on.

### Work Item 3: RH Experiment Extension Plan

Output:

- A plan for extending `experiments/pnt/pnt_experiments.py` or adding
  `experiments/rh/`.

Possible first experiments:

- Compute low-order Li coefficients from a finite zero list.
- Compare `psi(x) - x` with a truncated explicit-formula zero contribution.
- Generate a Markdown report from the existing PNT CSV.

Acceptance criteria:

- Experiments remain dependency-light by default.
- Optional high-precision dependencies are isolated behind clear CLI flags.
- Results are labeled empirical.

### Work Item 4: Blocker Table

Output:

- A table mapping each serious RH route to its missing infrastructure.

Initial blockers:

- Entire functions of finite order.
- Hadamard factorization.
- Perron formula.
- Argument principle and residue theorem in the required form.
- Borel-Caratheodory and zeta growth estimates.
- Convergence of sums over nontrivial zeros.

Acceptance criteria:

- Each blocker is classified as local, Mathlib-level, literature-level, or
  speculative.

## What Not To Do

- Do not claim that numerical verification proves RH.
- Do not treat a model-generated natural-language proof as evidence unless it
  survives expert or formal checking.
- Do not mix this roadmap with the active `sorry` cleanup branch.
- Do not add a speculative proof file full of placeholders.
- Do not pursue Hilbert-Polya implementation work without a concrete operator
  theorem.

## Next Decision

The next productive decision is whether to start with:

1. `Xi Definition Audit`, best for formal foundations.
2. `Li Criterion Research Note`, best for a focused RH-equivalent target.
3. `RH Experiment Extension Plan`, best for immediate computational feedback.

Recommended next step: start with `Xi Definition Audit`, then immediately write
the `Li Criterion Research Note`.
