# Li Criterion Research Note

## Purpose

This note isolates the Li criterion as the recommended first RH-equivalent
target. It is not a proof plan yet. It defines the mathematical target,
connects it to local files, and lists the dependencies needed before Lean
implementation.

## Mathematical Statement

The Li criterion says that the Riemann Hypothesis is equivalent to positivity
of a sequence of real coefficients:

```text
lambda_n > 0 for every n >= 1.
```

One zero-sum expression is

```text
lambda_n = sum_rho (1 - (1 - 1/rho)^n),
```

where `rho` ranges over the nontrivial zeros of the Riemann zeta function, with
the standard symmetric limiting interpretation.

Another expression uses the xi function:

```text
lambda_n =
  (1 / (n - 1)!) * d^n/ds^n [s^(n - 1) * log xi(s)] at s = 1.
```

The xi-function version is more suitable as the first formal target because it
does not start by summing over zeros.

## Why This Route Fits This Repository

The local repository already has:

- `RiemannExplorer.lean`
  - `RiemannHypothesis.Statement`
  - `IsNontrivialZero`
  - `criticalLine`
  - a local `completedZeta` definition needing audit
- `PrimeNumberTheorem.lean`
  - `rh_statement_iff_mathlib`
  - `RH_ErrorBound`
  - `explicit_formula_von_mangoldt`
- `HardyTheorem.lean`
  - completed-zeta conjugation and critical-line real-valued facts
- `docs/research/xi-definition-audit.md`
  - recommended boundary for a future xi API
- `experiments/pnt/pnt_experiments.py`
  - existing computational pipeline that can be extended

Li's criterion gives this project a finite sequence of milestones before any
claim about the full RH theorem.

## Candidate Local Definitions

The eventual Lean API should avoid committing to computational details too
early. A staged design is safer.

### Stage 1: Predicate-only statement

```lean
def LiCriterionHolds : Prop :=
  ∀ n : ℕ, 1 ≤ n -> 0 < liCoefficient n
```

This requires `liCoefficient : ℕ -> ℝ` or `ℕ -> ℂ` plus a proof that the
coefficient is real. Do not add this until `xiFunction` is canonical.

### Stage 2: Xi-derivative definition

Candidate mathematical shape:

```lean
noncomputable def liCoefficient (n : ℕ) : ℂ :=
  (1 / Nat.factorial (n - 1)) *
    iteratedDeriv n (fun s : ℂ =>
      s ^ (n - 1) * Complex.log (xiFunction s)) 1
```

Risks:

- `Complex.log` branch control is nontrivial.
- Iterated derivatives of logarithms require nonvanishing neighborhoods.
- This may need a local analytic-log abstraction rather than raw
  `Complex.log`.

### Stage 3: Generating-function route

An alternative avoids direct log derivatives at first:

```text
log xi(1 / (1 - z)) = constant + sum_{n >= 1} (lambda_n / n) z^n.
```

This may be better for experiments and formal power series, but it still needs
xi nonvanishing and analytic control around the expansion point.

## Dependencies

### Local dependencies

- Canonical `xiFunction`.
- Functional equation for `xiFunction`.
- Agreement of `xiFunction` with the classical completed-zeta expression.
- Zero correspondence between `xiFunction` and nontrivial zeta zeros.
- A statement that the relevant Li coefficients are real.

### Mathlib-level dependencies

- Iterated derivatives over complex functions.
- Analytic logarithm or controlled branch of `Complex.log`.
- Formal power series coefficient extraction for analytic functions.
- Entire-function product or zero-sum machinery for the equivalence proof.
- Convergence control for sums over nontrivial zeros.

### Research-level dependencies

- Full equivalence proof between positivity of all Li coefficients and RH.
- Translation between xi-derivative and zero-sum definitions.

## Computational Experiments

The first experiment should not attempt high-precision proof. It should produce
auditable numerical evidence and stable data formats.

Proposed module:

```text
experiments/rh/li_coefficients.py
```

First version:

- Input: a finite list of known zeta zeros, either embedded as a small fixture
  or loaded from CSV.
- Output: approximate `lambda_n` values for small `n`.
- Report: sign, magnitude, and sensitivity to truncation.
- Caveat: results are empirical and do not imply RH.

Test targets:

- Parsing zero fixtures.
- Symmetric-pair contribution is real up to tolerance.
- Early coefficients are positive for the fixture.
- Increasing the zero cutoff changes values in a visible but bounded way.

## Acceptance Criteria For A First Implementation

A useful first implementation should:

- add no new Lean `sorry`;
- not modify existing Lean proof files;
- add tests for the experiment module;
- generate a Markdown report under `experiments/rh/output/`;
- label all numerical conclusions as empirical.

## How This Could Become Lean Work

After the xi audit and experiment module exist, Lean work can start with
statement-only declarations in a future isolated file:

```text
LiCriterion.lean
```

Suggested first theorem statements:

```lean
def LiCriterionHolds : Prop := ...

theorem li_criterion_implies_rh :
    LiCriterionHolds -> RiemannHypothesis.Statement := by
  ...

theorem rh_implies_li_criterion :
    RiemannHypothesis.Statement -> LiCriterionHolds := by
  ...
```

These should not be implemented with `sorry` in the main branch. If used for
planning, they should live in a clearly marked scratch file or design document
until the required infrastructure is present.

## Recommendation

Do the next step in this order:

1. Add a tiny `experiments/rh/li_coefficients.py` prototype with tests.
2. Generate an empirical Markdown report for early coefficients.
3. Write a `XiFunction.lean` implementation plan only after active `sorry`
   cleanup settles.
4. Postpone Lean implementation of Li criterion until `xiFunction` has a
   stable API.

