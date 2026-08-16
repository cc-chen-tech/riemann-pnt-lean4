# Weil Finite-to-Infinite Schur Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a kernel-checked bridge and exact diagnostic that state whether certified finite Weil data plus supplied analytic bounds close a sufficient finite-to-infinite positivity criterion.

**Architecture:** A generic Lean module proves normalized-tail and Schur sufficient conditions without claiming the analytic hypotheses. A standalone Python consumer validates existing overlap artifacts, validates an optional hash-bound analytic artifact, and decides the inequalities in exact rational arithmetic. A Chinese research note explains the result and the still-missing Weil estimates.

**Tech Stack:** Lean 4, Mathlib, Python 3 standard library, pytest.

## Global Constraints

- Do not infer RH or the infinite-dimensional Weil criterion from finite artifacts alone.
- Do not use floating point in any closure decision.
- Reuse the existing overlap artifact validator and canonical SHA-256 rule.
- Reject missing, malformed, mismatched, or normalization-incompatible analytic data.
- Do not run tests or builds unless the user separately requests validation.

---

### Task 1: Generic Lean bridge

**Files:**
- Create: `WeilExtremalKernels/FiniteToInfiniteSchur.lean`

**Interfaces:**
- Consumes: `WeilExtremalKernels.FiniteQuadraticForm`.
- Produces: `nonneg_of_normalized_truncation_bound`, `two_mul_coupling_le_of_sq_le`, `schur_nonneg_of_bounds`, and strict counterparts.

- [ ] **Step 1: Define the normalized truncation theorem**

Add a generic pointwise theorem taking `q`, `qN`, `sizeSq`, `epsilon`, and `delta`, with lower-bound, error-bound, nonnegative-size, and budget hypotheses.

- [ ] **Step 2: Prove the scalar Schur coupling inequality**

Use exact real algebra and

```lean
sq_nonneg (epsilon * lowSize - beta * highSize)
```

together with `beta ^ 2 <= epsilon * gamma`.

- [ ] **Step 3: Prove the generic Schur form theorem**

Instantiate the scalar inequality with the low/high size functions and combine it with the low block, high block, and absolute coupling bounds.

- [ ] **Step 4: Add strict variants**

Expose positive conclusions when normalized-tail slack is strict or the caller supplies strict block margin.

### Task 2: Exact feasibility diagnostic

**Files:**
- Create: `experiments/rh/weil_schur_feasibility.py`

**Interfaces:**
- Consumes: validated overlap JSON and optional `weil-finite-to-infinite-schur-bounds/v1` JSON.
- Produces: `diagnose(overlap, analytic_bounds=None) -> dict` and CLI JSON.

- [ ] **Step 1: Define schema constants and exact parsers**

Use `Fraction`; reject booleans, floats, malformed rationals, and unexpected keys.

- [ ] **Step 2: Validate analytic artifact identity and hash**

Require source hash, parameters, index convention, normalization, claim scope, provenance, and canonical payload digest to match.

- [ ] **Step 3: Derive the finite margin**

Compute exactly:

```python
epsilon = Fraction(center_lower_bound) - Fraction(perturbation_row_bound)
```

- [ ] **Step 4: Implement route decisions**

Normalized route uses `delta <= epsilon`. Schur route uses
`beta * beta <= epsilon * gamma`. Missing fields remain missing.

- [ ] **Step 5: Implement CLI**

Accept `--overlap` and optional `--analytic-bounds`; print deterministic JSON; return `2` on invalid input and `0` for every valid verdict.

### Task 3: Research-facing explanation

**Files:**
- Create: `docs/research/weil-finite-to-infinite-schur.md`

**Interfaces:**
- Consumes: theorem names and diagnostic fields from Tasks 1-2.
- Produces: a Chinese explanation of the four bounds and current status.

- [ ] **Step 1: Explain the low/high decomposition**

Use plain language and one diagram.

- [ ] **Step 2: Record the current conclusion**

State that N=16/32 certify only `epsilon`; actual `delta` or `gamma,beta` remain analytic obligations.

- [ ] **Step 3: Define the next mathematical experiment**

Specify the positive reference form, normalized coefficient-tail estimate, and ratio to measure.

### Task 4: Focused integration coverage

**Files:**
- Modify: `tests/test_weil_interval_integration.py`

**Interfaces:**
- Consumes: `experiments.rh.weil_schur_feasibility`.
- Produces: regression coverage for exact decisions and tamper rejection.

- [ ] **Step 1: Add imports and helpers**

Add the diagnostic import and a helper that creates hash-valid analytic fixtures.

- [ ] **Step 2: Cover current artifacts**

Assert N=16/32 return `MISSING_ANALYTIC_BOUNDS`.

- [ ] **Step 3: Cover both sufficient routes**

Use exact rational boundary fixtures to assert `CLOSES`.

- [ ] **Step 4: Cover failed bounds and tampering**

Assert `BOUND_FAILS` for complete insufficient bounds and rejection for source hash, normalization, and payload tampering.

- [ ] **Step 5: Leave validation pending**

Do not execute pytest or Lean builds without explicit user permission.
