# Centered Fourth-Trace Audit Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Turn the Blomer–Pascadi centered fourth-cycle idea into exact finite audit code, determine its published exponent coverage, and state the precise remaining bridge to the Möbius coupled-kernel gate without promoting a conditional route to a theorem.

**Architecture:** Add one focused Python checker for the integral `SL₂` trace word, its discriminant, Jacobi character, exceptional strata, and finite multiplicity energy. Extend the existing Type-II exponent ledger with exact rational margins for the published Blomer–Pascadi bound. Record both positive coverage and counterexamples in the research specification, preserving the original `a = hδ` coupling and both Möbius weights as non-negotiable inputs to the still-missing bridge.

**Tech Stack:** Python standard library (`dataclasses`, `fractions`, `itertools`, `math`), pytest, Markdown.

**Spec:** `docs/research/2026-08-24-mobius-weighted-off-diagonal.md`

## Global Constraints

- Do not promote a route or gate to a theorem.
- Preserve exact centered/common-mode cancellations and both Möbius weights.
- Verify finite identities and rational exponent applicability; finite computation is evidence, not an asymptotic proof.
- Keep the Blomer–Pascadi representation-character trace distinct from a raw count of inverse-cycle solutions.

---

### Task 1: Lock the published exponent range with failing tests

**Files:**

- Modify: `tests/test_mobius_type_ii_audit.py`
- Modify: `scripts/audit_mobius_type_ii.py`

- [x] Add exact `Fraction` assertions for the three Blomer–Pascadi margins against the best elementary bound at `ν = 1/2`.
- [x] Assert zero margin at the two published endpoints `ν = 13/28` and `ν = 7/12`.
- [x] Assert that the full-residue scale `ν = 1` is outside the nontrivial range.
- [x] Run the focused test and observe the expected failure before implementation.
- [x] Implement the minimum rational-exponent ledger and rerun the focused test.

### Task 2: Build the exact finite fourth-trace object test-first

**Files:**

- Create: `tests/test_centered_fourth_trace_audit.py`
- Create: `scripts/audit_centered_fourth_trace.py`

- [x] Test the matrix identity
  `tr(T^h1 S T^h2 S T^h3 S T^h4 S) = h1 h2 h3 h4 - (h1+h3)(h2+h4) + 2`
  on fixed literals and a small exhaustive box.
- [x] Test `Δ = tr² - 4`, Jacobi-symbol multiplicativity, and the exceptional set explicitly removed in the published fourth-moment proposition.
- [x] Add a fixed counterexample showing that the raw inverse-cycle solution count is not globally `1 + (Δ/p)`.
- [x] Run the new tests and observe failure before adding production code.
- [x] Implement modular matrices, Jacobi symbols, inverse-cycle counting, and discriminant multiplicity/energy summaries.

### Task 3: Audit whether the trace route reaches the coupled kernel

**Files:**

- Modify: `tests/test_centered_fourth_trace_audit.py`
- Modify: `scripts/audit_centered_fourth_trace.py`
- Modify: `docs/research/2026-08-24-mobius-weighted-off-diagonal.md`

- [x] Add finite audits separating proposition-degenerate tuples, zero discriminants, and repeated nonzero discriminants.
- [x] State the exact coefficient family to which a quadratic large sieve would apply after the trace conversion.
- [x] Check explicitly whether the conversion preserves the outer modulus family, the `a = hδ` coupling, and both Möbius weights.
- [x] If any of these three bridges is absent, record it as the precise missing lemma and do not claim the coupled-kernel gate.
- [x] Record why Menon’s logarithmic averaged-Chowla saving cannot absorb a positive power deficit by itself.

### Task 4: Verify and publish only evidence-backed progress

**Files:**

- Modify: this plan (checkboxes only as tasks finish)

- [x] Run the focused Python tests.
- [x] Run the full Python test suite through `uv`.
- [x] Run the relevant Lean build/check if any Lean source or imported specification changed.
- [x] Inspect the exact diff and theorem-status language.
- [x] If the result is materially new, commit, push, and update the existing Ready-for-view PR; otherwise report the negative result without manufacturing a PR update.

### Task 5: Exploit fixed-numerator spacing without weakening the coefficient structure

**Files:**

- Modify: `tests/test_mobius_type_ii_audit.py`
- Modify: `scripts/audit_mobius_type_ii.py`
- Modify: `docs/research/2026-08-24-mobius-weighted-off-diagonal.md`

- [x] Add failing exact-rational tests for the congruence linking two inverse fractions with the same numerator.
- [x] Prove and exhaustively audit the inverse-linear spacing bound in one balanced dyadic interval.
- [x] Express the coherent modulus family as an operator and compute the exact large-sieve gap at the balanced maximal box.
- [x] Record that an arbitrary product-coefficient spectral norm still loses `A^(1/2)` and that a successful route must retain `hδ`.
- [x] Re-run focused and repository-wide Python verification.
- [x] Commit, push, and update the Ready-for-view PR with the new proved spacing lemma and unchanged coupled-kernel boundary.

### Task 6: Parameterize cross-numerator near collisions before any Cauchy loss

**Files:**

- Modify: `tests/test_mobius_type_ii_audit.py`
- Modify: `scripts/audit_mobius_type_ii.py`
- Modify: `docs/research/2026-08-24-mobius-weighted-off-diagonal.md`

- [x] Add failing finite tests for the exact cross-numerator inverse congruence.
- [x] Prove the associated central-arc Diophantine parameterization and sharp dyadic bounds for its auxiliary integer.
- [x] Expand the uncollapsed product kernel and separate the genuine central arc from noncentral rational arcs.
- [x] Test whether the resulting equation has a usable Type I/II factorization retaining all four Möbius weights.
- [x] Map the remaining estimate against primary literature without importing a withdrawn or mismatched theorem.
- [x] Run focused and repository-wide verification; update the Ready-for-view PR only for a materially new exact reduction or proved estimate.
