# Certified Smoothed-Error Difference Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the optimizer's implicit identity finite difference with an explicit certified interval input while preserving a named identity convenience mode, then connect the Lean transfer theorem to both endpoint instances of the existing second-order explicit formula.

**Architecture:** A report-wide approximation-difference object resolves every smoothing width to an interval for `Re(A_T(x+h)-A_T(x))`. Signed interval division converts that interval into endpoint bias, while candidate error envelopes remain separate. The Lean bridge fixes one contour and invokes the existing second-order theorem at `x` and `x+h`, exposing the two Perron truncation bounds and the resulting Chebyshev inequalities.

**Tech Stack:** Python 3 standard library (`decimal`, `dataclasses`, `argparse`, `json`), pytest, Lean 4, Mathlib, Lake targeted roots.

## Global Constraints

- Work only in `.worktrees/smoothed-error-optimization` on `research/smoothed-error-optimization`.
- Do not run a full Lake build.
- Preserve outward interval arithmetic and deterministic UTF-8 JSON.
- Do not claim improved constants without a certified analytic envelope.

---

### Task 1: Certified approximation-difference input

**Files:**
- Modify: `tests/test_smoothed_error_optimizer.py`
- Modify: `experiments/pnt/smoothed_error_optimizer.py`

**Interfaces:**
- Produces: `ApproximationDifferences.identity()` and `ApproximationDifferences.certified(...)`.
- Produces: explicit `approximation=` arguments on `optimize_candidate` and `compare_candidates`.

- [x] Add adversarial tests for signed, non-identity intervals, exact `h` coverage, identity equivalence, and malformed intervals.
- [ ] Run the focused pytest file and confirm failures arise from the missing explicit approximation interface.
- [x] Add general signed interval multiplication/division and resolve every `h` through the selected approximation mode.
- [x] Run the focused pytest file and confirm all tests pass.

### Task 2: Deterministic schema and CLI migration

**Files:**
- Modify: `tests/test_smoothed_error_optimizer.py`
- Modify: `experiments/pnt/smoothed_error_optimizer.py`
- Modify: `docs/research/smoothed-error-optimization-preregistration.md`

**Interfaces:**
- Produces: schema `smoothed-error-comparison-v2`.
- Produces: mutually exclusive CLI inputs `--identity-approximation` and repeated `--approximation-difference H:LOWER:UPPER`.

- [x] Add tests asserting sorted interval serialization, stable repeated JSON bytes, v2 field placement, and explicit CLI mode selection.
- [ ] Confirm the tests fail against v1 output and the old CLI.
- [x] Serialize approximation provenance at report level, remove the incorrect candidate-level identity label, and implement both CLI modes.
- [x] Update the research record with the migration and rerun focused tests.

### Task 3: Genuine second-order endpoint bridge

**Files:**
- Modify: `PrimeNumberTheorem/SmoothedErrorTransfer.lean`
- Modify: `Test/SmoothedErrorTransferContract.lean`
- Modify: `Test/SmoothedErrorTransferAxiomAudit.lean`
- Modify: `docs/research/smoothed-error-optimization-preregistration.md`

**Interfaces:**
- Produces: a theorem existentially constructing residue data at both endpoints on one fixed contour.
- Produces: both norm bounds from `exists_norm_residue_sum_sub_contourRemainder_sub_smoothedPsi_le` and their exact instantiation into `chebyshevPsi_bounds_of_smoothedApproximation`.

- [ ] Write a contract using the proposed endpoint theorem and confirm the targeted root fails before the theorem exists.
- [x] Prove the theorem by invoking the second-order formula separately at `x` and `x+h`, then instantiate the algebraic transfer theorem.
- [x] Record that the remaining analytic API gap is a certified interval for the finite difference of the two second-order contour remainders.
- [x] Run only the targeted Lean contract and axiom-audit roots.

### Task 4: Verification and commit

**Files:**
- Verify all modified files.

- [x] Run the complete Python test suite.
- [x] Run targeted Lean contract and audit commands, inspect `#print axioms`, and scan modified Lean files for placeholders.
- [x] Review `git diff` and the claim boundary.
- [x] Commit the verified changes on `research/smoothed-error-optimization`.
