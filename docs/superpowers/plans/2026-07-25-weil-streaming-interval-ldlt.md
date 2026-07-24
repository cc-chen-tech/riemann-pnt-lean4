# Weil Streaming Interval LDL Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build and run a rigorous bounded-storage interval LDL pipeline for the
sharded `(100,200)` Weil intersection.

**Architecture:** A standard-library reader authenticates source shards and
checkpoint JSON. Python-flint performs block Schur updates and interval
factorization. Mutable Schur blocks and factor panels are content-addressed
files in a workspace; the final checkpoint records only rigorous outcomes.

**Tech Stack:** Python 3.12, python-flint 0.8.0 Arb, exact `Fraction`, canonical
JSON, deterministic gzip, pytest.

## Global Constraints

- Modify only `research/weil-extremal-kernels-next`.
- Never infer a sign from floating-point eigenvalues.
- Stop at the first pivot interval containing zero.
- Require an exact rational negative witness before a negative claim.
- Keep `gate_a_status = "not_satisfied"` without analytic transfer.

---

### Task 1: Checkpoint Contract

**Files:**
- Create: `experiments/rh/weil_extremal_streaming_ldlt.py`
- Create: `tests/test_weil_extremal_streaming_ldlt.py`

- [ ] Write tests for positive, unresolved and tampered checkpoint records.
- [ ] Implement canonical rational parsing, source binding and the
  standard-library verifier.
- [ ] Run the focused tests.

### Task 2: Streaming Arb Factorizer

**Files:**
- Modify: `experiments/rh/weil_extremal_streaming_ldlt.py`
- Modify: `tests/test_weil_extremal_streaming_ldlt.py`

- [ ] Write tests that require bounded block files and deterministic replay.
- [ ] Implement source-tile loading, Arb outward serialization, panel LDL,
  Schur updates and workspace manifests.
- [ ] Run fixture factorization at two precisions.

### Task 3: Full 896-Bit Run

**Files:**
- Create: `experiments/rh/reference/groskin_2607_02828_v1_c100_N200_streaming_ldlt_896_checkpoint.json`

- [ ] Run against the committed 401-by-401 high intersection.
- [ ] Record all rigorously positive pivots and the first unresolved pivot, or
  emit a positive certificate if all pivots are strictly positive.
- [ ] Replay the checkpoint verifier in `python -S`.

### Task 4: High-Precision Route

**Files:**
- Create: `experiments/rh/reference/groskin_2607_02828_v1_c100_N200_streaming_ldlt_high_precision_plan.json`
- Create: `docs/research/weil-streaming-interval-ldlt-2026-07-25.md`

- [ ] Bind the 9000/9512 provenance digests and registered parameters.
- [ ] Specify precision-dependent outward digits, tile geometry, disk budget,
  commands and acceptance conditions.
- [ ] Document that provenance metadata is not dual-route matrix evidence.

### Task 5: Verification and Commit

- [ ] Run all Weil Python tests.
- [ ] Run standard-library checkpoint replay and independent fixture
  regeneration.
- [ ] Check source formatting, overclaim language and clean worktree scope.
- [ ] Commit the implementation, artifacts, tests and documentation.
