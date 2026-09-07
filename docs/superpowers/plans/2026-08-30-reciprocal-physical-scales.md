# Reciprocal Physical Scales Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. The user has already authorized inline execution and ready-for-review publication; do not ask again.

**Goal:** Correct the complementary-Poisson scale and certify the finite boundary ledger without claiming the coupled-kernel gate.

**Architecture:** A small exact-rational module records the physical coordinate changes and integer interval endpoints. A Chinese-first research note proves the corrected critical smooth-model lemma using the published MRSTT input and lists the still-missing physical transfers.

**Tech Stack:** Python standard-library fractions, pytest; no Lean changes.

**Spec:** User's signed-operator proof boundary and the mathematical specification in `docs/research/2026-08-30-mwkf-reciprocal-physical-scales.md` (RP1–RP12).

## Global Constraints

- Preserve the existing isolated worktree and every unrelated change.
- PR #483 is a read-only source at commit `7cc472d45f934f7465a8543273a3bb866ef8da5a`; publish our findings only on PR #490.
- Tests certify finite calculations, not MRSTT, the physical adapter, or the full moment.
- Use `M=A*S/R`, `X=S/(e*r)`, and phase numerator `-j*A*k*l/r`; retain the integer-count boundary and the `c=0` packet separately.

### Task 1: Exact scale and boundary regression

**Files:** Create `scripts/mwkf_reciprocal_scale_adapter.py` and `tests/test_mwkf_reciprocal_scale_adapter.py`.

**Interfaces:** `reciprocal_scales(R,S,A,e,r,j,kl)` returns exact rational scales, Jacobian, phase and weighted per-mode budget. `complementary_interval_ledger(D,r,M,Z)` returns the finite nonzero-c pair count, weighted count and continuous/boundary upper bounds. `cubic_window_margin(u,a)` returns the exact worst-case Taylor margin with the fixed parameters in RP7.

- [x] Write tests with literal witnesses: `(R,S,A)=(100,1000,75)` gives `M=750`, `D/M=4/3`, and per-mode outer budget `1/100`; `(D,r,M,Z)=(5,1,0,30)` has three nonzero-c pairs and weighted mass `7/15` despite zero continuous length. Compare all small interval outputs to an independent enumeration.
- [x] Run `pytest -q tests/test_mwkf_reciprocal_scale_adapter.py -p no:cacheprovider`; verify assertion failures for missing interfaces (19 expected failures).
- [x] Implement exact fraction arithmetic, ceiling/floor endpoints, and the explicit harmonic bound `(4*M*H_C/r+2*C)/D`, `C=floor((abs(Z)+M)/D)`.
- [x] Rerun the focused tests; compare the scale change also to a Gaussian Poisson fixture whose Fourier transform is explicit (19 passed, including 2400 enumerated boxes).

### Task 2: Mathematical handoff and publication

**Files:** Create the RP research note above; add Section 9.203 to `docs/research/2026-08-24-mobius-weighted-off-diagonal.md`.

- [x] Prove the scaled c-Poisson formula, the physical dilation witness, the MRSTT sliding lemma with Taylor and edge errors, and the finite boundary bound. State all physical/mask and aggregation hypotheses.
- [x] Reuse the independent reviewer to check the corrected critical prefactor and the boundary statement; fix any must-fix findings (none; reviewer also checked 1000 random rational boxes and three Gaussian fixtures).
- [x] Run the available Python suite (excluding the two previously identified Flint-dependent files), Ruff correctness checks, and `git diff --check`; record actual exit codes and counts (983 passed, 1 skipped; all commands exited 0).
- [ ] Stage only the four new files and the main-note index, commit, normal-push the existing branch, refresh PR #490 as non-Draft. Do not merge or edit #483 and do not mark the persistent goal complete.
