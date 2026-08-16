# Merge-path resolution and strategy update (2026-08-16)

## What happened

- PR #466 (assembly layer) and #467 (gate contract) were CLOSED WITHOUT
  merge by the repository owner on 2026-08-15.
- Inspection of `origin/main` shows the assembly layer
  (`HalfIsolatedZeroDichotomy/*`, `ZeroDensityAmplificationAudit*` — 13
  files, `ExceptionalZeroAmplification*`) and the gate contract
  (`ExceptionalZeroAmplificationGate{Contract,AxiomAudit}.lean`) are ALL
  on main, merged through other PRs (latest: #473 "half-isolated zeta
  capacity and detect/count bridges").
- `origin/main`'s `ExceptionalZeroAmplificationGateContract.lean` is
  byte-identical to our file: the owner adopted the content directly.

Conclusion: the PR closure was a workflow choice (owner-side merge path),
not a rejection of the content.  The assembly + gate contract are landed.

## Consequences for the goal

1. The authority base for further work is `origin/main` (currently
   `2b884906`, toolchain v4.29.1), not our worktree branches.
2. `DetectionPointChoice.lean` (L1) does NOT exist on main yet — the L1
   promotion (Appendix A proved, B/main as axioms) is the next main-bound
   contribution.  Its content is ready in the worktrees; it should be
   applied on top of a fresh `origin/main` checkout.
3. The running merge-test build (bash-1) still has value: its shared
   `vendor/mathlib` cache rebuild is machine-wide, and its dependency
   closure covers `HalfIsolatedZeroDichotomy.Contract` (needed to compile
   `DetectionPointChoice`).  After it finishes, re-anchor the worktree to
   `origin/main`, rebuild incrementally, then compile `DetectionPointChoice`.
4. Do NOT re-push PRs for content already on main.  Future contributions
   follow the owner's merge conventions (direct branch/PR against the
   current main), to be coordinated when the L1 promotion is ready.

## Open items unchanged

- L1 promotion (Appendix A compiled, Appendix B, main assembly);
- beta > 14/17 single-layer forcing (aligned with the cubic worktree);
- full `Re > 2/3` objective: strip (2/3, 14/17] still needs a new
  mechanism (directed detector withdrawn, see `L3-defect-record.md`).
