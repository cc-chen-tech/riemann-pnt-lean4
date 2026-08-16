# Merge-path dependency audit: amplification assembly layer -> main

## Date and scope

Audit of the branch `research/exceptional-zero-amplification-integration`
(worktree `exceptional-zero-amplification-integration`, HEAD `fce39509`)
against `main` (`d3fb11c7`, 307 commits ahead of the merge base
`75af0d91`).

Goal: establish the exact file set and ordering needed to land the
amplification assembly layer (plus the gate contract) on `main`, and verify
the merged tree builds.

## Result summary

- **21 assembly `.lean` files are new on `main`** (see list below).
- **3 files are already on `main` in a newer form** and must be skipped:
  `PrimeNumberTheorem/ZeroForcedOscillationComplementaryBound.lean`,
  `Test/ZeroForcedOscillationComplementaryBound{Contract,AxiomAudit}.lean`.
- **`lakefile.lean` needs no change**: `main` already registers
  `PrimeNumberTheorem.ZeroForcedOscillationComplementaryBound` and both
  `Test.ZeroForcedOscillationComplementaryBound*` entries.
- **All 16 direct dependency modules are byte-identical between the merge
  base and `main`** (zero interface drift): HardyIntegralContradiction,
  ExplicitFormulaAllHeights/Aux/Truncated, GlobalZeroCount,
  LocalSeparationKernel, NontrivialZeroMultiplicity, PintzEnvelope,
  RiemannVonMangoldt.CriticalLinePartition, ZeroDensityClusterComparisonGrowth,
  ZeroDensityCount, ZeroDensityLayerBudgetAsymptoticTransfer/Carlson,
  ZeroForcedOscillation, ZeroForcedOscillationExplicitFormula,
  ZeroFreeRegion.MeromorphicAux.
- The `main` version of `ZeroForcedOscillationComplementaryBound.lean` removed
  19 top-level names (moving-height/maximal-package energy series); **none of
  the 21 new files references any of them**.  The three names the new files do
  use (`maximalComplementaryRealPartGap`, `maximalZeroRealPart`,
  `norm_zeroPackageUncontrolledRemainder_le_complementary_add_approximation`)
  survive on `main`.
- `ExplicitFormulaResidues.exists_norm_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le_log_sq_div`
  (used by `HalfIsolatedZeroDichotomy/Audit.lean`) exists on `main`.

## File list (merge in this order)

All under `PrimeNumberTheorem/`:

1. `ZeroDensityAmplificationAudit.lean`
2. `ZeroDensityAmplificationAuditContract.lean`
3. `ZeroDensityAmplificationAuditAxiomAudit.lean`
4. `ZeroDensityAmplificationAuditIteration.lean`
5. `ZeroDensityAmplificationAuditIterationContract.lean`
6. `ZeroDensityAmplificationAuditIterationAxiomAudit.lean`
7. `ZeroDensityAmplificationAuditIterationDepth.lean`
8. `ZeroDensityAmplificationAuditIterationDepthContract.lean`
9. `ZeroDensityAmplificationAuditIterationDepthAxiomAudit.lean`
10. `ZeroDensityAmplificationAuditIterationExpansion.lean`
11. `ZeroDensityAmplificationAuditIterationExpansionContract.lean`
12. `ZeroDensityAmplificationAuditIterationExpansionAxiomAudit.lean`
13. `ZeroDensityAmplificationAuditIterationHalfIsolatedAdapter.lean`
14. `VKEdgeConditionalPackage.lean`
15. `VKEdgeConditionalPackageContract.lean`
16. `VKEdgeConditionalPackageAudit.lean`
17. `HalfIsolatedZeroDichotomy.lean`
18. `HalfIsolatedZeroDichotomy/Contract.lean`
19. `HalfIsolatedZeroDichotomy/Audit.lean`
20. `ExceptionalZeroAmplificationIntegration.lean`
21. `ExceptionalZeroAmplificationContract.lean`
22. `ExceptionalZeroAmplificationGateContract.lean` (new in this session)
23. `ExceptionalZeroAmplificationGateAxiomAudit.lean` (new in this session)

## PR split recommendation

- **PR 1 (assembly layer)**: files 1-21.  Pure assembly; all proofs closed in
  the branch, `#print axioms` audits included (files 3, 6, 9, 12, 16).
- **PR 2 (gate contract)**: files 22-23, depending on PR 1.  The gate theorem
  is an instantiation of the proved assembly; its axiom audit must print only
  `[propext, Classical.choice, Quot.sound]` (verified in the source worktree
  build).

Optionally include the two docs updates
(`docs/research/zero-forced-oscillation-preregistration.md` and the
integration design docs) in PR 1.

## Verification performed

- Source-worktree build of the same target already succeeded (8346 jobs,
  all green) on the branch HEAD `fce39509`.
- Static merge-equivalence evidence:
  - all 16 direct dependency modules byte-identical between the merge base
    and `main`;
  - the transitive import closure of the gate target is 97 repository
    modules, whose intersection with the 268 modules changed on `main` is
    exactly one file (`ZeroForcedOscillationComplementaryBound.lean`),
    audited name-by-name above.
- A full merge-test build was attempted (`merge-test-amplification` worktree
  at `main` + the 23 files).  It failed on **environment, not code**: the
  `vendor/mathlib` symlink shares one `.lake/build` across worktrees, and a
  concurrent build in another worktree wrote the same olean files
  (`error: no such file or directory (error code: 4294967294)` on three
  Mathlib modules).  The merge-test worktree is kept for a later rebuild;
  the practical verification point is the PR CI, which builds on a clean
  machine.

## Remaining risks

- The full `lean_lib` default target was not built locally; PR CI covers it.
- `docs/research/zero-forced-oscillation-preregistration.md` differs between
  the branch and `main`; check which version should win.
- `PrimeNumberTheorem/HalfIsolatedZeroDichotomy/DetectionPointChoice.lean`
  and `Test/DetectionPointChoiceAxiomAudit.lean` (the L1 skeleton, added
  after this audit) are NOT part of the merge file list above; they are
  unverified research targets (axioms) and should NOT go into PR 1.
