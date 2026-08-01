# VK Edge Sharp Left-Gap Stability Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Preserve the genuine cofinal low-height zeta Gaussian-energy lower bound after deleting any fixed finite zero set separated to the left of the target real part.

**Architecture:** A finite-package module proves exponential decay, exact complement subtraction, and a quantitative energy-transfer inequality. A composition module applies those results to the existing true-zeta low-height theorem, with `S` affecting only the eventual threshold.

**Tech Stack:** Lean 4.29.1, Mathlib measure theory and complex analysis, project zeta explicit-formula modules, exact contract files, axiom audits.

## Global Constraints

- Work only on `research/vk-edge-sharp-left-gap-stability` based on PR #263.
- Keep outer exponent `alpha` separate from detector exponent `gammaLow`.
- Do not modify Gate B witness/growth modules or Carlson/Gram-Schur modules.
- Do not claim arbitrary-`S` repeatability, a zero-density contradiction, or RH.
- Run no more than four globally concurrent Lean builds and use this worktree's own build/cache outputs.

---

### Task 1: Lock the finite-package interfaces

**Files:**
- Create: `Test/VKEdgeSharpLeftGapDecayContract.lean`
- Create: `PrimeNumberTheorem/VKEdgeSharpLeftGapDecay.lean`

**Interfaces:**
- Consumes: `normalizedFiniteZeroClusterContribution`, `normalizedFiniteZeroClusterComplementContribution`, `nontrivialZerosFinset`.
- Produces: `norm_normalizedFiniteZeroClusterContribution_le_exp_leftGap`, `normalizedFiniteZeroClusterContributionForwardGaussianSecondMoment_le_exp_leftGap`, `normalizedFiniteZeroClusterComplementContribution_empty_eq_selected_add_complement`, and a fixed-height deletion-energy lower bound.

- [x] Write the exact contract with the four intended public signatures.
- [x] Compile the contract and confirm failure because the module/declarations are absent.
- [x] Implement the selected-package pointwise exponential bound using the real-part gap and finite triangle inequality.
- [x] Integrate the pointwise square bound against the nonnegative normalized Gaussian and use total Gaussian mass at most one.
- [x] Prove eventual containment of a fixed finite nontrivial-zero set in `nontrivialZerosFinset Tlow` as `Tlow -> infinity`.
- [x] Prove the exact empty-complement decomposition and the `2-2` energy-transfer inequality.
- [x] Compile source and contract in this worktree's isolated output path.

### Task 2: Compose the genuine cofinal endpoint

**Files:**
- Create: `Test/VKEdgeSharpLeftGapStabilityContract.lean`
- Create: `PrimeNumberTheorem/VKEdgeSharpLeftGapStability.lean`

**Interfaces:**
- Consumes: `exists_eventually_emptyClusterLowHeightNormalizedComplementSecondMoment_gt` and every Task 1 theorem.
- Produces: `exists_eventually_leftGapFiniteSetLowHeightNormalizedComplementSecondMoment_gt`.

- [x] Write the exact endpoint contract first and confirm the expected missing-declaration failure.
- [x] Show the fixed selected-package Gaussian energy tends to zero along `a = log Y`.
- [x] Combine eventual height containment, the true `S = empty` lower bound, and fixed-height deletion stability.
- [x] Retain a fixed positive fraction of `initialEmptyClusterFullMovingGaussianL2Constant`; allow only the eventual onset to depend on `S` and `delta`.
- [x] Compile source and exact contract.

### Task 3: Audit and publish the milestone

**Files:**
- Create: `Test/VKEdgeSharpLeftGapDecayAxiomAudit.lean`
- Create: `Test/VKEdgeSharpLeftGapStabilityAxiomAudit.lean`
- Modify: `Test/MultiplicityAxiomAudit.lean`
- Modify: `scripts/check_axiom_allowlist.py`
- Create: `docs/research/vk-edge-sharp-left-gap-stability-boundary.md`

**Interfaces:**
- Consumes: all public declarations from Tasks 1-2.
- Produces: exact audit coverage and a claim-boundary record.

- [x] Add dedicated `#print axioms` audits and first verify they fail before the allowlist update.
- [x] Register every public theorem in the central audit and allowlist.
- [x] Run focused source, contract, dedicated audit, central audit, allowlist registration parser, target consistency, chain-gap, placeholder, and diff checks.
- [x] Record that strictly-left finite deletions are harmless while same-layer deletion remains the exact analytic blocker.
- [ ] Commit, push, and open a small Draft PR stacked on PR #263.
