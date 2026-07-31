# Zero-Free Gap to Actual PNT Decay Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Turn a moving zero-free logarithmic gap into actual relative PNT decay while preserving the Stack 116 conditional signed-Omega output.

**Architecture:** One abstract amplitude lemma rewrites `Real.rpow` as an exponential. One facade squeezes the actual explicit-formula error using the Stack 116 upper bound.

**Tech Stack:** Lean 4, Mathlib filters and `Real.rpow`, Stack 116 actual transfer.

## Global Constraints

- Modify only `ZeroDensityLayerBudget*`, matching contract/audit files, and task documents.
- Preserve the constructed sigma-only boundary and exact scales.
- Keep signed anti-cancellation witnesses explicit.
- Do not touch protected complementary-bound or Sharp/VK-edge files.
- Do not claim unconditional Omega or RH.

---

### Task 1: Moving-amplitude decay

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetVariableBoundaryZeroFreeUpperDecay.lean`

**Interfaces:**
- Produces: `IsNaturalVariableBoundaryZeroFreeDecay` and `variableBoundaryTargetAmplitude_tendsto_zero_of_zeroFreeDecay`.

- [ ] Define the logarithmic zero-free condition.
- [ ] Rewrite the positive-natural-point target amplitude as an exponential.
- [ ] Compose negation and `Real.tendsto_exp_atBot` to prove decay.

### Task 2: Actual PNT decay facade

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetVariableBoundaryZeroFreeUpperDecay.lean`
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetVariableBoundaryZeroFreeUpperDecayContract.lean`
- Create: `Test/ZeroDensityLayerBudgetVariableBoundaryZeroFreeUpperDecayAxiomAudit.lean`

**Interfaces:**
- Consumes: Stack 116 and Task 1.
- Produces: `actualSigmaOnlyRunningBoundaryZeroFreeUpperDecaySignedOmega`.

- [ ] State the final theorem with the constructed Stack 116 boundary.
- [ ] Squeeze the absolute actual PNT error by the decaying amplitude bound.
- [ ] Return actual PNT decay and the unchanged signed witness conclusion.
- [ ] Add contract and axiom audit targets.
- [ ] Compile, commit, push, and open a draft PR based on Stack 116.
