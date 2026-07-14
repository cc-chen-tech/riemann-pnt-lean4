# Uniform Natural Contour Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the remaining fixed-`x` horizontal-contour constants by estimates uniform for `x >= 2`, then consume them in a natural-point selected-height explicit formula.

**Architecture:** First expose the explicit far-left constant already proved by the functional-equation decomposition and uniformly bound it at `epsilon = 1`. Combine that result with the existing absolute central-band estimate, preserving the necessary `x^2` factor. Then feed the stronger horizontal theorem and the uniform natural-point Perron theorem into `CofinalExplicitFormula` at a sufficiently high polynomial height.

**Tech Stack:** Lean 4, mathlib complex analysis, interval integrals, real inequalities, repository contract tests.

## Global Constraints

- Count only stronger analytic estimates that change theorem quantifier order or close a named explicit-formula gap.
- Do not add conditional `Prop` targets or API-only wrappers.
- Keep constants independent of `x`, `A`, the selected height, and the moving left endpoint unless displayed explicitly.
- Preserve the claim boundary: this is RH infrastructure, not an RH proof.

---

### Task 1: Uniform far-left horizontal edge

**Files:**
- Modify: `PrimeNumberTheorem/LeftHorizontalEdge.lean`
- Test: `Test/UniformNaturalContourContract.lean`

- [x] Add the failing contract with the constant quantified before `x`.
- [x] Verify that it fails because the stronger theorem is absent.
- [x] Factor the existing explicit far-left coefficient or repeat only the necessary quantitative argument.
- [x] Prove the uniform bound for `x >= 2` and `epsilon = 1`.
- [x] Run the contract and the source module.

### Task 2: Uniform complete horizontal contribution

**Files:**
- Modify: `PrimeNumberTheorem/CentralHorizontalEdge.lean`
- Test: `Test/UniformNaturalContourContract.lean`

- [x] Combine the absolute central-band constant with Task 1.
- [x] Absorb the far-left absolute constant into the displayed `x^2` factor.
- [x] Prove one selected-height theorem uniform in `x >= 2` and every left endpoint.
- [x] Run the contract and dependent contour modules.

### Task 3: Natural-point selected-height truncation

**Files:**
- Modify: `PrimeNumberTheorem/CofinalExplicitFormula.lean`
- Create or modify: a focused contract under `Test/`

- [x] Choose an explicit polynomial baseline height in the natural sample `m`.
- [x] Combine the uniform Perron `m^5/W` error with the uniform horizontal `m^2 log^2(A)/T` error.
- [x] Choose the moving-left depth so its contribution is absorbed at the displayed target scale.
- [x] State and prove a theorem whose outer constant is quantified before `m`.
- [x] Run focused and downstream contracts.

### Task 4: Verification and integration

**Files:**
- Modify: theorem inventory, explicit-formula chain, axiom audit, and `lakefile.lean` only as required by the proved surface.

- [x] Run `lake build RiemannPNT`.
- [x] Run Python tests, chain-gap checks, target consistency, and the axiom allowlist.
- [x] Review the diff for mathematical quantifier order and accidental fixed-`x` constants.
- [ ] Commit, merge to `main`, and push only after all gates pass.
