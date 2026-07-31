# Variable-Boundary Exponent Transfer Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Generalize the dynamic transfer machine from a fixed boundary exponent to a genuine schedule `beta(x)` while preserving exact relative and unnormalized scales.

**Architecture:** Define the moving actual package and target amplitude, prove pointwise right-edge and explicit-formula facts, then compose generic negligible-residual and sign-alternative transfers.

**Tech Stack:** Lean 4, Mathlib filters and real powers, actual explicit formula, existing far-witness interfaces.

## Global Constraints

- Add only the variable-boundary transfer module, contract, audit, and docs.
- Preserve the exact `x^(beta x - 1)` and `x^(beta x)` scales.
- Keep residual negligibility and moving-package anti-cancellation as explicit inputs.
- Do not claim simultaneous signs, right-edge attainment, or RH.

---

### Task 1: Variable package and right edge

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetVariableBoundaryExponentTransfer.lean`

**Interfaces:**
- Produces: `variableBoundaryZeroPackage`, `variableBoundaryTargetAmplitude`, `IsVariableBoundaryRightEdge`, membership, strict-complement, and explicit-formula decomposition theorems.

- [ ] **Step 1:** define the package and target amplitude.
- [ ] **Step 2:** prove exact package membership.
- [ ] **Step 3:** prove strict complement real-part inequality from the pointwise right edge.
- [ ] **Step 4:** prove the exact explicit-formula decomposition.

### Task 2: Variable-scale sign transfer

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetVariableBoundaryExponentTransferContract.lean`
- Create: `Test/ZeroDensityLayerBudgetVariableBoundaryExponentTransferAxiomAudit.lean`

**Interfaces:**
- Produces: variable target positivity, natural sign-alternative transfer, variable-exponent unnormalized conversions, and the final unnormalized sign alternative.

- [ ] **Step 1:** prove eventual positivity at natural samples.
- [ ] **Step 2:** transfer an unsigned moving-package witness through a negligible residual.
- [ ] **Step 3:** prove positive and negative relative-to-unnormalized conversions.
- [ ] **Step 4:** assemble the final `Omega+ OR Omega-` variable-exponent theorem.
- [ ] **Step 5:** compile main, contract, and audit serially.
- [ ] **Step 6:** commit docs and Lean code separately and publish a draft PR based on stack99.
