# Joint Two-Height Parameter Feasibility Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Construct one parameter tuple that simultaneously gives negative low-layer and Carlson two-height target-amplitude exponents for every `2 / 3 < beta < 1`.

**Architecture:** Add one isolated real-arithmetic theorem downstream of the existing low-layer and Carlson exponent modules. The theorem chooses nested midpoints and a capped common outer-height exponent, then packages exact balanced cuts and positive margins for both transfer mechanisms.

**Tech Stack:** Lean 4, Mathlib real arithmetic, repository contract and axiom-audit conventions.

## Global Constraints

- Modify only `ZeroDensityLayerBudget*.lean` and task design/plan files.
- Do not modify `ZeroForcedOscillationComplementaryBound.lean`.
- Do not modify VK-edge files.
- Do not claim a sharp oscillation theorem, Guth-Maynard formalization, or RH consequence.

---

### Task 1: Joint numerical feasibility theorem

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightParameterFeasibility.lean`

**Interfaces:**
- Consumes: `targetAmplitudeCarlsonTwoHeightBalancedSlope_lt_half`, `carlsonTwoHeightBalancedCut_pos`, `carlsonTwoHeightBalancedCut_lt_alpha`, and the balanced exponent identities.
- Produces: `exists_jointTwoHeightTargetAmplitudeParameters`.

- [ ] **Step 1: Define the theorem contract**

Return witnesses `sigma`, `tau`, `alpha`, `gammaLow`, `gammaHigh`,
`epsilonLow`, and `epsilonHigh`, including all strict margin conclusions.

- [ ] **Step 2: Construct nested real intervals**

Choose `sigma` below `(3 * beta - 1) / 2`, choose `tau` below the Carlson
feasibility ceiling, and choose `alpha` below the minimum of the low, high,
and unit ceilings.

- [ ] **Step 3: Close balanced margins**

Set `gammaLow = alpha / 2`, use the existing Carlson balanced cut for
`gammaHigh`, and define each epsilon as half the negative common exponent.

- [ ] **Step 4: Compile the implementation**

Run:

```bash
lake env lean PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightParameterFeasibility.lean
```

Expected: exit code 0.

### Task 2: Contract and axiom audit

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetJointTwoHeightParameterFeasibilityContract.lean`
- Create: `Test/ZeroDensityLayerBudgetJointTwoHeightParameterFeasibilityAxiomAudit.lean`

**Interfaces:**
- Consumes: `exists_jointTwoHeightTargetAmplitudeParameters`.
- Produces: import-level API and axiom evidence.

- [ ] **Step 1: Add the contract**

Use `#check exists_jointTwoHeightTargetAmplitudeParameters`.

- [ ] **Step 2: Add the axiom audit**

Use `#print axioms exists_jointTwoHeightTargetAmplitudeParameters`.

- [ ] **Step 3: Compile both audit files**

Run direct `lake env lean` commands for the contract and audit.

Expected: both exit with code 0; the theorem reports only the repository's
standard classical axioms.

### Task 3: Publish bounded stacked PR

**Files:**
- Stage only the five files listed in Tasks 1 and 2 plus this design and plan.

**Interfaces:**
- Consumes: validated local files.
- Produces: a draft PR based on stack43.

- [ ] **Step 1: Commit documentation separately**

Commit the design and implementation plan.

- [ ] **Step 2: Commit Lean code**

Commit the implementation, contract, and axiom audit.

- [ ] **Step 3: Push and open a draft PR**

Use branch
`research/pintz-carlson-stack-44-joint-two-height-parameter-feasibility`
and base
`research/pintz-carlson-stack-43-automatic-good-height-natural-unified-transfer`.

