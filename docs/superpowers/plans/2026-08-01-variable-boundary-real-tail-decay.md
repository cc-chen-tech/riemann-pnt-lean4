# Variable-Boundary Real-Tail Decay Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove the actual moving-package real-ordinate normalized tail tends to zero from a fixed strict real-part gap.

**Architecture:** Build a finite fixed-exponent majorant, prove its termwise decay, establish a pointwise moving-tail bound using deletion and target-amplitude domination, then squeeze and feed the result into stack105.

**Tech Stack:** Lean 4, finite sums, real powers, stack103 amplitude domination, stack105 full-tail budget.

## Global Constraints

- Modify only `ZeroDensityLayerBudget*.lean`, matching audits, and this task's documentation.
- Do not modify protected complementary-bound or VK-edge files.
- Keep the fixed strict real-part gap explicit.
- Do not claim positive-tail closure, both oscillation signs, or RH.
- Run at most one Lean process at a time.

---

### Task 1: Fixed finite real-zero majorant

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetVariableBoundaryRealTailDecay.lean`

**Interfaces:**
- Produces: `variableBoundaryRealOrdinateFixedMajorant` and its convergence theorem.

- [ ] **Step 1:** define the finite sum over the height-zero real-ordinate zero set.
- [ ] **Step 2:** compose each fixed-beta kernel limit with natural casting.
- [ ] **Step 3:** apply finite-sum convergence.

### Task 2: Moving-tail comparison and assembly

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetVariableBoundaryRealTailDecay.lean`

**Interfaces:**
- Produces: the pointwise majorization, moving real-tail decay, and stack105 residual corollary.

- [ ] **Step 1:** bound the norm of the deleted finite sum by the full sum of norms.
- [ ] **Step 2:** enlarge the denominator from fixed `beta0` to moving `beta(m)`.
- [ ] **Step 3:** squeeze the moving real tail by the fixed majorant.
- [ ] **Step 4:** instantiate stack105's full residual theorem.

### Task 3: Audit and publish

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetVariableBoundaryRealTailDecayContract.lean`
- Create: `Test/ZeroDensityLayerBudgetVariableBoundaryRealTailDecayAxiomAudit.lean`

- [ ] **Step 1:** add focused signature and axiom checks.
- [ ] **Step 2:** compile all targets sequentially.
- [ ] **Step 3:** publish a Draft PR based on stack105.
