# Geometric Moving Right-Edge Unified Transfer Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Derive the indexed Carlson visible right edge from the direct finite-zero right edge and expose the resulting canonical-good-height moving transfer.

**Architecture:** One bridge lemma converts an indexed zero into membership of the visible positive-zero Finset and applies the geometric right-edge bound. One facade applies the Stack 113 theorem using that bridge.

**Tech Stack:** Lean 4, Mathlib Finsets, repository Carlson zero indices and explicit-formula transfer modules.

## Global Constraints

- Touch only `ZeroDensityLayerBudget*`, matching contract/audit files, and task documents.
- Preserve the exact moving upper and signed lower scales.
- Keep `beta`, its monotonicity/lower anchor, and signed witnesses explicit.
- Do not modify the protected complementary-bound module.
- Do not claim unconditional Omega or RH.

---

### Task 1: Geometric-to-indexed right-edge bridge and facade

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetVariableBoundaryGeometricRightEdgeUnifiedUpperSignedOmega.lean`
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetVariableBoundaryGeometricRightEdgeUnifiedUpperSignedOmegaContract.lean`
- Create: `Test/ZeroDensityLayerBudgetVariableBoundaryGeometricRightEdgeUnifiedUpperSignedOmegaAxiomAudit.lean`

**Interfaces:**
- Consumes: `IsVariableBoundaryRightEdge`, `actualCarlsonPositiveZero_spec`, and the Stack 113 theorem.
- Produces: `IsVariableBoundaryRightEdge.toIndexedVisible` and `actualMonotoneGeometricVariableBoundaryCanonicalGoodHeightUnifiedUpperSignedOmega`.

- [ ] **Step 1: Prove the bridge**

Construct membership in `positiveNontrivialZerosFinset (H(m))` from the indexed
zero specification and the visible ordinate inequality, then apply the direct
right-edge hypothesis.

- [ ] **Step 2: Add the facade**

Apply the Stack 113 theorem with `hright.toIndexedVisible` and preserve all
remaining arguments and conclusions.

- [ ] **Step 3: Add contract and axiom audit**

Use `#check` for both declarations and `#print axioms` for both declarations.

- [ ] **Step 4: Verify and publish**

Compile all three targets sequentially with the overlay, stage exactly the
three Lean files, commit, push, and open a draft PR based on Stack 113.
