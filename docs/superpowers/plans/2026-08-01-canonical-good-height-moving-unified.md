# Canonical Good-Height Moving Unified Transfer Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Specialize the Stack 112 moving upper/signed-Omega theorem to the canonical selected good-height schedule and eliminate all external height and contour certificates.

**Architecture:** A single facade theorem obtains the three height-side inputs from `actualDynamicBoundaryCanonicalSelectedGoodHeight_spec`, then applies `actualMonotoneVariableBoundaryUnifiedUpperSignedOmega` with the canonical schedule. A contract exposes the signature and an axiom audit checks the declaration boundary.

**Tech Stack:** Lean 4, Mathlib filters and asymptotics, repository explicit-formula and Carlson modules.

## Global Constraints

- Modify only `ZeroDensityLayerBudget*` files, matching contract/audit files, and this task's documents.
- Do not read, modify, stage, or overwrite `ZeroForcedOscillationComplementaryBound.lean`.
- Preserve the exact scales `m^(beta(m)-1)` and `x^(beta(x))`.
- Keep moving right-edge and positive/negative main-term witnesses explicit.
- Do not claim unconditional Omega or RH.

---

### Task 1: Canonical good-height specialization

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetVariableBoundaryCanonicalGoodHeightUnifiedUpperSignedOmega.lean`
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetVariableBoundaryCanonicalGoodHeightUnifiedUpperSignedOmegaContract.lean`
- Create: `Test/ZeroDensityLayerBudgetVariableBoundaryCanonicalGoodHeightUnifiedUpperSignedOmegaAxiomAudit.lean`

**Interfaces:**
- Consumes: `actualDynamicBoundaryCanonicalSelectedGoodHeight_spec` and `actualMonotoneVariableBoundaryUnifiedUpperSignedOmega`.
- Produces: `actualMonotoneVariableBoundaryCanonicalGoodHeightUnifiedUpperSignedOmega`.

- [ ] **Step 1: Add the public specialization theorem**

Import the Stack 112 theorem and the canonical good-height theorem.  State the
same moving upper/signed-Omega conclusion with
`H = actualDynamicBoundaryCanonicalSelectedGoodHeight alpha`, omitting
`hHle`, `hHtop`, and `remainder` from the hypotheses.

- [ ] **Step 2: Derive the height inputs**

Use

```lean
rcases actualDynamicBoundaryCanonicalSelectedGoodHeight_spec
    hbeta0 halpha halphaOne hcontourMargin with
  ⟨hHle, hHtop, remainder⟩
```

and pass those three facts to the Stack 112 theorem.

- [ ] **Step 3: Add the contract and axiom audit**

The contract contains:

```lean
#check PrimeNumberTheorem.actualMonotoneVariableBoundaryCanonicalGoodHeightUnifiedUpperSignedOmega
```

The audit contains:

```lean
#print axioms PrimeNumberTheorem.actualMonotoneVariableBoundaryCanonicalGoodHeightUnifiedUpperSignedOmega
```

- [ ] **Step 4: Compile the three direct targets**

Run the implementation, contract, and audit through `lake env lean` with the
existing overlay, sequentially and with one Lean process.

Expected: all commands exit 0; the audit lists only `propext`,
`Classical.choice`, and `Quot.sound`.

- [ ] **Step 5: Commit and publish**

Stage only the three Lean files and commit:

```bash
git commit -m "feat: specialize moving transfer to canonical good heights"
```

Push the branch and open a draft PR based on the Stack 112 branch.
