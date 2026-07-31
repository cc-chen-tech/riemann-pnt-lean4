# Reciprocal Variable-Boundary Transfer Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Propagate the reciprocal low-layer margin through the monotone variable-boundary upper and conditional signed PNT transfer.

**Architecture:** Bound the moving low layer by global reciprocal mass and a fixed lower amplitude anchor, feed that convergence into the existing full-tail residual assembler, then reuse variable package caps and signed witness transfer.

**Tech Stack:** Lean 4, Stack150 reciprocal layer bound, Stack151 explicit-formula transfer, existing variable-boundary absorption and signed-transfer modules.

## Global Constraints

- Modify only `ZeroDensityLayerBudgetReciprocalVariableBoundaryTransfer*.lean` and this stack's spec/plan files.
- Keep old variable-boundary theorems intact.
- Preserve the explicit visible-main witness boundary.
- Do not modify protected, Sharp, or VK-edge modules.
- Compile serially with `nice -n 10` and the existing overlay.

---

### Task 1: Prove reciprocal variable low-layer decay

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetReciprocalVariableBoundaryTransfer.lean`
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetReciprocalVariableBoundaryTransferContract.lean`

- [ ] Reuse the generic reciprocal layer bound on the variable canonical low bucket.
- [ ] Compare the moving amplitude with the fixed `beta0` amplitude.
- [ ] Prove convergence under `sigma - beta0 + epsilon < 0`.

### Task 2: Reassemble variable residual and signed transfer

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetReciprocalVariableBoundaryTransfer.lean`

- [ ] Feed reciprocal low decay into the automatic high/real full-tail assembler.
- [ ] Transfer positive and negative main witnesses through the new residual.
- [ ] Combine the residual with the variable package coefficient cap.

### Task 3: Verify and publish Stack152

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetReciprocalVariableBoundaryTransferAxiomAudit.lean`
- Create: `docs/superpowers/specs/2026-08-01-reciprocal-variable-boundary-transfer-design.md`
- Create: `docs/superpowers/plans/2026-08-01-reciprocal-variable-boundary-transfer.md`

- [ ] Compile implementation, contract, and audit serially through the overlay.
- [ ] Confirm only `propext`, `Classical.choice`, and `Quot.sound` are reported.
- [ ] Commit docs and Lean files separately and open a stacked draft PR based on Stack151.
