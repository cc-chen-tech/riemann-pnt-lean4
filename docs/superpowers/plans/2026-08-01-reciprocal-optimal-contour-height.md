# Reciprocal Optimal Contour Height Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove that `1 - beta` is the exact infimum of actual polynomial selected-height exponents in the reciprocal transfer.

**Architecture:** Define feasible contour windows, prove the universal strict lower bound, construct explicit near-optimal windows, and realize them with the existing uniform good-height selector and actual contour remainder certificate.

**Tech Stack:** Lean 4, real linear arithmetic, selected uniform good heights, actual natural-point remainder certificates.

## Global Constraints

- Modify only `ZeroDensityLayerBudgetReciprocalOptimalContourHeight*.lean` and this stack's spec/plan files.
- State optimality as strict lower bound plus arbitrary-precision realization, not a falsely attained minimum.
- Preserve visible-main witness boundaries.
- Do not modify protected, Sharp, or VK-edge modules.
- Compile serially with `nice -n 10` and the existing overlay.

---

### Task 1: Prove arithmetic optimality

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetReciprocalOptimalContourHeight.lean`
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetReciprocalOptimalContourHeightContract.lean`

- [ ] Define feasible reciprocal contour windows.
- [ ] Prove every feasible outer exponent is above `1 - beta`.
- [ ] Construct explicit windows inside every positive neighborhood.

### Task 2: Realize near-optimal windows analytically

**Files:**
- Modify: `PrimeNumberTheorem/ZeroDensityLayerBudgetReciprocalOptimalContourHeight.lean`

- [ ] Prove selected-height polynomial domination at the near-optimal outer exponent.
- [ ] Prove selected-height cofinality.
- [ ] Construct the actual natural-point remainder certificate.

### Task 3: Verify and publish Stack154

**Files:**
- Create: `PrimeNumberTheorem/ZeroDensityLayerBudgetReciprocalOptimalContourHeightAxiomAudit.lean`
- Create: `docs/superpowers/specs/2026-08-01-reciprocal-optimal-contour-height-design.md`
- Create: `docs/superpowers/plans/2026-08-01-reciprocal-optimal-contour-height.md`

- [ ] Compile implementation, contract, and audit serially through the overlay.
- [ ] Confirm only `propext`, `Classical.choice`, and `Quot.sound` are reported.
- [ ] Commit docs and Lean files separately and open a stacked draft PR based on Stack153.
