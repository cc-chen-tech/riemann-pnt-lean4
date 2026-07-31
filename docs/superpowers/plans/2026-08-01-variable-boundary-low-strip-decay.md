# Variable-Boundary Low-Strip Decay Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove decay of the actual moving low positive strip and derive the complete moving explicit-formula residual with all zero-tail pieces automatic.

**Architecture:** Define the pointwise variable canonical two-strip input, obtain an empty-cluster uniform norm guard, adapt the global multiplicity/log-power majorant at fixed `beta0`, and instantiate stacks 105-107.

**Tech Stack:** Lean 4, global zero multiplicity, polynomial selected heights, real-power amplitude domination, Carlson visible tail.

## Global Constraints

- Modify only `ZeroDensityLayerBudget*.lean`, matching audits, and task docs.
- Do not modify protected complementary-bound or VK-edge files.
- Keep the fixed low-strip margin and contour certificate explicit.
- Do not claim the moving main witness, both signs, or RH.
- Run one Lean process only after shared CPU pressure subsides.

### Task 1: Variable canonical low layer

- [ ] Define the pointwise canonical two-strip input.
- [ ] Prove low endpoint coverage and a uniform norm lower bound.
- [ ] Identify its low layer with stack107's explicit low Finset.

### Task 2: Fixed-anchor low decay

- [ ] Apply the global multiplicity bound to the moving low layer.
- [ ] Compare the moving target denominator with fixed `beta0`.
- [ ] Squeeze by the existing fixed log-power majorant.

### Task 3: Full residual corollary and audit

- [ ] Instantiate stack107 positive-tail majorization and stack106 real-tail decay.
- [ ] Add contract and axiom audit targets.
- [ ] Compile sequentially and publish a Draft PR based on stack107.
