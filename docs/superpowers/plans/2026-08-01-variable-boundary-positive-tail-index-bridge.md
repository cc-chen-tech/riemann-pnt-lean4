# Variable-Boundary Positive-Tail Index Bridge Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Bound the finite visible high positive-zero kernel sum by the variable Carlson tail and derive the stack105 positive-tail majorization.

**Architecture:** Reuse the high-zero subtype embedding, prove term equality under visibility and package exclusion, apply finite-sum-to-tsum domination, then partition the finite positive complement at `sigma`.

**Tech Stack:** Lean 4, Finset embeddings, Summable/tsum, stack101 visible tail, stack105 full-tail budget.

## Global Constraints

- Modify only `ZeroDensityLayerBudget*.lean`, matching audits, and task docs.
- Preserve exact moving target normalization and current-height visibility.
- Keep low-strip decay explicit; do not claim both signs or RH.
- Run one Lean process at a time.

### Task 1: High finite sum to visible tail

- [ ] Define/prove visibility for members of the high subtype Finset.
- [ ] Prove summability of the visible normalized kernel term.
- [ ] Map the finite family into Carlson indices and apply `sum_le_tsum`.

### Task 2: Low/high positive split

- [ ] Define the moving low positive normalized sum.
- [ ] Partition the full positive complement into low and high pieces.
- [ ] Derive `VariableBoundaryVisiblePositiveTailMajorized` automatically.

### Task 3: Audit and publish

- [ ] Add focused contract and axiom audit files.
- [ ] Compile sequentially and publish a Draft PR based on stack106.
