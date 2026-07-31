# Full PNT Budget Rate Optimizer Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Minimize the actual complete hybrid relative PNT budget over Stack123's finite rate grid and prove relative PNT decay.

**Architecture:** Define the per-rate full budget, bridge each actual truncated certificate to a real error upper bound, construct a finite rate minimizer, and squeeze the minimum by the least-rate budget.

**Tech Stack:** Lean 4, Stack123/124, hybrid PNT upper budget, fixed-rate density decay.

## Constraints

- Create one implementation module and matching contract/audit files.
- Optimize over rates directly because the full budget depends on both rate and height.
- State finite-rate exact optimality only; continuous-rate loss remains separate.
- Validate with one low-priority overlay process.

### Task 1: Per-rate full budget

- [ ] Define the concrete full relative budget.
- [ ] Prove it bounds the real relative PNT error at every large sample.
- [ ] Prove fixed-rate budget decay from density and contour decay.

### Task 2: Pointwise full-budget optimizer

- [ ] Select the finite minimum rate and prove membership/minimality.
- [ ] Define the corresponding optimized actual good height and minimum budget.
- [ ] Transfer the real error upper bound to the selected rate.

### Task 3: PNT decay

- [ ] Squeeze the minimum budget by the least-rate budget.
- [ ] Squeeze the real relative PNT error by the minimum budget.
- [ ] Derive an automatic Pintz-constant corollary.

### Task 4: Contract, audit, and PR

- [ ] Add contract and axiom audit targets.
- [ ] Build and publish a draft PR based on Stack124.
