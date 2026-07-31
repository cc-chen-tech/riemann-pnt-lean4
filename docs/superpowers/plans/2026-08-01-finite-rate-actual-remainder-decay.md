# Finite-Rate Actual Remainder Decay Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Establish ordinary actual PNT remainder decay for each actual Pintz rate candidate and for the pointwise finite-rate optimizer.

**Architecture:** Reuse fixed-rate contour decay and the closed-log majorant, bridge each truncated certificate to the actual remainder, then squeeze a switching optimizer by a finite sum.

**Tech Stack:** Lean 4, Stack123, natural remainder bridge, closed-form full-PNT majorant.

## Constraints

- Create one implementation module and matching contract/audit files.
- Require `k <= 1` for each grid rate, matching the existing contour theorem.
- State ordinary decay only; do not claim target-amplitude negligibility.
- Validate with one low-priority overlay process.

### Task 1: Fixed-rate decay

- [ ] Prove eventual candidate interval membership.
- [ ] Define the exact contour-plus-closed-log upper bound and prove it tends to zero.
- [ ] Derive eventual domination of the actual relative remainder.
- [ ] Squeeze to fixed-rate actual remainder decay.

### Task 2: Finite switching

- [ ] Sum candidate absolute remainders over the finite rate set.
- [ ] Bound the optimizer remainder by the active candidate summand.
- [ ] Prove optimized-height actual remainder decay.

### Task 3: Contract, audit, and PR

- [ ] Add contract and axiom audit targets.
- [ ] Build and publish a draft PR based on Stack123.
