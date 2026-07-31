# Balanced-Rate Grid Approximation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove a multiplicative finite-grid approximation theorem for the continuous classical balanced rate.

**Architecture:** Reuse the exact continuous optimizer, show rates below it lie on the contour-controlled branch, maximize the envelope rate over the finite grid via finite minimization of its negative, and transfer the rate bound to exponential envelopes.

**Tech Stack:** Lean 4, Stack125 rate grid, classical zero-free profile and admissible balanced-rate modules.

## Constraints

- Create one implementation module and matching contract/audit files.
- Do not assert continuity of actual zero counts or good-height choices.
- Quantify approximation by an explicit factor `q >= 1`.
- Validate with one low-priority overlay process.

### Task 1: Below-optimum branch arithmetic

- [ ] Prove `classicalDynamicBalancedRate b k = k` for `0 < k <= rStar`.
- [ ] Derive the `rStar / q` candidate lower bound and competing exponential envelope.

### Task 2: Finite-grid envelope optimizer

- [ ] Build the positive finite rate-value grid.
- [ ] Select the rate maximizing the balanced envelope.
- [ ] Prove membership, maximality, the `1/q` lower bound, and the continuous-optimum upper bound.

### Task 3: Contract, audit, and PR

- [ ] Add contract and axiom audit targets.
- [ ] Build and publish a draft PR based on Stack125.
