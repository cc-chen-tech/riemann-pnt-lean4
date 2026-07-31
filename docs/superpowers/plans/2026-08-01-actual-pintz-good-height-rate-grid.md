# Actual Pintz Good-Height Rate Grid Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build a finite Pintz rate optimizer whose candidates are actual uniform good heights and carry exact truncated PNT certificates.

**Architecture:** Regularize selected good heights at small scales, use the least positive rate for the diverging envelope, reuse dynamic finite-grid optimization, and recover a rate witness from image membership.

**Tech Stack:** Lean 4, `PintzCarlsonRateGridInput` ideas, uniform good-height selection, dynamic finite-grid optimization.

## Constraints

- Create one implementation module and matching contract/audit files.
- Do not modify existing rate-grid, protected, Sharp, or VK-edge modules.
- Keep full-budget decay and continuous cost-cover as later stacks.
- Validate with one low-priority overlay process.

### Task 1: Actual rate candidates and lower envelope

- [ ] Define the finite rate-grid structure and regularized candidate height.
- [ ] Prove rate monotonicity of `pintzCarlsonHeight`.
- [ ] Construct the positive finite candidate grid and diverging lower envelope.

### Task 2: Optimizer certificates

- [ ] Define the dynamic grid and cost optimizer.
- [ ] Recover the selected rate and exact finite-rate cost optimality.
- [ ] Prove eventual Pintz interval membership and analytic good-height status.
- [ ] Recover the natural-point truncated explicit-formula certificate at the optimized height.

### Task 3: Contract, audit, and PR

- [ ] Check all public interfaces and audit central theorems.
- [ ] Build all targets and publish a draft PR based on Stack122.
