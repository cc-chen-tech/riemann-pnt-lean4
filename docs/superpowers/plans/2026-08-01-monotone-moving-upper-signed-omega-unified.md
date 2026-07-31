# Monotone Moving Upper and Signed Omega Unified Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Return a moving-exponent PNT upper bound and conditional signed Omega lower bound from one explicit-formula setup.

**Architecture:** Generalize the package coefficient cap and upper perturbation argument to `beta(m)`, construct the cap pointwise from Carlson mass, then pair the result with stack111.

**Tech Stack:** Lean 4, Carlson coefficient mass, stack108 automatic residual, stack111 signed transfer.

- [ ] Define `VariableBoundaryPackageCoefficientCap` and its automatic Carlson instance.
- [ ] Prove the variable-exponent eventual upper transfer.
- [ ] Pair upper and signed lower conclusions in one theorem.
- [ ] Add contract/audit and publish a Draft PR.
