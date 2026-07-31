# Monotone Variable-Boundary Signed Omega Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Transfer two signed moving-package witnesses through automatic moving zero tails to simultaneous unnormalized PNT witnesses.

**Architecture:** Derive the automatic residual and monotone absorption-or-gap, obtain one eventual error bound, transfer positive and negative natural witnesses separately, then embed and unnormalize both.

**Tech Stack:** Lean 4, stacks 102, 108, signed natural-point transfer, and variable-exponent unnormalization.

- [ ] Derive one automatic residual and eventual absolute-error bound.
- [ ] Transfer positive and negative main witnesses with common coefficient loss.
- [ ] Convert both to real-variable unnormalized witnesses and package them as `HasFarSignedTargetAmplitudeWitnesses`.
- [ ] Add contract/audit and publish a stacked Draft PR.
