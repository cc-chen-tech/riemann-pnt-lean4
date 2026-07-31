# Monotone Variable-Boundary End-to-End Sign Transfer Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace stack109's absorption-or-gap input by monotonicity of the sampled moving boundary.

**Architecture:** Derive absorption-or-gap through stack102 and instantiate stack109 unchanged.

**Tech Stack:** Lean 4, stacks 102 and 109.

- [ ] State the monotone end-to-end theorem.
- [ ] Derive `VariableBoundaryAbsorptionOrGap` automatically.
- [ ] Add contract/audit, compile, and publish a stacked Draft PR.
