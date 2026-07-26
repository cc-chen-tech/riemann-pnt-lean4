# VK PR #14 Stacked Split Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace PR #14 with three ordered draft PRs reconstructed from a
frozen committed snapshot.

**Architecture:** Apply the net diff of each approved historical range onto
current `main` and then onto the preceding new layer. Preserve the original
branch and dirty worktree; publish one integration commit per layer.

**Tech Stack:** Git, GitHub CLI, Lean 4, Lake.

## Global Constraints

- Never modify, stash, reset, delete, or overwrite the active
  `.worktrees/vinogradov-korobov` dirty worktree.
- Freeze source history at `54e9e00`.
- Keep all three PRs as drafts.
- Do not claim the VK zero-free region, the `3/5` PNT remainder, or RH.

---

### Task 1: Record the split

**Files:**
- Create: `docs/superpowers/specs/2026-07-25-vk-pr14-stacked-split-design.md`
- Create: `docs/superpowers/plans/2026-07-25-vk-pr14-stacked-split.md`

**Interfaces:**
- Consumes: approved stacked-PR design and frozen source SHAs.
- Produces: an auditable split record included in Layer A.

- [ ] **Step 1: Add the design and implementation plan**

Use the exact branch names, source ranges, validation gates, and preservation
rules in this plan.

- [ ] **Step 2: Check the documents**

Run:

```bash
git diff --check
rg -n 'T[B]D|TO[D]O|implement[ ]later|fill[ ]in' \
  docs/superpowers/specs/2026-07-25-vk-pr14-stacked-split-design.md \
  docs/superpowers/plans/2026-07-25-vk-pr14-stacked-split.md
```

Expected: `git diff --check` succeeds and the placeholder scan is empty.

- [ ] **Step 3: Commit**

```bash
git add docs/superpowers/specs/2026-07-25-vk-pr14-stacked-split-design.md \
  docs/superpowers/plans/2026-07-25-vk-pr14-stacked-split.md
git commit -m "docs(vk): record PR 14 stacked split"
```

### Task 2: Build Layer A

**Files:**
- Apply the net source change from `638735b..cb86b99`.

**Interfaces:**
- Consumes: current `origin/main`.
- Produces: `agent/vk-exponential-zeta-core`.

- [ ] **Step 1: Apply the frozen Layer A tree change**

Apply the net diff without rewriting the active research branch. Resolve
`lakefile.lean` by retaining current mainline targets and adding the Layer A
targets.

- [ ] **Step 2: Validate**

Run:

```bash
git diff --check
lake -Kjobs=1 build Test.VinogradovKorobovAProcessBoundsContract
lake -Kjobs=1 build Test.VinogradovKorobovAxiomAudit
```

Expected: all commands exit successfully.

- [ ] **Step 3: Commit and publish**

Commit the Layer A files, push `agent/vk-exponential-zeta-core`, and open a
draft PR targeting `main`.

### Task 3: Build Layer B

**Files:**
- Apply the net source change from `cb86b99..f1c0305`.

**Interfaces:**
- Consumes: `agent/vk-exponential-zeta-core`.
- Produces: `agent/vk-prime-power-moments`.

- [ ] **Step 1: Create Layer B from Layer A**

Create an isolated worktree and apply the frozen Layer B tree change.

- [ ] **Step 2: Validate**

Run:

```bash
git diff --check
lake -Kjobs=1 build Test.VinogradovKorobovMixedConditionedSolutionContract
lake -Kjobs=1 build Test.VinogradovKorobovAxiomAudit
```

Expected: all commands exit successfully.

- [ ] **Step 3: Commit and publish**

Commit the Layer B files, push `agent/vk-prime-power-moments`, and open a draft
PR targeting `agent/vk-exponential-zeta-core`.

### Task 4: Build Layer C

**Files:**
- Apply the net source change from `f1c0305..54e9e00`.

**Interfaces:**
- Consumes: `agent/vk-prime-power-moments`.
- Produces: `agent/vk-mixed-tail-recurrence`.

- [ ] **Step 1: Create Layer C from Layer B**

Create an isolated worktree and apply the frozen Layer C tree change.

- [ ] **Step 2: Validate**

Run:

```bash
git diff --check
lake -Kjobs=1 build Test.VinogradovKorobovCoupledTailRecurrenceContract
lake -Kjobs=1 build Test.VinogradovKorobovAxiomAudit
```

Expected: all commands exit successfully.

- [ ] **Step 3: Commit and publish**

Commit the Layer C files, push `agent/vk-mixed-tail-recurrence`, and open a
draft PR targeting `agent/vk-prime-power-moments`.

### Task 5: Supersede PR #14

**Files:** None.

**Interfaces:**
- Consumes: three published replacement draft PRs.
- Produces: a documented GitHub review topology and a closed umbrella PR.

- [ ] **Step 1: Verify the stack**

Confirm that each PR base/head pair matches the design and that each PR is
draft and conflict-free.

- [ ] **Step 2: Comment on and close PR #14**

Add a comment listing the three replacement PRs in merge order and state that
the original branch remains available. Close PR #14 without deleting its
branch.

- [ ] **Step 3: Report**

Report the three PR URLs, exact merge order, validation evidence, and any
remaining research gaps.
