# Local Proof DAG Coordination Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a repository-local, read-only-by-default DAG manifest and status view for coordinating independent proof agents.

**Architecture:** Keep `proof-dag.yaml` as the canonical graph and generate `DAG.md` plus status output from it. Store agent protocol and append-only run records separately so agents can coordinate without editing the same state document concurrently.

**Tech Stack:** YAML-like manifest parsed by a dependency-free shell/awk validator, Markdown, Mermaid, Git, Lean project paths.

**Spec:** `docs/superpowers/specs/2026-09-06-local-proof-dag-coordination-design.md`

## Global Constraints

- Read-only by default: no branch switching, worktree cleanup, merge, push, or automatic Lean build.
- `proof-dag.yaml` is the only canonical state source.
- A node may be `verified` only with named evidence and an acceptance command.
- A node is claimable only when all dependencies are `verified`.
- Preserve existing dirty worktrees and active processes.

---

### Task 1: Add the canonical RH DAG manifest

**Files:**
- Create: `proof-dag.yaml`

**Interfaces:**
- Produces stable node ids, dependency edges, status fields, and acceptance metadata consumed by the validator and generated documentation.

- [ ] **Step 1: Define the manifest schema and graph nodes**

  Add a top-level `version`, `generated_from`, and `nodes` list. Include stable nodes for the main foundation, explicit formula, PNT, Riemann–von Mangoldt, Hardy–Littlewood, Carlson, Conrey, Selberg–Möbius, 14/17, and audit/integration. Use `verified` only for mainline theorem interfaces with source paths and evidence references; use `open` or `blocked` for research gaps.

- [ ] **Step 2: Check node and edge counts manually**

  Run `awk '/^  - id:/{n++} /^    - /{e++} END{print "nodes=" n, "edges=" e}' proof-dag.yaml` and confirm every dependency id appears as a node id.

### Task 2: Add a dependency validator and claimable-node report

**Files:**
- Create: `scripts/dag_status.sh`

**Interfaces:**
- Consumes: `proof-dag.yaml`.
- Produces: validation errors, node/edge counts, and open nodes whose dependencies are all verified.

- [ ] **Step 1: Implement strict structural checks**

  Validate ids, statuses, dependency references, self-edges, and duplicate ids using POSIX shell and awk. Exit nonzero on malformed state.

- [ ] **Step 2: Implement claimable-node output**

  Print each `open` node with all dependencies verified, and separately list `blocked` and `claimed` nodes with owners.

- [ ] **Step 3: Run the validator**

  Run `scripts/dag_status.sh proof-dag.yaml`; expected result is a zero exit code and a non-empty report of claimable research nodes.

### Task 3: Generate the human-readable DAG view

**Files:**
- Create: `DAG.md`
- Modify: `scripts/dag_status.sh`

**Interfaces:**
- Consumes: validated `proof-dag.yaml`.
- Produces: Mermaid graph with node status, owner, worktree, and dependency edges.

- [ ] **Step 1: Add deterministic Mermaid generation**

  Generate nodes in manifest order, sanitize labels for Mermaid, and emit one edge per dependency. Use status classes for open, claimed, blocked, and verified.

- [ ] **Step 2: Add operating instructions and snapshot metadata**

  Put the generated graph, node counts, and a warning that branch/worktree names are execution metadata into `DAG.md`.

- [ ] **Step 3: Verify graph consistency**

  Run `scripts/dag_status.sh --write DAG.md proof-dag.yaml`; then compare the reported node/edge counts with the generated graph.

### Task 4: Document the multi-agent protocol

**Files:**
- Create: `agents/README.md`
- Create: `agents/runs/.gitkeep`

**Interfaces:**
- Documents the claim, work, evidence, and handoff protocol used by independent conversations.

- [ ] **Step 1: Document agent startup**

  Require agents to read `proof-dag.yaml`, `DAG.md`, and the current Git/worktree state before claiming a node.

- [ ] **Step 2: Document safe claiming and evidence**

  Define owner/worktree fields, collision handling, acceptance evidence, and the rule that only the node owner records a status transition.

- [ ] **Step 3: Add a run-record template**

  Provide a Markdown template under `agents/README.md` for append-only records in `agents/runs/`.

### Task 5: Verify the coordination layer

**Files:**
- Test: `proof-dag.yaml`, `DAG.md`, `scripts/dag_status.sh`, `agents/README.md`

- [ ] **Step 1: Run shell syntax checks**

  Run `sh -n scripts/dag_status.sh`; expected result is exit code 0.

- [ ] **Step 2: Run the DAG validator and generator**

  Run `scripts/dag_status.sh --write DAG.md proof-dag.yaml`; expected result is exit code 0 and a deterministic `DAG.md`.

- [ ] **Step 3: Inspect the final diff**

  Run `git diff --check` and `git status --short`; expected result is no whitespace errors and only the new coordination files.

- [ ] **Step 4: Commit the isolated implementation**

  Run `git add proof-dag.yaml DAG.md scripts/dag_status.sh agents/README.md agents/runs/.gitkeep docs/superpowers/specs/2026-09-06-local-proof-dag-coordination-design.md docs/superpowers/plans/2026-09-06-local-proof-dag-coordination-plan.md && git commit -m "feat: add local proof DAG coordination"`.
