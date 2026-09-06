# Local Proof DAG Coordination Design

## Goal

Provide a repository-local coordination layer so independent Codex conversations and agents can share Riemann formalization progress through one auditable DAG without uploading work to Prove2Me.

## Scope

The first version tracks theorem, lemma, audit, and integration nodes; dependency edges; ownership; worktree assignment; status; acceptance commands; and evidence. It generates a human-readable Mermaid view and exposes a read-only status command. It does not orchestrate processes, merge branches, delete worktrees, or claim that a theorem is verified without recorded evidence.

## Architecture

`proof-dag.yaml` is the canonical state file. `DAG.md` is a generated snapshot for humans and agents. `agents/README.md` documents the protocol for claiming and completing nodes, while `scripts/dag_status.sh` validates the graph and prints actionable open nodes. Agent-specific evidence is stored under `agents/runs/` as append-only Markdown records, avoiding concurrent edits to one large log.

Every node has a stable id, a semantic type, a status, dependencies, owner, worktree, source files, acceptance command, and evidence. A node is claimable only when all dependencies are `verified`; a node is `verified` only when its evidence names a successful acceptance command. Existing Git worktrees remain execution contexts, not proof nodes.

## State model

Allowed statuses are `open`, `claimed`, `blocked`, and `verified`. The validator rejects unknown statuses, duplicate ids, missing dependencies, self-dependencies, cycles, claimed nodes without an owner, and verified nodes without evidence. It reports blocked descendants but does not mutate state.

## Initial data

The initial DAG will contain the RH theorem interface, the main verified foundation, the explicit-formula/PNT chain, Hardy–Littlewood, Carlson zero-density, Conrey, Selberg–Möbius, 14/17, and integration/audit nodes. The initial statuses are conservative: only nodes documented as present in the mainline inventory are marked `verified`; open research targets remain `open` or `blocked` with an explicit gap.

## Safety

All scripts are read-only by default. No script switches branches, edits Lean files, runs a long build, cleans worktrees, merges, pushes, or changes ownership automatically. A future agent must work in its assigned worktree and record raw command output or a linked evidence file before changing a node to `verified`.

## Acceptance

The coordination layer is accepted when the YAML parses, the dependency graph is acyclic, every referenced source file exists on the baseline branch, the status script lists currently claimable nodes, and the generated Mermaid graph agrees with the YAML node and edge counts.
