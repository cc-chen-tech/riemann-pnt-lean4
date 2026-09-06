# Local proof-agent protocol

This directory is the coordination surface for independent proof-agent
conversations. The protocol keeps ownership and handoffs auditable without
making agents share a mutable log.

## Canonical state and safety rules

- `proof-dag.yaml` is the canonical state. `DAG.md` is a generated view; do
  not edit it by hand. Inspect the state with
  `scripts/dag_status.sh proof-dag.yaml`.
- The validator is read-only by default. It does not claim a theorem, assign
  an owner, change a branch, merge work, clean a worktree, or run a long Lean
  build for you.
- A node is `open`, `claimed`, `blocked`, or `verified`. An `open` node is
  claimable only when every dependency is `verified`. A `verified` node must
  have named acceptance evidence in the manifest and in a run record.
- Branch and worktree names identify execution context. They are not proof
  evidence and do not establish theorem status.
- Each run record is a new Markdown file under `agents/runs/`. Existing run
  records are append-only: do not rewrite, delete, or amend one to conceal a
  failed attempt. Link later corrections or follow-ups to the earlier record.

## Startup checklist

Before claiming any node, an agent must:

1. Read the current `proof-dag.yaml` and `DAG.md`.
2. Run `scripts/dag_status.sh proof-dag.yaml` and confirm that the selected
   node is open and that all of its dependencies are verified.
3. Inspect the current Git and worktree state, including the current branch,
   worktree path, and `git status --short`. Preserve unrelated dirty files and
   active work in that worktree.
4. Read the node's `summary`, `source_paths`, `acceptance_command`, and
   `evidence` fields, then state the exact proposition or audit question being
   attempted and what part of the original expression it covers.
5. Create a run record for the attempt before doing substantive work.

Do not claim a node from a stale DAG snapshot. Re-read the manifest immediately
before recording the claim.

## Claiming a node

The node owner is the agent or conversation responsible for the work. The
`owner` field records that stable identifier; the `worktree` field records the
branch/worktree in which the work is being performed. For an open node, the
owner records a claim by changing exactly that node to `status: claimed` and
filling both fields with non-null values. Record the claim in a new run file
with the current commit, worktree path, and timestamp.

Claiming is a coordination change, not evidence that the mathematics is
proved. Keep `proof-dag.yaml` as the only status source and regenerate `DAG.md`
after a validated manifest change:

```sh
scripts/dag_status.sh --write DAG.md proof-dag.yaml
```

Only the node owner may record a status transition for that node. Other agents
may add their own observations or a handoff record, but must not change the
node from `open` to `claimed`, or from `claimed` to `open`, `blocked`, or
`verified`. The owner must retain the run-record trail for every transition.

### Collision handling

Claims are serialized through the canonical manifest, not through conversation
messages. Immediately before editing, re-read the node and check the current
Git/worktree state. If another owner has already claimed it, stop and do not
overwrite their `owner`, `worktree`, or status; choose another claimable node
or leave a non-owning observation. If two claims were prepared concurrently,
the first claim recorded in the canonical history wins. The losing agent must
restore no fields, must not force-push or rewrite history, and must record the
collision and its abandoned work in its own run file. A handoff requires the
new owner to accept it explicitly in a new run record before the old owner
changes the manifest owner.

## Work, evidence, and completion

During work, keep the run record factual and update it with new append-only
records rather than rewriting history. Separate proof evidence from execution
metadata:

- **Work:** name source files, declarations, lemmas, computations, or audit
  checks changed or inspected. State assumptions, unresolved gaps, and the
  proof category (for example, Lean theorem, paper-only audit, finite check,
  or conditional interface).
- **Evidence:** record the exact acceptance command from the manifest, the
  commit or worktree at which it ran, its exit code, and raw output or a stable
  linked evidence file. A passing command is evidence only for the proposition
  and scope it actually tests; a finite computation, an axiom audit, or an
  interface theorem is not silently promoted to a stronger theorem.
- **Completion:** the owner may change a node to `verified` only after the
  acceptance command succeeds and the run record names the resulting evidence.
  The owner may use `blocked` when a concrete missing proposition or external
  dependency prevents progress, and must state that checkpoint. Do not mark a
  node verified because a branch is clean, a process exited, a CI check is
  empty, or a downstream node appears plausible.

After a status change, run the validator, regenerate `DAG.md`, and inspect the
diff. The generated snapshot must agree with the manifest. If the owner cannot
finish, leave a precise handoff rather than changing another node's status.

## Handoff

A handoff transfers unfinished work, not proof status. The outgoing owner adds
a run record containing the current commit, worktree, files inspected, exact
claim being pursued, commands already run, raw results, known gaps, and the
next acceptance checkpoint. The incoming owner first verifies that the
worktree and manifest still match, then records acceptance in a new run file.
Only after that acceptance may the outgoing owner update `owner` and
`worktree`; the incoming owner becomes responsible for subsequent status
transitions. If the handoff is declined or stale, leave the existing status
unchanged and record the reason.

Never use a handoff to convert an unproved result into `verified`. Evidence
must remain attributable to the command, source state, and proposition for
which it was produced.

## Run-record template

Create one file per attempt, for example
`agents/runs/2026-09-06--conrey-kernel-bridge--alice.md`. Use a new file for a
collision, follow-up, or handoff; do not edit an earlier record.

```markdown
# Run: <node-id>

- Date (UTC): <YYYY-MM-DDThh:mm:ssZ>
- Agent / conversation: <owner>
- Phase: claim | work | evidence | handoff | collision
- Manifest status at start: <open|claimed|blocked|verified>
- Branch: <branch-name>
- Worktree: <absolute-path>
- Starting commit: <full-sha>

## Claim and scope

- Proposition or audit question: <exact target>
- Dependencies checked: <node-id: verified, ...>
- Original-expression scope: <what this covers and what remains>

## Work performed

- Source paths / declarations: <paths and names>
- Changes or checks: <brief factual record>
- Proof category: <Lean theorem | paper-only audit | finite check | conditional interface | ...>
- Known gaps or blockers: <none or precise missing proposition>

## Acceptance evidence

- Acceptance command: `<exact command from proof-dag.yaml>`
- Evidence commit: <full-sha>
- Exit code: <integer>
- Raw output or evidence file: <paste concise output or link/path>
- Interpretation and boundary: <what the result establishes; no stronger claim>

## Handoff / status transition

- Requested transition: <none | open -> claimed | claimed -> blocked | claimed -> verified | ...>
- Owner authorization: <why this agent is the node owner>
- Incoming owner acceptance: <not applicable or owner + date + run file>
- Next checkpoint: <exact command or missing proposition>
```

The template is guidance for records; the manifest remains authoritative for
the current status, owner, worktree, and evidence list.
