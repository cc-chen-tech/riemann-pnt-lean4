# Proof DAG

_Generated from proof-dag.yaml by scripts/dag_status.sh; edit the manifest and regenerate this file._

## Snapshot

- Validation: `ok`
- Nodes: `14`
- Dependency edges: `33`
- Status counts: `open=13`, `claimed=0`, `blocked=1`, `verified=0`
- Manifest version: `1`
- Generated from: `docs/superpowers/specs/2026-09-06-local-proof-dag-coordination-design.md`

> Warning: branch and worktree names are execution metadata. They identify the current coordination context; they are not proof evidence or theorem status.

## Operating instructions

1. Treat `proof-dag.yaml` as the canonical state; do not edit this generated snapshot directly.
2. Inspect the current state with `scripts/dag_status.sh proof-dag.yaml`.
3. Regenerate this view after a validated manifest change with `scripts/dag_status.sh --write DAG.md proof-dag.yaml`.
4. An open node is claimable only when every dependency is `verified`; a verified node requires named acceptance evidence.

## Status legend

The node colors correspond to the manifest status: `open`, `claimed`, `blocked`, and `verified`.

## Graph

```mermaid
flowchart TD
    node_main_foundation["main-foundation<br/>status: open<br/>owner: (unassigned)<br/>worktree: (unassigned)<br/>Mainline analytic-number-theory foundation and RH interface"]
    node_explicit_formula["explicit-formula<br/>status: open<br/>owner: (unassigned)<br/>worktree: (unassigned)<br/>Mainline explicit-formula interface for von Mangoldt sums"]
    node_pnt["pnt<br/>status: open<br/>owner: (unassigned)<br/>worktree: (unassigned)<br/>Prime number theorem interface"]
    node_riemann_von_mangoldt["riemann-von-mangoldt<br/>status: open<br/>owner: (unassigned)<br/>worktree: (unassigned)<br/>Riemann–von Mangoldt zero-counting formula"]
    node_hardy_littlewood["hardy-littlewood<br/>status: open<br/>owner: (unassigned)<br/>worktree: (unassigned)<br/>Hardy–Littlewood linear lower bound on critical-line zeros"]
    node_carlson["carlson<br/>status: open<br/>owner: (unassigned)<br/>worktree: (unassigned)<br/>Fixed-sigma Carlson zero-density interface"]
    node_conrey_kernel_bridge["conrey-kernel-bridge<br/>status: open<br/>owner: (unassigned)<br/>worktree: (unassigned)<br/>Conrey kernel and argument-principle bridge work package"]
    node_selberg_lcm_type_ii["selberg-lcm-type-ii<br/>status: open<br/>owner: (unassigned)<br/>worktree: (unassigned)<br/>Selberg LCM main term and Type-II off-diagonal work package"]
    node_carlson_improvement["carlson-improvement<br/>status: open<br/>owner: (unassigned)<br/>worktree: (unassigned)<br/>Carlson zero-density improvement and quantitative margin work package"]
    node_fourteen_seventeenths_projection["fourteen-seventeenths-projection<br/>status: open<br/>owner: (unassigned)<br/>worktree: (unassigned)<br/>14/17 projection and zero-density transfer work package"]
    node_selberg_mobius["selberg-mobius<br/>status: blocked<br/>owner: (unassigned)<br/>worktree: (unassigned)<br/>Selberg–Möbius LCM and varying-level off-diagonal route"]
    node_conrey["conrey<br/>status: open<br/>owner: (unassigned)<br/>worktree: (unassigned)<br/>Genuine Conrey strict simple-zero lower-bound route"]
    node_fourteen_seventeenths["fourteen-seventeenths<br/>status: open<br/>owner: (unassigned)<br/>worktree: (unassigned)<br/>14/17 zero-density target and quantitative closure"]
    node_audit_integration["audit-integration<br/>status: open<br/>owner: (unassigned)<br/>worktree: (unassigned)<br/>Cross-chain audit and integration gate for the RH proof DAG"]
    node_main_foundation --> node_explicit_formula
    node_explicit_formula --> node_pnt
    node_explicit_formula --> node_riemann_von_mangoldt
    node_pnt --> node_riemann_von_mangoldt
    node_main_foundation --> node_hardy_littlewood
    node_pnt --> node_carlson
    node_riemann_von_mangoldt --> node_carlson
    node_hardy_littlewood --> node_conrey_kernel_bridge
    node_carlson --> node_conrey_kernel_bridge
    node_hardy_littlewood --> node_selberg_lcm_type_ii
    node_riemann_von_mangoldt --> node_selberg_lcm_type_ii
    node_pnt --> node_carlson_improvement
    node_riemann_von_mangoldt --> node_carlson_improvement
    node_carlson --> node_fourteen_seventeenths_projection
    node_selberg_lcm_type_ii --> node_selberg_mobius
    node_hardy_littlewood --> node_selberg_mobius
    node_riemann_von_mangoldt --> node_selberg_mobius
    node_conrey_kernel_bridge --> node_conrey
    node_hardy_littlewood --> node_conrey
    node_selberg_mobius --> node_conrey
    node_carlson --> node_conrey
    node_fourteen_seventeenths_projection --> node_fourteen_seventeenths
    node_carlson --> node_fourteen_seventeenths
    node_conrey --> node_fourteen_seventeenths
    node_main_foundation --> node_audit_integration
    node_explicit_formula --> node_audit_integration
    node_pnt --> node_audit_integration
    node_riemann_von_mangoldt --> node_audit_integration
    node_hardy_littlewood --> node_audit_integration
    node_carlson --> node_audit_integration
    node_selberg_mobius --> node_audit_integration
    node_conrey --> node_audit_integration
    node_fourteen_seventeenths --> node_audit_integration

    classDef open fill:#fff2cc,stroke:#bf9000,color:#000;
    classDef claimed fill:#cfe2f3,stroke:#3d85c6,color:#000;
    classDef blocked fill:#f4cccc,stroke:#cc0000,color:#000;
    classDef verified fill:#d9ead3,stroke:#38761d,color:#000;
    class node_main_foundation open;
    class node_explicit_formula open;
    class node_pnt open;
    class node_riemann_von_mangoldt open;
    class node_hardy_littlewood open;
    class node_carlson open;
    class node_conrey_kernel_bridge open;
    class node_selberg_lcm_type_ii open;
    class node_carlson_improvement open;
    class node_fourteen_seventeenths_projection open;
    class node_selberg_mobius blocked;
    class node_conrey open;
    class node_fourteen_seventeenths open;
    class node_audit_integration open;
```
