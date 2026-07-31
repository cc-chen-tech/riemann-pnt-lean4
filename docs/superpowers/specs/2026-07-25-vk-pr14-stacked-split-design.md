# VK PR #14 Stacked Split Design

## Goal

Replace the 210-commit Vinogradov--Korobov umbrella PR with three stacked,
reviewable draft PRs while preserving the active research branch and its dirty
worktree.

## Frozen Source

The split uses the committed remote snapshot ending at `54e9e00`.
Uncommitted files in `.worktrees/vinogradov-korobov` are not part of the split
and must not be modified, moved, stashed, or deleted.

The original history diverged from `main` at
`638735b2c78de817ea9315d086ba039fe1eea1b3`.

## Stack

### Layer A: Exponential sums and zeta bridges

- Source range: `638735b..cb86b99`
- Branch: `agent/vk-exponential-zeta-core`
- Base: `main`
- Scope: finite exponential sums, van der Corput and Kusmin--Landau bounds,
  recursive A-process estimates, Dirichlet blocks, zeta-growth interfaces,
  zero-repulsion interfaces, and Richert scaling.

### Layer B: Prime-power moments and conditioning

- Source range: `cb86b99..f1c0305`
- Branch: `agent/vk-prime-power-moments`
- Base: `agent/vk-exponential-zeta-core`
- Scope: finite Vinogradov moments, Jacobian and Hensel lifting, prime-power
  fibers, singular/nonsingular strata, weighted conditioning, translated
  systems, and mixed-congruence extraction.

### Layer C: Mixed moments and tail recurrences

- Source range: `f1c0305..54e9e00`
- Branch: `agent/vk-mixed-tail-recurrence`
- Base: `agent/vk-prime-power-moments`
- Scope: mixed-moment recurrences, residual tails, complete-block and
  arbitrary-interval savings, terminal-tail obstruction theorems, and the
  coupled recurrence.

## Construction

Each layer is reconstructed as the net tree change of its frozen source range,
not by rewriting or force-pushing the active research branch. Layer A is
applied to current `origin/main`; Layers B and C are applied to the preceding
new layer. This produces one focused integration commit per layer while the
original 210-commit history remains reachable on
`feat/vinogradov-korobov-exponential-sums`.

The existing PR #14 remains untouched until all three replacement branches are
pushed and their draft PRs exist. It is then closed as superseded, with links
to the replacement stack. Its branch is not deleted.

## Validation

For every layer:

1. `git diff --check` must pass.
2. Added Lean sources must contain no `sorry`, `admit`, or project `axiom`.
3. The layer-specific contract must build.
4. The cumulative `Test.VinogradovKorobovAxiomAudit` target must build.
5. The worktree must be clean before push.

The PR descriptions must state that the VK zero-free region, the `3/5` PNT
remainder, and RH are not proved.

## Failure Handling

If applying a frozen range conflicts with current `main`, resolve only files
whose final content is determined by combining current mainline registrations
with the frozen layer registrations. Do not discard current mainline targets.

If a layer fails validation, keep it local and leave PR #14 open. Do not push
or retarget later layers until the failure is resolved.
