# Main Documentation Status Sync Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make the public documentation agree with the theorem-level results currently merged into `main`, while keeping Draft PR #19 and other research targets outside the verified main surface.

**Architecture:** First update the repository-wide status documents on a branch based on `origin/main`. After that documentation is merged, rebase Draft PR #19 onto the updated `main`, retain only its Ford-specific documentation, and retarget it to `main`.

**Tech Stack:** Markdown, Git, GitHub pull requests, Lean/Lake contract and axiom-audit targets.

## Global Constraints

- Chinese is the primary README language; English is a supporting summary.
- Separate proved Lean theorems, reusable interfaces, and `def ... : Prop` targets.
- Do not claim RH, the Vinogradov--Korobov zero-free region, Selberg's `T log T` result, or Ford's Lemma 5.1.
- Preserve all dirty worktrees and untracked files.
- Base public `main` claims on focused contracts and axiom audits, not branch activity.

---

### Task 1: Synchronize the public main status

**Files:**
- Modify: `README.md`
- Modify: `lakefile.lean`
- Modify: `docs/formal-theorem-inventory.md`
- Modify: `docs/missing-chains-index.md`
- Modify: `docs/current-target-status.json`
- Modify: `PUBLISHING.md`
- Modify: `scripts/target_inventory.py`
- Modify: `scripts/update-target-status.py`

**Interfaces:**
- Consumes: theorem declarations and tests already present on `origin/main`.
- Produces: a consistent public description of merged Hardy--Littlewood, Pintz envelope, strict `pi/2` oscillation, and VK infrastructure.

- [x] **Step 1: Promote merged theorem-level results in README**

Add Hardy--Littlewood, Pintz envelope, and strict `pi/2` PNT oscillation to the verified-main sections. Describe PR #16--#18 as merged VK infrastructure while retaining `vinogradov_korobov_zero_free_region` as an open target.

- [x] **Step 2: Remove stale PR and research-branch statuses**

Remove statements that PR #8, #11, #12, #13, #15, #16, #17, or #18 are still draft, unmerged, or awaiting integration.

- [x] **Step 3: Correct the formal theorem inventory**

List the merged top-level Hardy--Littlewood, Pintz, and strict `pi/2` theorems. Move Hardy--Littlewood out of the open-target summary while retaining Selberg and Conrey.

- [x] **Step 4: Correct the chain-gap and publishing documents**

Mark the Hardy--Littlewood linear lower bound closed, identify Selberg's logarithmic gain as the next critical-line blocker, and describe Ford's short-sum/tent-kernel bridge as the remaining VK endpoint.

- [x] **Step 5: Classify merged VK predicates and regenerate target status**

Classify the normal schedule, solution-membership, moment, and congruence predicates introduced by PR #16--#18 as reusable predicates. Update the critical-line chain summary and regenerate `docs/current-target-status.json`.

Run:

```bash
python3 scripts/update-target-status.py
python3 scripts/list-prop-targets.py
python3 scripts/check-targets-consistent.py
python3 scripts/check-chain-gaps.py
```

Expected: 12 mathematical targets, 5 route interfaces, 46 reusable predicates, and 0 unclassified Prop definitions.

- [x] **Step 6: Validate documentation consistency**

Run:

```bash
rg -n "proved on research branch|still need.*Hardy|Hardy--Littlewood and Selberg.*remain|Hardy--Littlewood.*awaiting integration|PR #11|Draft PR #8|Draft PR #16" \
  README.md docs/formal-theorem-inventory.md docs/missing-chains-index.md PUBLISHING.md
git diff --check
```

Expected: no stale main-status matches and no whitespace errors.

- [x] **Step 7: Build focused contracts and audits**

Register the merged strict-`pi/2` source module, theorem contract, and axiom
audit in the default Lean library so the documented Lake target is real.

Run:

```bash
lake -Kjobs=1 build \
  Test.HardyLittlewoodTheoremContract \
  Test.HardyLittlewoodOddTheoremContract \
  Test.PintzEnvelopeContract \
  Test.VKEdgePiOverTwoAbelPhaseContract \
  Test.VKEdgePiOverTwoAbelPhaseAxiomAudit \
  Test.VinogradovKorobovAxiomAudit
```

Expected: exit code 0. Report the focused nature of this build.

- [ ] **Step 8: Commit and publish the documentation branch**

```bash
git add README.md PUBLISHING.md \
  lakefile.lean \
  docs/formal-theorem-inventory.md \
  docs/missing-chains-index.md \
  docs/current-target-status.json \
  scripts/target_inventory.py \
  scripts/update-target-status.py
git commit -m "docs: synchronize verified main theorem status"
git push -u origin docs/main-status-sync
```

Open a pull request against `main`, review its diff, and merge it only if GitHub reports no conflict.

### Task 2: Normalize Draft PR #19 after the docs merge

**Files:**
- Modify: `README.md` on `agent/vk-ford-incomplete-bridge`
- Optionally create: `docs/research/vk-ford-incomplete-bridge.md`

**Interfaces:**
- Consumes: the newly merged public documentation and PR #19's Ford-specific theorems.
- Produces: a PR against `main` whose documentation discusses only the new Ford layer.

- [ ] **Step 1: Change PR #19 base to `main`**

Retarget the PR after the documentation merge, then merge or rebase the updated `origin/main` into its head branch without rewriting unrelated commits.

- [ ] **Step 2: Keep the README delta narrow**

State that PR #16--#18 are already merged. Describe only the new incomplete moments, double Holder, residue-mass audit, and near-integer count.

- [ ] **Step 3: Preserve the exact claim boundary**

Keep `FordShortSumPrefixBound`, equation (5.4), smooth-support estimates, VK zeta growth, the final VK region, the `3/5` PNT remainder, and RH explicitly unproved.

- [ ] **Step 4: Validate the final PR diff**

Run:

```bash
git diff --check origin/main...HEAD
git diff --name-status origin/main...HEAD
lake -Kjobs=1 build \
  Test.VinogradovKorobovFordDoubleHolderContract \
  Test.VinogradovKorobovFordIncompleteSupportMomentContract \
  Test.VinogradovKorobovFordNearIntegerContract \
  Test.VinogradovKorobovFordShortSumBridgeContract \
  Test.VinogradovKorobovAxiomAudit
```

Expected: only PR #19 files remain in the diff and the focused build exits 0.

- [ ] **Step 5: Push the normalized branch**

Push the updated head branch and confirm PR #19 is mergeable against `main`. Leave it as draft unless its mathematical review and validation gates justify ready-for-review status.
