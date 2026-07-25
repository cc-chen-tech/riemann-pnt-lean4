# Exceptional Zero Amplification Integration Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Integrate the half-isolated, zero-density amplification, and VK-edge theorem packages, prove the concrete downstream composition to Carlson, and attempt either a zeta-derived averaged propagation theorem or a strict no-go theorem.

**Architecture:** A dedicated integration branch serially merges the three complete research branches so their dependency histories remain intact. A small integration module connects existing endpoints without introducing assumed classes or structures. A separate experiment module then attempts averaged detector propagation; if existing analytic inputs cannot prove it, an explicit finite symmetric model proves the precise no-go result.

**Tech Stack:** Lean 4, Mathlib, Lake, Git worktrees.

## Global Constraints

- Work only in `.worktrees/exceptional-zero-amplification-integration`.
- Keep the three source branches unchanged.
- Run at most one `lake` or `lean` process at a time.
- Do not run aggregate `lake build`.
- Do not add `axiom`, `sorry`, or `admit`.
- A new interface, `Prop`, class, structure field, or assumed propagation hypothesis does not satisfy Gate C.
- Do not state or imply that this project proves RH.

---

### Task 1: Merge the three verified source branches

**Files:**
- Merge: all tracked files from `research/half-isolated-zero-dichotomy`
- Merge: all tracked files from `research/zero-density-amplification-audit`
- Merge: all tracked files from `research/vk-edge-conditional-package`
- Verify: `PrimeNumberTheorem/HalfIsolatedZeroDichotomy/Contract.lean`
- Verify: `PrimeNumberTheorem/ZeroDensityAmplificationAuditIterationExpansionContract.lean`
- Verify: `PrimeNumberTheorem/VKEdgeConditionalPackageContract.lean`

**Interfaces:**
- Consumes: the three branch tips `e9291cb`, `2d1919d`, and `da196a2`
- Produces: one branch containing all three theorem packages and their original histories

- [ ] **Step 1: Merge the half-isolated branch**

```bash
git merge --no-ff --no-edit research/half-isolated-zero-dichotomy
```

Expected: a merge commit containing `halfIsolatedDetectorClusterEndpoint`,
`halfIsolatedDirectedIteration_exponential`, and the equal-imaginary-part
stall theorem.

- [ ] **Step 2: Compile the half-isolated contract**

```bash
lake build PrimeNumberTheorem.HalfIsolatedZeroDichotomy.Contract
```

Expected: `Build completed successfully`.

- [ ] **Step 3: Merge the density branch**

```bash
git merge --no-ff --no-edit research/zero-density-amplification-audit
```

Expected: a merge commit containing
`iterativeWindowLayer_to_carlson_contradiction` and the shared-neighbor
counterexample.

- [ ] **Step 4: Compile the density contract**

```bash
lake build PrimeNumberTheorem.ZeroDensityAmplificationAuditIterationExpansionContract
```

Expected: `Build completed successfully`.

- [ ] **Step 5: Merge the VK-edge branch**

```bash
git merge --no-ff --no-edit research/vk-edge-conditional-package
```

Expected: a merge commit containing the clustered spectral bridge, zeta
symmetry blockers, and window monotonicity theorem.

- [ ] **Step 6: Compile the VK-edge contract**

```bash
lake build PrimeNumberTheorem.VKEdgeConditionalPackageContract
```

Expected: `Build completed successfully`.

- [ ] **Step 7: Record the integrated branch state**

```bash
git status --short --branch
git log -4 --oneline
```

Expected: a clean integration worktree whose recent history contains three
merge commits.

### Task 2: Prove the concrete downstream composition

**Files:**
- Create: `PrimeNumberTheorem/ExceptionalZeroAmplificationIntegration.lean`
- Create: `PrimeNumberTheorem/ExceptionalZeroAmplificationContract.lean`

**Interfaces:**
- Consumes: `halfIsolatedDirectedIteration_exponential`, `iterativeWindowLayer_qpow_lowerBound_with_subcertificate`, and `iterativeWindowLayer_to_carlson_contradiction`
- Produces: `exceptionalZeroAmplification_to_carlson_of_expandingLayers`

- [ ] **Step 1: Expose the exact imported signatures**

Create `/tmp/exceptional_zero_checks.lean`:

```lean
import PrimeNumberTheorem.HalfIsolatedZeroDichotomy.Contract
import PrimeNumberTheorem.ZeroDensityAmplificationAuditIterationExpansionContract
import PrimeNumberTheorem.VKEdgeConditionalPackageContract

#check halfIsolatedDirectedIteration_exponential
#check iterativeWindowLayer_qpow_lowerBound_with_subcertificate
#check iterativeWindowLayer_to_carlson_contradiction
#check halfIsolatedDirectedIteration_stall_under_equal_im_topLayer
#check halfIsolatedDirectedGrowth_no_new_from_zeta_symmetry
```

Run:

```bash
lake env lean /tmp/exceptional_zero_checks.lean
```

Expected: all declarations resolve and Lean prints their complete types.

- [ ] **Step 2: Write a failing integration contract**

Create `PrimeNumberTheorem/ExceptionalZeroAmplificationContract.lean`:

```lean
import PrimeNumberTheorem.ExceptionalZeroAmplificationIntegration

#check exceptionalZeroAmplification_to_carlson_of_expandingLayers
```

Run:

```bash
lake env lean PrimeNumberTheorem/ExceptionalZeroAmplificationContract.lean
```

Expected: failure because the integration module and theorem do not yet
exist.

- [ ] **Step 3: Implement the minimal adapter**

Create `PrimeNumberTheorem/ExceptionalZeroAmplificationIntegration.lean`.
Import the three source contracts. Define only the explicit conversion
functions required to turn the half-isolated directed layers into the
`iterativeWindowLayer` data consumed by the density theorem. Prove:

```lean
theorem exceptionalZeroAmplification_to_carlson_of_expandingLayers
```

by applying the existing half-isolated cardinality theorem, constructing the
existing `IterativeWindowLayerCertificate`, and invoking
`iterativeWindowLayer_to_carlson_contradiction`.

The theorem must expose every separation, bounded-overlap, growth-depth, and
Carlson hypothesis as an ordinary theorem argument. It must not introduce a
new class or structure that merely stores the desired conclusion.

- [ ] **Step 4: Compile the integration contract**

```bash
lake build PrimeNumberTheorem.ExceptionalZeroAmplificationContract
```

Expected: `Build completed successfully`.

- [ ] **Step 5: Commit Gate B**

```bash
git add PrimeNumberTheorem/ExceptionalZeroAmplificationIntegration.lean \
  PrimeNumberTheorem/ExceptionalZeroAmplificationContract.lean
git commit -m "feat: integrate exceptional-zero amplification endpoints"
```

### Task 3: Audit concrete averaged-propagation candidates

**Files:**
- Create: `docs/research/exceptional-zero-averaged-propagation-candidates.md`

**Interfaces:**
- Consumes: existing explicit-formula, Dirichlet-polynomial mean-square, detector, and zero-package declarations
- Produces: a ranked list of exact Lean declarations that could prove propagation, with a yes/no type-level compatibility result for each

- [ ] **Step 1: Search only theorem declarations**

```bash
rg -n "theorem .*meanSquare|theorem .*mean_square|theorem .*detector|theorem .*explicitFormula|theorem .*zeroPackage|theorem .*Dirichlet" \
  PrimeNumberTheorem HardyTheorem
```

Expected: a bounded candidate list rather than a repository-wide content
dump.

- [ ] **Step 2: Classify each candidate**

For each candidate, record:

```text
declaration
input scale
output scale
pointwise or averaged
depends on an already assumed zero family?
can select separated windows?
```

Reject any candidate whose conclusion already assumes the required family of
off-line zeros.

- [ ] **Step 3: Select the strongest concrete candidate**

The selected candidate must output an integral, finite sum, or measure lower
bound over a height range. A theorem that is only local at the original zero
is not selected.

- [ ] **Step 4: Commit the candidate audit**

```bash
git add docs/research/exceptional-zero-averaged-propagation-candidates.md
git commit -m "docs: audit averaged exceptional-zero propagation inputs"
```

### Task 4: Attempt the positive averaged-propagation theorem

**Files:**
- Create: `PrimeNumberTheorem/ExceptionalZeroAmplificationExperiment.lean`
- Modify: `PrimeNumberTheorem/ExceptionalZeroAmplificationContract.lean`

**Interfaces:**
- Consumes: the strongest concrete candidate selected in Task 3
- Produces: `offlineZero_to_manySeparatedDetectorWindows` and an instantiation of `exceptionalZeroAmplification_to_carlson_of_expandingLayers`

- [ ] **Step 1: State the concrete target using repository types**

State:

```lean
theorem offlineZero_to_manySeparatedDetectorWindows
```

with an actual zeta-zero input and an output expressed as a `Finset` of
height-window centers. The conclusion must include pairwise disjointness and a
detector or cluster certificate for every center.

- [ ] **Step 2: Attempt the proof from the selected analytic theorem**

The proof must contain no additional argument equivalent to:

```text
there are already many good windows
```

Use the selected mean-square lower bound, a threshold/selection lemma, and the
existing local detector endpoint.

- [ ] **Step 3: Compile the experiment**

```bash
lake build PrimeNumberTheorem.ExceptionalZeroAmplificationExperiment
```

Expected positive exit: `Build completed successfully` with a theorem derived
from concrete existing analytic inputs.

- [ ] **Step 4: Connect the positive endpoint**

Extend `ExceptionalZeroAmplificationContract.lean` with:

```lean
#check offlineZero_to_manySeparatedDetectorWindows
```

and a concrete application of
`exceptionalZeroAmplification_to_carlson_of_expandingLayers`.

- [ ] **Step 5: Commit the positive result**

```bash
git add PrimeNumberTheorem/ExceptionalZeroAmplificationExperiment.lean \
  PrimeNumberTheorem/ExceptionalZeroAmplificationContract.lean
git commit -m "feat: prove averaged exceptional-zero propagation"
```

If Step 2 requires assuming the target conclusion, stop Task 4 without
committing a misleading theorem and execute Task 5.

### Task 5: Prove the strict no-go model if Task 4 fails

**Files:**
- Create: `PrimeNumberTheorem/ExceptionalZeroAmplificationNoGo.lean`
- Modify: `PrimeNumberTheorem/ExceptionalZeroAmplificationContract.lean`

**Interfaces:**
- Consumes: the existing equal-height stall and symmetry-preservation results
- Produces: `currentExceptionalZeroInputs_do_not_force_averagedPropagation`

- [ ] **Step 1: Build an explicit finite symmetric model**

Use a concrete two-point or four-point finite type. Define:

```text
conjugation orbit
monotone height-window packages
local cluster relation
directed next-layer relation
```

so that every currently used symmetry, monotonicity, and local-cluster premise
is proved, while every larger window contains only the original finite orbit.

- [ ] **Step 2: Prove propagation fails**

Prove:

```lean
theorem currentExceptionalZeroInputs_do_not_force_averagedPropagation
```

whose conclusion is a negation of the concrete many-separated-window
conclusion from Task 4.

- [ ] **Step 3: Prove the missing-input boundary**

Prove that adding a concrete averaged lower-mass theorem or a uniformly
bounded-window-overlap theorem excludes the finite model and is sufficient to
construct the expansion certificate consumed by Gate B.

- [ ] **Step 4: Compile the no-go contract**

```bash
lake build PrimeNumberTheorem.ExceptionalZeroAmplificationNoGo \
  PrimeNumberTheorem.ExceptionalZeroAmplificationContract
```

Expected: `Build completed successfully`.

- [ ] **Step 5: Commit the no-go result**

```bash
git add PrimeNumberTheorem/ExceptionalZeroAmplificationNoGo.lean \
  PrimeNumberTheorem/ExceptionalZeroAmplificationContract.lean
git commit -m "theorem: isolate exceptional-zero propagation no-go boundary"
```

### Task 6: Produce the focused evidence bundle

**Files:**
- Create: `PrimeNumberTheorem/ExceptionalZeroAmplificationAxiomAudit.lean`
- Create: `docs/research/exceptional-zero-amplification-audit.md`

**Interfaces:**
- Consumes: Gate B and the positive or no-go Gate C endpoint
- Produces: reproducible compilation, contract, axiom, and placeholder evidence

- [ ] **Step 1: Add axiom prints**

Create `ExceptionalZeroAmplificationAxiomAudit.lean` with `#print axioms` for:

```text
exceptionalZeroAmplification_to_carlson_of_expandingLayers
offlineZero_to_manySeparatedDetectorWindows
```

or, on the no-go path:

```text
currentExceptionalZeroInputs_do_not_force_averagedPropagation
```

- [ ] **Step 2: Run focused builds serially**

```bash
lake build PrimeNumberTheorem.ExceptionalZeroAmplificationContract
lake build PrimeNumberTheorem.ExceptionalZeroAmplificationAxiomAudit
```

Expected: both commands succeed, one after the other.

- [ ] **Step 3: Scan owned files**

```bash
rg -n "\\bsorry\\b|\\badmit\\b|^axiom\\b" \
  PrimeNumberTheorem/ExceptionalZeroAmplification*.lean
```

Expected: no matches.

- [ ] **Step 4: Record the exact mathematical conclusion**

Write `docs/research/exceptional-zero-amplification-audit.md` with:

```text
integrated theorem chain
focused build commands and outputs
#print axioms outputs
positive or no-go Gate C result
remaining unproved zeta-specific statement
explicit statement that RH is not proved
```

- [ ] **Step 5: Commit the evidence bundle**

```bash
git add PrimeNumberTheorem/ExceptionalZeroAmplificationAxiomAudit.lean \
  docs/research/exceptional-zero-amplification-audit.md
git commit -m "audit: certify exceptional-zero amplification experiment"
```

