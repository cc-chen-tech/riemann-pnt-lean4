# Exceptional-Zero Target Dyadic Gram/Schur Implementation Plan

> **Execution:** Follow test-driven development and verification-before-completion. Keep this branch stacked on Draft PR #265 and open a new Draft PR; do not merge.

**Goal:** Prove the actual-zeta, target-normalized, right-higher,
`S`-relative whole-Gram Schur upper bound for one dyadic ordinate block and
expose the `Re rho > beta` alternative.

**Architecture:** Reuse the existing dynamic packet whole-Gram theorem.
Convert packet mass squares to a local-occupancy factor times the sum of
individual coefficient squares, identify those squares exactly with the
target-weighted reciprocal-square capacity, and specialize the excluded set
to `rightHigherExclusionSet`.  Add a separate real-part dichotomy to obtain an
unweighted corollary only when all surviving zeros satisfy `Re rho <= beta`.

**Tech stack:** Lean 4, Mathlib finite sums and complex norms, existing
Gaussian Schur/dynamic zero-packet APIs, focused contract and axiom-audit
targets.

## Global constraints

- Add no `sorry`, `admit`, new axiom, or conditional Witness interface.
- Reuse `dynamicComplementGaussianMajorantEnergy_le`; do not reprove Schur
  control pair by pair.
- Keep all constants explicit and independent of `S.card`.
- Do not assume `Re rho <= beta`; return a farther-right zero when it fails.
- Do not begin dyadic aggregation, Carlson, smoothing, or two-height transfer
  in this PR.

### Task 1: Lock the public contract in RED

**Files:**

- Create `Test/ExceptionalZeroTargetDyadicGramSchurContract.lean`.
- Modify `lakefile.lean` only as needed to register the focused test target.

- [ ] Declare checks for the dyadic bucket set, packet occupancy, exact
  coefficient-square identity, weighted capacity, whole-Gram bound,
  right-higher specialization, and real-part dichotomy.
- [ ] Build only the contract and record the expected missing-module or
  missing-declaration failure.
- [ ] Commit the failing contract separately.

### Task 2: Prove finite packet occupancy control

**Files:**

- Create `MathlibAux/FinitePacketOccupancy.lean` only if the existing
  `FiberwiseNormSq` API cannot express the required real nonnegative mass
  estimate cleanly.
- Otherwise extend no generic interface and prove the specialization in the
  E2 module.

- [ ] Define a maximum finite-fiber cardinality with value zero on an empty
  index set.
- [ ] Prove every packet cardinality is bounded by that maximum.
- [ ] Prove
  `(sum packet mass)^2 <= Occ * sum packet (mass^2)` for nonnegative masses.
- [ ] Sum over dyadic buckets without introducing `S.card`.
- [ ] Build the focused helper and contract fragment.

### Task 3: Identify target-normalized coefficient squares

**Files:**

- Create `PrimeNumberTheorem/ExceptionalZeroTargetDyadicGramSchur.lean`.

- [ ] Prove the exact general-`a` identity for
  `‖finiteZeroClusterCoefficientAt ... beta a rho‖ ^ 2`.
- [ ] Resolve the `rho = 0` case algebraically; use actual nontrivial-zero
  facts only where needed for reciprocal notation.
- [ ] Define the dyadic target-weighted square capacity over the dynamic
  complement packets.
- [ ] Rewrite the sum of coefficient squares to this capacity.
- [ ] Build the implementation module.

### Task 4: Specialize whole-Gram Schur to one dyadic block

**Files:**

- Modify `PrimeNumberTheorem/ExceptionalZeroTargetDyadicGramSchur.lean`.
- Modify `Test/ExceptionalZeroTargetDyadicGramSchurContract.lean`.

- [ ] Apply `dynamicComplementGaussianMajorantEnergy_le` to
  `Finset.Icc (2^k) (2^(k+1)-1)`.
- [ ] Bound the packet coefficient-mass squares by local occupancy times the
  target-weighted square capacity.
- [ ] Prove the sharper internal `Occ` estimate and the public
  `(1 + Occ)` theorem.
- [ ] Specialize the excluded set to
  `rightHigherExclusionSet S Told sigma T`.
- [ ] Confirm theorem statements contain no `S.card`.
- [ ] Build implementation and contract.

### Task 5: Add the explicit real-part dichotomy

**Files:**

- Modify `PrimeNumberTheorem/ExceptionalZeroTargetDyadicGramSchur.lean`.
- Modify `Test/ExceptionalZeroTargetDyadicGramSchurContract.lean`.

- [ ] Split on existence of a surviving dyadic-block zero with
  `beta < rho.re`.
- [ ] In the positive branch return actual-zero membership, dyadic height,
  `rho ∉ S`, the old-height inequality, and the strip facts derived from
  `directedWitness_of_not_mem_rightHigherExclusionSet`.
- [ ] In the negative branch prove `rho.re <= beta` for every surviving zero.
- [ ] For `0 <= a`, prove each exponential weight is at most one and derive
  the unweighted square-capacity upper bound.
- [ ] Combine this with the Gram theorem into the requested dichotomy.
- [ ] Build implementation and contract.

### Task 6: Audit, review, and publish the Draft PR

**Files:**

- Create `Test/ExceptionalZeroTargetDyadicGramSchurAxiomAudit.lean`.
- Modify the central audit/allowlist registration only if repository policy
  requires it.

- [ ] Build serially in this worktree: implementation, contract, axiom audit.
- [ ] Run forbidden-declaration and accidental-axiom scans.
- [ ] Inspect the diff against `3aaf0d80` and confirm scope/claim boundaries.
- [ ] Commit intentionally, push the branch, and open a Draft PR based on
  `codex/exceptional-zero-dyadic-direct-l2` / PR #265.
- [ ] Report exact verification commands and leave all PRs unmerged.
