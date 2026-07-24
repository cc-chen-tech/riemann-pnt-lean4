# Dynamic Zero Transfer Design

## Purpose

Build a machine-checked transfer layer that turns three kinds of analytic
input into explicit conclusions about prime-number-theorem error terms:

1. a zero-free boundary,
2. a zero-density bound,
3. a truncated explicit-formula kernel estimate.

The same layer must support both directions:

- upper bounds obtained by controlling every zero layer and the truncation
  remainder;
- lower bounds obtained from a nonzero rightmost zero package and a
  mean-square anti-cancellation argument.

The contribution intended to go beyond a fixed-height wrapper is the explicit
finite layer certificate. It records how a dynamic height `T x`, real-part
strips, zero-density counts, kernel weights, and truncation errors combine into
one auditable cost. The formal theorem will not claim a new numerical
zero-density exponent unless that exponent is supplied and proved separately.

## Existing Inputs

The design composes the following established project results.

- `PrimeNumberTheorem/PintzEnvelope.lean` supplies the Pintz envelope-growth
  mechanism.
- `PrimeNumberTheorem/ZeroForcedOscillation.lean` supplies a zero-package
  mean-square lower bound.
- `PrimeNumberTheorem/CarlsonAsymptotic.lean` supplies the Carlson
  zero-density input.
- `PrimeNumberTheorem/ZeroForcedOscillationComplementaryBound.lean` supplies
  the gap between the maximal-real-part package and its fixed-height
  complement.
- `PrimeNumberTheorem/ExplicitFormulaTruncated.lean` supplies the truncated
  explicit formula and its compact-height remainder structure.
- `PrimeNumberTheorem/ZeroDensityCount.lean` supplies finite zero sets and
  zero-counting notation.

The implementation must reuse these theorem statements. It must not duplicate
their proofs or silently strengthen their hypotheses.

## Scope

This feature has four coupled deliverables.

### 1. Finite real-part layering

For each evaluation point `x`, choose:

- a truncation height `T x`;
- a finite increasing sequence of real-part cutoffs;
- the zero finset below `T x`.

Assign every zero in the controlled tail to exactly one half-open real-part
strip. Prove disjointness, coverage, and the identity that rewrites the full
finite sum as a sum over strips.

### 2. Layered density-to-kernel budget

Each strip has:

- an occupancy bound derived from zero-density counts at its left endpoint;
- a uniform upper bound for the explicit-formula kernel on that strip;
- a cost equal to occupancy times kernel weight.

Prove that the norm of the zero-tail contribution is bounded by the sum of
these strip costs. The theorem must accept an abstract zero-density majorant;
Carlson is then supplied as a concrete adapter rather than built into the
combinatorial lemma.

### 3. Dynamic height and upper transfer

Define the total cost at `(x, T)` as:

- the layered zero-tail cost;
- the explicit-formula truncation remainder;
- any compact low-height or boundary contribution not covered by density.

A height schedule `T : Real -> Real` is admissible when it satisfies all
height side conditions required by the imported theorems. The upper-transfer
theorem specializes the total-cost theorem to `T x`.

Optimality is expressed as a certificate, not as noncomputable global
minimization:

```text
IsOptimalHeight cost admissible T x :=
  admissible x (T x) and
  for every U, admissible x U -> cost x (T x) <= cost x U.
```

This keeps the theorem explicit and allows later papers to provide analytic or
computable choices of `T x`. A weaker constant-factor certificate may be added
only if an existing application needs it.

### 4. Rightmost-cluster anti-cancellation and lower transfer

Represent the finite maximal-real-part zero package as a trigonometric
polynomial with nonzero coefficient energy. Reuse the existing mean-square
lower bound to prove that the package cannot remain uniformly small on every
large averaging interval. Combine that witness scale with the complementary
package bound and the explicit-formula remainder.

The first implementation target is an unsigned `Omega` conclusion: existence
of arbitrarily large witness scales with a quantitative absolute-value lower
bound. An `Omega_plus_minus` conclusion is exposed only through a separate
sign-balance hypothesis; it must not be inferred from mean square alone.

## Architecture

The implementation is split into focused modules.

### `ZeroDensityLayerBudget.lean`

This module owns finite strip geometry and the density-to-weighted-sum
inequality. It is independent of the PNT error term and depends only on the
finite zero representation, real-part cutoffs, and norm estimates.

Primary public concepts:

- `RealPartLayering`;
- `zeroLayer`;
- `LayerOccupancyBound`;
- `LayerKernelBound`;
- `layerCost`;
- `layeredTailBudget`;
- the partition and weighted-tail theorems.

### `DynamicExplicitFormulaUpper.lean`

This module adapts the abstract layered budget to the project's truncated
explicit formula. It owns:

- `AdmissibleHeight`;
- `DynamicHeightSchedule`;
- `explicitFormulaCost`;
- `IsOptimalHeight`;
- the dynamic upper-transfer theorem;
- the Carlson adapter theorem.

The generic upper theorem must remain usable with future zero-density inputs,
including bounds stronger than Carlson near the Vinogradov-Korobov boundary.

### `RightmostClusterAntiCancellation.lean`

This module packages the finite rightmost cluster and converts coefficient
energy plus the existing mean-square theorem into witness scales. It owns the
unsigned anti-cancellation result and a hypothesis-explicit signed variant.

### `ZeroForcingUnifiedTransfer.lean`

This is the public facade. It imports the three focused modules and states:

- a dynamic zero-free/density upper bound;
- a dynamic zero-forcing lower bound;
- a paired transfer theorem returning both conclusions when both sets of
  hypotheses are available.

The current skeleton in this file is replaced incrementally. A theorem that
merely substitutes `T x` into a fixed-height theorem is retained only as a
compatibility lemma and is not presented as the main result.

## Data Flow

For the upper direction:

```text
zero-free boundary
  + zero-density majorant
  + kernel strip bounds
  + admissible T(x)
    -> finite strip occupancy bounds
    -> layered zero-tail budget
    -> explicit-formula total cost
    -> PNT error upper bound at x
```

For the lower direction:

```text
rightmost finite zero cluster
  + nonzero coefficient energy
  + mean-square lower bound
    -> a large witness scale
  + complementary-layer budget
  + explicit-formula remainder budget
    -> PNT error absolute-value lower bound
```

The paired theorem shares the height schedule and explicit-kernel assumptions
but keeps upper and lower hypotheses logically separate.

## Hypothesis Discipline

Every public theorem must expose the following distinctions.

- A zero-free region controls which strips can be nonempty; it is not itself a
  zero-density estimate.
- A zero-density estimate controls occupancy; it does not imply a rightmost
  zero exists.
- The anti-cancellation theorem requires nonzero coefficient energy.
- An unsigned `Omega` statement does not imply `Omega_plus_minus`.
- A dynamic-height certificate selects or compares truncation heights; it does
  not prove a numerical optimum without a supplied analytic comparison.
- No result in this feature is described as RH, an RH criterion, or a proof of
  the Vinogradov-Korobov boundary.

## Degenerate Cases

The interfaces must handle these cases explicitly.

- Empty cutoff sequences are rejected by the `RealPartLayering` validity
  predicate.
- Empty zero layers contribute zero cost.
- Repeated cutoffs are rejected by strict monotonicity.
- Zeros on a strip boundary use a single documented half-open convention.
- A zero cluster with zero coefficient energy yields no lower-bound witness.
- Heights below imported theorem thresholds are inadmissible.
- If no optimal-height certificate is available, the generic bound at any
  admissible `T x` remains usable.

## Verification Strategy

Lean contract examples serve as theorem-level tests.

- A two-strip synthetic finset checks exact partition and no double counting.
- A constant kernel bound checks that the layered cost reduces to
  `cardinality * weight`.
- An empty tail checks zero cost.
- A synthetic admissible cost checks specialization to `T x` and the
  `IsOptimalHeight` comparison theorem.
- A nonzero one-frequency cluster checks the unsigned anti-cancellation
  interface.
- A contract importing the facade checks that both transfer directions can be
  instantiated without exposing internal layer definitions.

Verification is staged:

1. focused builds of each new module;
2. focused builds of the contract examples;
3. `#print axioms` for the public transfer theorems;
4. a `sorry` scan limited to changed files;
5. the project aggregate build after focused checks pass.

Any pre-existing axioms in imported analytic results must be reported
separately from new axioms introduced by this feature.

## Delivery Boundary

The feature is complete when:

- the layer partition and density-to-kernel budget are proved;
- a concrete Carlson adapter feeds that budget;
- an admissible dynamic schedule yields an explicit upper bound;
- a nonzero rightmost cluster yields an unsigned witness-scale lower bound;
- the public facade states the paired theorem;
- all public results pass the focused build and axiom audit.

The following are subsequent research projects, not hidden completion
requirements:

- deriving a new best numerical PNT exponent from the framework;
- proving sign balance sufficient for an unconditional `Omega_plus_minus`
  theorem in every target normalization;
- formalizing the full 2024-2025 literature comparison;
- replacing certificate-based height choice by a general computable optimizer.
