# Canonical Good-Height Moving Unified Transfer Design

## Objective

Specialize the Stack 112 variable-boundary upper/signed-Omega theorem to the
repository's canonical selected good-height schedule.  The specialization must
remove the external height upper bound, cofinality proof, and explicit-formula
remainder certificate without changing the moving zero package or weakening its
exact variable-exponent scales.

## Chosen approach

Reuse
`actualDynamicBoundaryCanonicalSelectedGoodHeight_spec` at the fixed lower
anchor `beta0`.  Its three conclusions provide exactly the Stack 112 inputs

- eventual `H(m) <= m^alpha`;
- `H(m) -> infinity`;
- `ActualSelectedHeightNaturalPointRemainderCertificate beta0 H`.

Instantiate
`actualMonotoneVariableBoundaryUnifiedUpperSignedOmega` with
`H = actualDynamicBoundaryCanonicalSelectedGoodHeight alpha` and pass through
all remaining density, moving-boundary, and sign-witness assumptions unchanged.

## Public interface

Add one theorem:

`actualMonotoneVariableBoundaryCanonicalGoodHeightUnifiedUpperSignedOmega`.

Its conclusion has two parts for the same canonical moving package:

1. an eventual relative PNT upper bound at
   `variableBoundaryTargetAmplitude beta m = m^(beta(m)-1)`;
2. conditional positive and negative unnormalized PNT witnesses at
   `(c - loss) * x^(beta(x))`.

## Explicit remaining assumptions

The theorem deliberately retains:

- an eventual fixed lower anchor `beta0 <= beta(m)`;
- monotonicity of the sampled moving exponent;
- the indexed visible right-edge property;
- the fixed real-zero strict gap;
- the Carlson strip and margin inequalities;
- independent positive and negative main-term witnesses.

These are not hidden behind a new structure.  In particular, this stack does
not construct a maximum-real-part boundary and does not prove anti-cancellation.

## Ownership and claim boundary

Only `ZeroDensityLayerBudget*` modules, matching contract/audit files, and this
task's documents are in scope.  The protected complementary-bound module and
Sharp/VK-edge modules are neither imported for new implementation facts nor
modified.

The result is a conditional transfer specialization.  It is not an
unconditional Omega theorem and does not imply RH.

## Verification

Compile the implementation, contract, and axiom-audit targets directly with the
existing overlay.  The audit must report no axioms beyond `propext`,
`Classical.choice`, and `Quot.sound`.
