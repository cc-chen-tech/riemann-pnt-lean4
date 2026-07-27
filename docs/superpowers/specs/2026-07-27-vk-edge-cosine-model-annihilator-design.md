# VK-edge Cosine-Model Annihilator Design

## Goal

Build and audit a symmetric finite-difference detector that:

1. annihilates one prescribed cosine frequency exactly;
2. has an exact three-scale expression on the normalized PNT error;
3. transfers positive detector energy on an inner interval to a pointwise
   lower bound for the formal psi-minus-model residual on an expanded
   interval.

The cosine model uses zeta-derived parameters, but this branch deliberately
does not identify it with an actual explicit-formula zero term.

## Detector

```text
D_(h,gamma) F(y)
  = F(y+h) - 2 cos(gamma h) F(y) + F(y-h).
```

For `P(y) = -2m cos(lambda y - phase)`:

```text
D_(h,gamma) P(y)
  = 2 (cos(lambda h) - cos(gamma h)) P(y).
```

This gives exact annihilation at `lambda = gamma` and records the collision
condition for other frequencies.

## Model specialization

The parent module defines

```text
normalizedCosineModelPair rho
normalizedPsiModelResidual rho
```

with the second definition equal to normalized PNT error minus the first.
The detector therefore acts on the formal residual after annihilating the
model. This is algebraically exact, but it is not an explicit-formula
identification.

## Inner-to-outer endpoint

The required review gate is:

```text
0 < integral_[a,b] |D F|^2
------------------------------------------------------
exists z in [a-|h|, b+|h|],
  F(z)^2 > integral_[a,b] |D F|^2 / (72 * (b-a)).
```

The proof uses explicit inclusion of `y+h`, `y`, and `y-h` in the expanded
interval and the pointwise estimate

```text
|D F|^2 <= 12(F(y+h)^2 + F(y)^2 + F(y-h)^2).
```

It is then specialized to `normalizedPsiModelResidual`.

## Files

- `PrimeNumberTheorem/VKEdgeCosineModelAnnihilator.lean`
- `Test/VKEdgeCosineModelAnnihilatorContract.lean`
- `Test/VKEdgeCosineModelAnnihilatorAxiomAudit.lean`
- `docs/research/vk-edge-cosine-model-annihilator-audit.md`
- `lakefile.lean`
- `scripts/check_axiom_allowlist.py`

## Acceptance

- Every public theorem has a full exact-type contract.
- Every public theorem is in the central axiom allowlist.
- The PR-specific audit reports only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Focused build, baseline verification, forbidden-term scan, and
  `git diff --check` pass.

## Boundary

Success is a reusable cosine-model detector plus a genuine inner-to-outer
pointwise transfer. It is not a proof of positive detector energy, an
explicit-formula decomposition, another zeta zero, a Carlson contradiction,
an unconditional PNT oscillation theorem, or RH.
