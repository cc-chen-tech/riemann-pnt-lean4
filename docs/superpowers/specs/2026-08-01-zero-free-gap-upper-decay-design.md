# Zero-Free Gap to Actual PNT Decay Design

## Objective

Close the upper direction of the sigma-only running-boundary transfer.  Convert
a zero-free-region statement about the constructed moving exponent into decay
of its exact target amplitude, then combine that decay with Stack 116's actual
explicit-formula upper bound.

## Zero-free interface

For `beta : Real -> Real`, define

```text
IsNaturalVariableBoundaryZeroFreeDecay beta :=
  Tendsto ((1 - beta(m)) * log m) atTop atTop.
```

At positive natural samples,

```text
m^(beta(m)-1) = exp (-(1-beta(m))*log m).
```

Therefore the zero-free condition implies
`variableBoundaryTargetAmplitude beta m -> 0`.

## Actual PNT transfer

Stack 116 gives eventually

```text
abs(relativeChebyshevPsi0Error m)
  < C * variableBoundaryTargetAmplitude beta m.
```

The right side tends to zero, so squeezing the absolute error gives

```text
relativeChebyshevPsi0Error m -> 0.
```

The final theorem returns this actual PNT decay together with the same
conditional signed unnormalized witnesses already produced by Stack 116.

## Claim boundary

The theorem does not assert that a particular zero-free region satisfies the
log-gap condition; it provides the exact reusable condition such a region must
prove.  Signed anti-cancellation witnesses remain external.  No unconditional
Omega theorem or RH claim is made.

Only `ZeroDensityLayerBudget*`, matching contract/audit files, and task
documents are modified.  Protected complementary-bound and Sharp/VK-edge files
remain untouched.

## Verification

Compile implementation, contract, and axiom audit sequentially with the
existing overlay.  The allowed axioms are `propext`, `Classical.choice`, and
`Quot.sound`.
