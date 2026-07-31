# Zero-Free Envelope for the Running Boundary Design

## Objective

Convert a pointwise zero-free envelope for visible zeta zeros into the
logarithmic decay condition required by Stack 117.

## Envelope

For a height schedule `H` and gap `gap : Nat -> Real`, require

```text
rho in positiveNontrivialZerosFinset(H(m))
  -> rho.re <= 1 - gap(m).
```

Assume `gap` is antitone, so `1-gap(m)` is a monotone upper envelope.

## Running maximum and effective gap

The canonical running boundary also contains the artificial fixed anchor
`beta0`.  Therefore the honest bound is

```text
runningBoundary(m) <= max beta0 (1-gap(m)).
```

Its distance from one is

```text
min (1-beta0) (gap(m)).
```

This minimum, not `gap(m)` alone, is the exact decay budget.  If

```text
min(1-beta0,gap(m)) * log m -> infinity,
```

then the Stack 117 zero-free logarithmic condition follows.

## Final transfer

Specialize the envelope theorem to the sigma-only canonical height and anchor,
then apply Stack 117.  The result gives actual relative PNT decay and preserves
the conditional signed-Omega witnesses.

## Claim boundary

No concrete VK-edge formula is proved here; such a theorem only needs to supply
the envelope, antitonicity, and effective-gap growth.  Signed anti-cancellation
remains external.  No unconditional Omega theorem or RH claim is made.

## Verification

Compile implementation, contract, and axiom audit sequentially.  Only the
standard `propext`, `Classical.choice`, and `Quot.sound` axioms are allowed.
