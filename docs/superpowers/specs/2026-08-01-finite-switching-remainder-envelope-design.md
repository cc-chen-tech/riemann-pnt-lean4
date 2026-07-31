# Finite-Switching Remainder and Envelope Transfer

## Scope

Stack120 turns the Stack119 certified optimizer into an actual remainder and
visible-zero-envelope height schedule. It adds no new zero-free-region input
and no signed anti-cancellation theorem.

## Finite-switching principle

Let `H_i` be a finite nonempty family of height schedules and let `H` satisfy

```text
forall x, exists i, H x = H_i x.
```

Assume every `H_i` has an
`ActualSelectedHeightNaturalPointRemainderCertificate beta H_i`. At a natural
sample, the normalized absolute remainder for `H` equals one summand in

```text
sum_i |actualRemainder H_i m| / targetAmplitude beta m.
```

Every summand tends to zero, hence the finite sum tends to zero. Positivity of
the target amplitude gives a squeeze proof for `H`. This permits the optimizer
to switch candidates with the scale; no fixed-selector assumption or uniform
rate is inserted.

## Actual good-height candidates

The Stack119 candidate is a fixed positive fallback below the asymptotic range
and equals `selectedUniformGoodHeight` eventually. The existing actual
remainder certificate for `selectedUniformGoodHeight` therefore transfers by
eventual congruence to every regularized candidate.

Combining candidate certificates with optimizer witness recovery gives an
`ActualSelectedHeightNaturalPointRemainderCertificate` for the exact optimized
height schedule.

## Visible-zero envelope

If every candidate schedule satisfies one common
`IsNaturalPositiveZeroFreeEnvelope`, optimizer witness recovery rewrites the
selected finite positive-zero set to the corresponding candidate set at each
natural sample. The optimized schedule inherits the same envelope without a
height comparison or monotonicity assumption.

## Claim boundary

This closes the finite-switching stability gap for the actual remainder and
the visible-zero envelope. A later facade may feed both certificates into the
existing Stack118 upper-transfer theorem. This module does not supply a VK
zero-free function, Carlson data, signed main witnesses, unconditional Omega,
or RH.
