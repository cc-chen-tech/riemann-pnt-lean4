# Automatic optimal height bridge to the Carlson chain

## Goal

Identify the actual candidate height of the Stack 130 singleton grid with the
classical admissible selected height already used throughout the dyadic
Carlson modules.

## Equality

Both schedules use the same selector and the same base

`pintzCarlsonGoodHeightBase (classicalAdmissibleBalancedRate (theta * b)) x`.

The actual candidate has an early fallback to height eight. Once the raw
height is at least nine, the fallback disappears, so the schedules are exactly
equal. This occurs eventually on real and natural samples.

## Transport

The module transports:

- the finite multiplicity-weighted zero sum;
- `dynamicFullPNTZeroTailNorm`;
- the actual explicit-formula relative remainder;
- `IsSelectedHeightDynamicZeroFree`.

It also supplies a generic theorem that dynamic zero-free predicates are
preserved by eventual equality of height schedules on natural samples.

## Claim boundary

This is an interface bridge. It does not itself improve a Carlson estimate or
prove an Omega theorem, target-amplitude negligibility, or RH.
