# Automatic reverse cluster exclusion design

## Goal

Connect target-scale negligibility of the actual relative PNT error to the
same automatic Pintz-Carlson-explicit-formula chain used in stack48.

## Generic incompatibility

For an eventually positive amplitude `A`, if `f = o(A)`, then `f` cannot
have a far witness of size `c * A` for any `c > 0`.

This is the real-domain counterpart of the existing natural-point reverse
lemma.

## Reverse transfer

Assume:

- `2 / 3 < beta < 1`;
- a global positive nontrivial-zero real-part bound below the canonical
  threshold;
- a conjugation-invariant base cluster;
- the actual relative Chebyshev error is negligible relative to
  `x ^ (beta - 1)`;
- every nonempty enlarged visible cluster supplies the natural-point
  target-amplitude witness required by stack48.

Stack48 transfers that cluster witness to a half-amplitude far witness for the
actual PNT error. The generic incompatibility contradicts PNT negligibility,
so the enlarged cluster is empty.

## Boundary

The theorem does not construct the visible-cluster witness. It isolates that
sharp-oscillation input while automating numerical parameters, selected
height, Carlson cap, conjugation, real ordinates, and explicit-formula
remainders.
