# Quantitative reverse finite-height zero-free design

## Goal

Replace the little-o PNT hypothesis in stack50 by an explicit eventual
target-amplitude coefficient.

## Quantitative threshold

Stack48 transfers a unit visible-cluster witness to a half-amplitude witness
for the actual relative PNT error. Therefore an eventual bound

`|E(x)| <= q * x ^ (beta - 1)`

is incompatible with a nonempty visible cluster whenever `q < 1 / 2`.

## Construction

1. Prove a real-domain incompatibility theorem for an eventual `q * A` upper
   bound and a far `d * A` witness with `q < d`.
2. Instantiate stack48 with the finite-height right-edge cluster.
3. If its real-ordinate enlargement is nonempty, transfer the conditional
   unit cluster witness to a half-amplitude actual-error witness.
4. Contradict the eventual `q` bound.
5. Project right-edge cluster emptiness and conclude
   `FiniteHeightRightEdgeZeroFree beta H`.

## Boundary

The global real-part bound and the nonempty-cluster witness remain explicit.
The result does not prove RH or construct the sharp witness.

