# Automatic reverse finite-height zero-free design

## Goal

Specialize the automatic reverse cluster-exclusion theorem to the concrete
finite set of nontrivial zeta zeros with

`beta <= rho.re` and `|rho.im| <= H`.

## Construction

Use `rightEdgeNontrivialZerosFinset beta H` as the base visible cluster.
Its existing API proves:

- conjugation invariance;
- emptiness is equivalent to `FiniteHeightRightEdgeZeroFree beta H`.

Stack49 proves that the cluster enlarged by all real-ordinate zeros is empty.
Since the right-edge cluster is a subset of that union, it is empty as well.
The existing equivalence then yields the finite-height zero-free conclusion.

## Boundary

The result remains conditional on:

- a global positive nontrivial-zero real-part bound below the canonical
  two-height threshold;
- target-scale negligibility of the actual PNT error;
- a natural-point target-amplitude witness whenever the enlarged right-edge
  cluster is nonempty.

No sharp witness is constructed in this module.
