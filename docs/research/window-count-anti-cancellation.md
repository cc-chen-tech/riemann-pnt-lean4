# Window-count anti-cancellation transfer

## Motivation

The finite coefficient-mass method bounds every extension term absolutely at
every sufficiently large point. The conjugation-aware Carlson barrier shows
that this is too expensive once the seed outside mass reaches `c / 2`.

The replacement interface asks only for one synchronized point in each far
window.

## Finite counting principle

For every threshold `M`, suppose there are finite sets `G` and `B` such that:

- every point of `G` lies beyond `M`;
- every point of `G` is a main-term good point;
- every remainder-bad point belonging to `G` is covered by `B`;
- `card B < card G`.

Then some point of `G` is main-good and remainder-good simultaneously.

At that point, the reverse triangle inequality transfers coefficient `c` for
the main term and loss `loss` for the remainder to coefficient `c - loss`
for the full visible cluster.

Unsigned, positive, and negative signed versions are formalized.

## Intended analytic inputs

This interface separates two future estimates:

- a local mean-square or phase argument giving many main-cluster good points;
- a second-moment, Markov, or Carlson-density estimate giving fewer
  remainder-bad points.

It does not itself assert either analytic estimate, an unconditional Omega
theorem, or RH.
