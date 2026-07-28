# Actual Carlson window-count bidirectional PNT transfer

## Verified theorem chain

The module
`ZeroDensityLayerBudgetActualCarlsonWindowCountBidirectionalPNTTransfer`
combines three existing verified components:

1. fixed-rate decay of the relative natural-point `psi0` error;
2. a zero-supported finite Carlson selector extending a prescribed seed;
3. finite-window count anti-cancellation for the exact decomposition of the
   selected visible cluster into seed and extension.

The unsigned certificate assumes that, arbitrarily far out, a finite window
contains strictly more points where the seed has size at least
`c * targetAmplitude` than points where the extension has size at least
`loss * targetAmplitude`.  It then transfers the selected cluster witness to
the actual `psi0` error at scale

```text
((c - loss) / 2) * x ^ beta.
```

The signed certificate imposes the analogous count advantage separately for
positive and negative seed points, using the same extension-bad predicate.

## What this removes

The transfer no longer assumes

```text
finiteVisibleClusterCoefficientMass (S \ S0) < loss.
```

That global premise is too strong when a finite extension has unavoidable
coefficient mass.  Window synchronization only needs one seed-good point that
is not extension-bad.

## Remaining analytic input

The window-count advantages are hypotheses, not consequences presently proved
from zeta-zero density.  A future input may combine:

- a local mean-square lower bound producing many seed-good points;
- a second-moment or density estimate bounding extension-bad points.

This module does not formalize Guth-Maynard density estimates, prove an
unconditional Omega theorem, or imply RH.
