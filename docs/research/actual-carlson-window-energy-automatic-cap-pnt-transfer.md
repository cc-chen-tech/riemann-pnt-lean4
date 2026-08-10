# Actual Carlson window-energy transfer with an automatic main cap

## Purpose

The actual-PNT window-energy route previously consumed a
`HasFarWindowEnergySeparation` certificate.  Such a certificate includes a
pointwise bound for the normalized selected-cluster main term.

For a finite visible zeta-zero cluster whose real parts are at most `beta`,
that pointwise bound is automatic.  Its bound is the finite coefficient mass

```text
finiteVisibleClusterCoefficientMass E.
```

The new transfer therefore asks only for `HasFarWindowEnergyBudgets`: the
main-window square lower bound and extension-window square upper bound.

## Theorem chain

```text
finite visible coefficient mass
  -> eventual normalized pointwise main cap
window energy budgets
  -> window energy separation
existing actual-PNT energy transfer
  -> HasFarTargetAmplitudeWitness chebyshevPsi0Error scale
```

The canonical specialization preserves the scale

```text
((c - loss) / 2) * x ^ beta.
```

## Boundary

This module does not prove either window-energy estimate.  In particular, it
does not derive a discrete natural-point window estimate from the continuous
zero-package mean-square theorem.  It also makes no unconditional Omega or RH
claim.
