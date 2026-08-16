# Sharp moving-left-strip boundary

## Proved endpoint

For a genuine zeta zero `rho` with `rho.re > 2 / 3`, fix
`1 / 2 < sigma < rho.re`.  At each selected low detector height `Tlow`, define

```text
leftStripNontrivialZerosFinset sigma Tlow
```

to contain every actual nontrivial zeta zero with height at most `Tlow` and
real part at most `sigma`.

The theorem

```text
exists_eventually_leftStripLowHeightNormalizedComplementSecondMoment_gt
```

proves cofinally that deleting this growing package leaves at least one
quarter of the genuine empty-cluster Gaussian energy.  The retained constant
does not depend on the number of deleted zeros.

The analytic reason is quantitative: the deleted package contributes at most

```text
exp (-(rho.re - sigma) * log Y)
  * globalReciprocalZeroMultiplicity Tlow,
```

while the global reciprocal multiplicity is `O(log^2 Tlow)` and
`Tlow` lies at the separate low scale `Y^gammaLow`.  The fixed positive
real-part gap therefore dominates the growing zero package.

## Height separation

The theorem keeps the two detector scales distinct:

- `Tlow` lies in the unit interval at `Y^gammaLow`;
- the independent outer allowance is `Y^alpha`;
- the hypotheses retain `gammaLow < alpha`.

No substitution of `alpha` for `gammaLow` occurs in the energy estimate.

## What remains open

This theorem does not remove:

- the anchor zero or its conjugate;
- zeros on the same real-part layer as the anchor;
- zeros with real part greater than `sigma`;
- an arbitrary previously recorded finite set containing such zeros.

Consequently it does not provide the repeatable `S`-relative lower bound
required by `rightHigherExclusionSet`.  It does not imply a Carlson
contradiction and does not prove RH.  The remaining Sharp problem is to obtain
a new source of target-scale energy after the current anchor layer itself has
been deleted.
