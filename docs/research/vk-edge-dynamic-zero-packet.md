# Dynamic zeta-zero packet expansion

## Scope

This branch starts the dynamic packet dichotomy after the finite-height
remainder and Gaussian bucket data layers.

For a current dominant zero set `S`, dynamic height `T`, and unit absolute
ordinate bucket `n`, the new packet is

```text
zeroOrdinateUnitBucket n ∩ (nontrivialZerosFinset T \ S).
```

It therefore contains only actual nontrivial zeta zeros, retains analytic
multiplicity in every frozen coefficient, and is disjoint from `S`.

## Closed step

The theorem

```text
exists_absorbableDynamicComplementPacket_of_centeredFrozenGaussianL2_gt
```

starts from the Gaussian-weighted `L2` energy of the frozen exponential sum
formed from actual height-`T` complementary zeta zeros.  Each coefficient is
twisted by the phase at the logarithmic window center `a`; this is the frozen
model that can later be compared with the actual moving zero contribution on
that window.  The exact Fourier transform

```text
fourierKernel normalizedGaussian = exp (-m * frequency^2)
```

and the collision-safe Schur estimate bound that second moment by the positive
packet majorant.  A large frozen second moment therefore forces a bucket `n`
such that:

- the new packet is nonempty;
- it is disjoint from `S`;
- it is contained in `nontrivialZerosFinset T`;
- adjoining it strictly increases the cardinality of the dominant set;
- its squared frozen coefficient mass is larger than

```text
eta / (gaussianBucketSchurConstant * K.card).
```

This is a concrete one-step zeta extraction theorem, not an abstract packet
interface.

## Exact remaining analytic bridge

The remaining trigger gap is no longer Gaussian Fourier analysis.  It is the
comparison between the actual moving complement on a growing logarithmic
window and the frozen exponential sum at its center.  The next theorem must
bound their difference by an explicit real-part drift loss.  That bridge must
use the actual complement contribution and may not assume its smallness.

After that bridge, the dichotomy is:

```text
large moving-complement L2
  -> large Gaussian majorant after drift accounting
  -> absorb a new actual zeta packet

small moving-complement L2
  -> combine the existing dominant-cluster coercivity and true remainder
  -> localized oscillation
```

Carlson zero density is deliberately not implemented here.  It will consume
the strict-expansion and captured-mass certificates to bound the number or
total mass of expansion steps.

## Non-claims

This work does not prove:

- that the moving complement `L2` energy is small;
- termination of the packet expansion;
- a Carlson contradiction;
- fixed-window oscillation;
- RH.
