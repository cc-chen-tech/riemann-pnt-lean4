# Dynamic zero packets: real-part drift bridge

This module connects the actual moving contribution of a finite collection of
zeta zeros to the centered frozen Gaussian packet energy used by the dynamic
packet extractor.

For every inspected packet zero in the real-part band

```text
beta - delta <= rho.re <= beta,
```

the pointwise moving-versus-frozen error is at most

```text
(1 - exp (-delta * (y - a))) * totalCoefficientMass.
```

Consequently, on the forward centered window `0 <= t <= L`,

```text
movingGaussianEnergy
  <= 2 * centeredFrozenGaussianEnergy
     + 2 * (1 - exp (-delta * L))^2 * totalCoefficientMass^2.
```

The center phase in the frozen energy is the exact phase at logarithmic center
`a`; it is locked by

```text
finiteExponentialSum (phaseTwist c omega a) omega t
  = finiteExponentialSum c omega (a + t).
```

The inspected moving contribution is now split exactly into

```text
full inspected packet = real-band packet + outside-band packet.
```

The corresponding Gaussian energy satisfies

```text
fullEnergy <= 2 * realBandEnergy + 2 * outsideBandEnergy.
```

This removes the unrealistic requirement that every zero in an entire
ordinate bucket lie in the real-part band. If the full energy remains large
after paying the explicit outside-band energy and the displayed drift budget,
the module forces one new nonempty packet of actual finite-height zeta zeros
inside the real band. The packet is disjoint from the current packet set,
strictly increases its cardinality, and every extracted zero carries the
band certificate.

## Boundary

This is a quantitative finite-height reduction, not an iteration theorem or a
zero-density contradiction. It still requires:

- a uniform upper bound for the explicit outside-band Gaussian energy;
- a separate estimate for zeros outside the inspected `K`-indexed packet
  range and for the contour remainder;
- a theorem transferring the real explicit-formula remainder into the moving
  packet energy hypothesis;
- an injective, non-overlapping iteration mechanism before Carlson zero
  density can be contradicted.

No RH, unconditional contradiction, or complete PNT oscillation theorem follows
from this module alone.
