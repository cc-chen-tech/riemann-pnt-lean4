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

A moving energy larger than the displayed drift budget therefore forces one
new nonempty packet of actual finite-height zeta zeros, disjoint from the
current packet set.

## Boundary

This is a conditional finite-height bridge, not an iteration theorem or a
zero-density contradiction. It still requires:

- a choice of packet indices whose zeros all satisfy the real-part band;
- a separate estimate for lower-real-part zeros and zeros outside the
  inspected packet range;
- a theorem transferring the real explicit-formula remainder into the moving
  packet energy hypothesis;
- an injective, non-overlapping iteration mechanism before Carlson zero
  density can be contradicted.

No RH, unconditional contradiction, or complete PNT oscillation theorem follows
from this module alone.
