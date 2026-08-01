# Normalized Cofinal Lower-Witness Obstruction

## Objective

Expose a narrow, auditable interface between the density/upper-transfer chain
and a future Sharp-owned oscillation witness without importing or changing any
Sharp module.

## Interface

`IsNormalizedCofinalPNTLowerWitness upper witness amplitude` records:

- witness indices are cofinal;
- amplitudes are eventually positive;
- each amplitude is eventually a lower bound for the real relative PNT error;
- the certified upper majorant divided by the amplitude tends to zero.

An eventual upper bound makes these four assertions inconsistent: the first
three force the normalized ratio to be eventually at least one, while the last
makes it eventually less than one.

The automatic corollary extracts the Stack135 best-of-direct-and-Carlson
majorant at the fixed strict choice `q = 2` and records this obstruction.

## Claim boundary

No lower witness is constructed here. In particular, this module proves no
Omega theorem, no zero propagation statement, and no form of RH. It identifies
the exact normalized comparison a separate oscillation theorem would need.
