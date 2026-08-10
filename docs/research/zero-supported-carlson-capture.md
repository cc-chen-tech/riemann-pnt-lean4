# Zero-supported finite Carlson capture

## Purpose

The original finite-capture construction chooses a finite set of actual
Carlson positive-zero indices and maps them to complex zeros. Its existential
interface retained the mass estimate but forgot that every selected point is
a nontrivial zeta zero.

This module preserves that certificate through the exact construction chain:

1. finite image of actual Carlson positive zeros;
2. conjugation closure;
3. filtering to the boundary `Re rho = beta`.

The resulting theorem simultaneously provides:

- finite support;
- conjugation stability;
- nontrivial zeta-zero support;
- boundary support;
- the prescribed doubled outside-mass gap.

## Why the certificate matters

Boundary support alone says only `rho.re = beta`; it does not imply
`riemannZeta rho = 0`. The conjugation factor-two coefficient estimate uses
equality of analytic multiplicities at conjugate zeta zeros, so zero support
must be carried explicitly.

## Research boundary

This is an interface-preservation result. It does not add a new zero-density
estimate, localized oscillation theorem, zero-reproduction mechanism, RH, or
an unconditional Omega conclusion.
