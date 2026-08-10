# Zero-supported coefficient-mass bidirectional PNT transfer

## Unified certificate

One selected finite cluster now supports both directions of the actual-PNT
chain:

- Carlson two-strip input gives fixed-rate natural-point convergence of the
  relative `psi0` error to zero;
- a seed visible-main witness plus
  `finiteCoefficientMass(S \ S0) < loss` gives an unnormalized
  `chebyshevPsi0Error` witness at scale
  `((c - loss) / 2) * x ^ beta`;
- every member of `S \ S0` is certified as a nontrivial zeta zero.

Unsigned and signed variants share the same selected cluster.

## Remaining hypotheses

The seed oscillation witness and the strict coefficient-mass budget remain
premises. In particular, the theorem does not claim that finite Carlson
capture automatically has small coefficient mass, and it does not assert an
unconditional Omega theorem or RH.
