# Strict-Margin Exponential-Core Rate Gap

## Objective

Quantify the precise square-root-log amplitude scale on which the actual
strict-margin contour and finite-zero terms are negligible.

## Theorem chain

1. Define `exp(-s * pntSqrtLog m)` as the comparison amplitude.
2. Split the actual full-PNT majorant exactly into its exponential core and the
   rate-independent residual.
3. For target rate `r` and every `s < r`, rewrite normalization of the core as
   degree-four and degree-two polynomials times `exp(-(r-s) * sqrt(log m))`.
4. Prove both terms tend to zero using the existing PNT asymptotic lemma.
5. State the full normalized theorem with the residual comparison as the only
   explicit remaining hypothesis.

## Barrier

This rate-gap theorem is deliberately restricted to square-root-log
exponential amplitudes. The repository already proves that the same fixed
Pintz contour factor cannot be negligible relative to a fixed power-scale
zero amplitude.

## Claim boundary

The core theorem is unconditional given the certified positive rate. Full
normalized decay still requires the displayed residual hypothesis. No power
scale oscillation, Omega theorem, or RH consequence is claimed.
