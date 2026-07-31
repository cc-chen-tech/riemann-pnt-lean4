# Actual strict-margin grid full-PNT envelope

## Goal

Assemble the actual finite-zero estimate from Stack 128 and the actual
good-height contour certificate at the same rate candidate. Then apply the
Stack 127 finite-grid arithmetic to the real relative PNT error itself.

## Per-rate envelope

For `u = sqrt (log m)`, use:

- contour coefficient `26 C_contour u^4` at rate `k`;
- finite-zero coefficient `9 C_zero u^2` at rate `theta b / k`;
- a rate-independent residual consisting of the contour tail, the closed-log
  term, and the absolute closed real-axis term.

The per-rate majorant is exactly

`classicalStrictMarginRateFullBudgetEnvelope contour zero residual theta b k`.

## Transfer

At every fixed grid rate, the exact explicit-formula decomposition gives an
eventual bound for the real relative `psi0` error by the per-rate envelope.
The envelope-optimal grid rate from Stack 126 then gives the explicit closed
rate

`classicalAdmissibleBalancedRate (theta b) / q`.

## Claim boundary

This is a classical zero-free plus explicit-formula upper bound. It does not
assert continuity of the actual error, target-amplitude negligibility,
unconditional Omega, RH, or a VK-edge constant. Carlson dyadic refinements are
not inserted into this particular majorant.
