# Variable-Boundary Monotone Absorption-or-Gap

## Objective

Discharge stack101's fixed-zero absorption-or-gap condition from the natural
properties of a finite-height maximum real-part schedule.

## Dichotomy

Fix one indexed zeta zero. Cofinality of `H` gives a natural sample `M` after
which the zero is always visible. The pointwise right-edge property then gives
`Re rho <= beta(m)` for `m >= M`.

If some `N >= M` satisfies `Re rho < beta(N)`, set

`delta = (beta(N) - Re rho) / 2`.

Monotonicity of `beta(m)` makes `Re rho <= beta(m) - delta` permanent for all
`m >= N`.

Otherwise strict inequality never occurs. The right-edge inequality must then
be equality at every `m >= M`, and the visible zero belongs to the complete
equal-real-part boundary package.

## Consequence

The absorption-or-gap hypothesis of stack101 becomes automatic, so the actual
visible Carlson kernel tail normalized by `m^(beta(m)-1)` tends to zero without
a global fixed right-edge cap.

## Claim boundary

This theorem assumes a concrete monotone boundary schedule and its pointwise
visible right-edge property. Construction of that schedule from the protected
finite-height maximum-real-part module remains separate. Low strips, contour
remainder, moving-package witnesses, simultaneous signs, and RH are not proved.
