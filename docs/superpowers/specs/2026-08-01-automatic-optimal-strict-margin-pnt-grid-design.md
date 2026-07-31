# Automatic optimal strict-margin PNT grid

## Goal

Remove the remaining manual constants and finite-grid witness from the actual
strict-margin PNT envelope of Stack 129.

## Construction

For the proved classical zero-free constant `b` and any fixed
`0 < theta < 1`, set

`rate = classicalAdmissibleBalancedRate (theta * b)`.

Construct an `ActualPintzCarlsonGoodHeightRateGrid` whose only rate and base
rate are `rate`, using an arbitrary uniform analytic good-height selector.
This is not a discretization approximation: it is the exact constrained
optimizer of the strict-margin analytic profile, so Stack 129 applies with
`q = 1`.

## Automatic theorem

Obtain `b` and the finite-zero coefficient `C` directly from the proved
classical zeta zero-free finite-sum theorem. For every `theta` and every
uniform good-height selector, derive an eventual closed-form bound on the
actual relative `psi0` error at the automatically selected optimal height.

## Claim boundary

The theorem is an unconditional classical zero-free upper-bound transfer. It
does not claim an optimal numerical constant, VK sharpness, target-amplitude
negligibility, an Omega theorem, or RH. The strict factor `theta < 1` remains
necessary because the actual width is `b / log (T + 6)`.
