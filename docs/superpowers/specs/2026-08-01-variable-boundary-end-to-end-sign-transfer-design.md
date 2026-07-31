# Variable-Boundary End-to-End Sign Transfer Design

## Goal

Expose one theorem connecting the complete automatic moving analytic residual
to the existing moving-package sign-alternative transfer on the actual
unnormalized PNT error.

## Interface

Analytic inputs provide:

- polynomial selected-height control;
- the fixed low-strip margin;
- indexed visible right-edge and absorption-or-gap conditions;
- the real-ordinate strict gap;
- the actual contour remainder certificate.

Stack108 converts these into negligibility of the complete actual residual at
`m^(beta(m)-1)`. The only oscillatory input is a far natural-point witness for
the actual moving package main term at coefficient `c`. For any
`0 < loss < c`, stack100 then yields a fixed sign alternative for
`chebyshevPsi0(x)-x` at coefficient `c-loss` and scale `x^beta(x)`.

## Claim boundary

The result is `Omega+ OR Omega-`, not both signs. The moving main witness is an
explicit hypothesis owned by the independent anti-cancellation/Sharp work.
The theorem does not imply RH.
