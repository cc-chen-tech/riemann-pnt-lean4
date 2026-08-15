# Explicit third-order residue at zero

## Result

Define the analytic zero core

    h_x(s) = (-zeta'(s) / zeta(s)) * x^s.

For x > 0, the genuine third-order explicit-formula kernel has the local
Laurent expansion

    analytic remainder
      + (h_x''(0) / 2) * s^(-1)
      + h_x'(0) * s^(-2)
      + h_x(0) * s^(-3),

where the second derivative is represented by iteratedDeriv 2, and

    h_x(0) = -zeta'(0) / zeta(0).

Thus the simple residue at zero is not an opaque existential coefficient: it
is exactly the quadratic Taylor coefficient

    iteratedDeriv 2 h_x 0 / 2.

## Proof structure

The proof reuses the verified analyticity of the zeta logarithmic derivative
at zero, the nonvanishing identity zeta(0) = -1/2, and analyticity of the
constant-base complex power x^s. The third-order Taylor quotient then gives
an analytic remainder after division by s^3.

## Role in the unified route

The corrected negative-left-edge explicit formula currently retains
residue(0) in its finite residue sum. This local theorem supplies the
intrinsic coefficient that the next uniqueness adapter must identify with
that existential residue.

No Carlson tail estimate, oscillation theorem, or RH conclusion is claimed.
