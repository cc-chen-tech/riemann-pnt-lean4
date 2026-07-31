# Actual Zero-Package Carlson Unnormalized Sign Alternative

## Objective

Expose the stack94 fixed-sign alternative at the mathematically natural
unnormalized scale for `chebyshevPsi0 x - x`.

## Transfer

Stack94 returns a positive-or-negative natural-point witness for
`relativeChebyshevPsi0Error` at coefficient
`(q * sqrt(energy) - loss) / 2` times `x^(beta - 1)`.

For either selected sign:

1. embed the natural-point witness into the real-variable signed interface;
2. restrict to positive sample points arbitrarily far out;
3. use `chebyshevPsi0Error x = x * relativeChebyshevPsi0Error x`;
4. use `x * x^(beta - 1) = x^beta`.

The finite extension, Carlson boundary budget, and fixed-rate relative PNT
convergence from stack94 are returned unchanged.

## Claim boundary

The result is conditional `Omega+ OR Omega-` at the exact net `x^beta` scale.
It is not simultaneous `Omega+-`, does not improve the energy coefficient,
does not discharge Carlson hypotheses, and does not imply RH.
